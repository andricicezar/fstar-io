module LogRelTargetSource

open FStar.Classical.Sugar
open FStar.List.Tot

open STLC
open QTyp
open IO
open Trace

(** Cross Language Binary Logical Relation between F* and STLC expressions
     for __closed terms__. **)
let rec (∈) (t:qType) (p:(history * fs_val t * closed_exp)) : Tot Type0 (decreases %[get_rel t;0]) =
  let (h, fs_v, e) = p in
  match get_rel t with // way to "match" on F* types
  | QUnit -> fs_v == () /\ e == EUnit
  | QBool -> (fs_v == true /\ e == ETrue) \/ (fs_v == false /\ e == EFalse)
  | QFileDescriptor ->  e == EFileDescr fs_v
  | QString -> (match e with | EString s -> fs_v == s | _ -> False)
  | QArr #t1 #t2 qt1 qt2 -> begin
    let fs_f : t1 -> t2 = fs_v in
    match e with
    | ELam e' ->
      (forall (v:value) (fs_v:t1) (lt_v:local_trace h). pack qt1 ∈ (h++lt_v, fs_v, v) ==>
        pack qt2 ⊆ (h++lt_v, fs_f fs_v, subst_beta v e'))
    | _ -> False
  end
  | QArrIO #t1 #t2 qt1 qt2 -> begin
    let fs_f : t1 -> io t2 = fs_v in
    match e with
    | ELam e' -> // instead quantify over h'' - extensions of the history:
      (forall (v:value) (fs_v:t1) (lt_v:local_trace h). pack qt1 ∈ (h++lt_v, fs_v, v) ==>
        pack qt2 ⫃ (h++lt_v, fs_f fs_v, subst_beta v e'))
    | _ -> False
  end
  | QPair #t1 #t2 qt1 qt2 -> begin
    match e with
    | EPair e1 e2 -> (** e1 and e2 are values. no need to quantify over lts **)
        pack qt1 ∈ (h, fst #t1 #t2 fs_v, e1) /\ pack qt2 ∈ (h, snd #t1 #t2 fs_v, e2)
    | _ -> False
  end
  | QSum #t1 #t2 qt1 qt2 -> begin
    let fs_v : either t1 t2 = fs_v in
    match fs_v, e with
    | Inl fs_v', EInl e' -> pack qt1 ∈ (h, fs_v', e')
    | Inr fs_v', EInr e' -> pack qt2 ∈ (h, fs_v', e')
    | _ -> False
  end
                           (** vvvvvvvvvv defined over values **)
and (⊆) (t:qType) (p:history * fs_val t * closed_exp) : Tot Type0 (decreases %[get_rel t;1]) =
  let (h, fs_e, e) = p in
  exists (e':closed_exp). e_beh e e' h [] /\ t ∈ (h, fs_e, e')
                           (** vvvvvvvvvv defined over producers **)
and (⫃) (t:qType) (p:history * fs_prod t * closed_exp) : Tot Type0 (decreases %[get_rel t;1]) =
  let (h, fs_e, e) = p in
  forall lt.
    (forall (fs_r:get_Type t). fs_beh fs_e h lt fs_r ==>
      exists e'. t ∈ (h++lt, fs_r, e') /\ e_beh e e' h lt)

let valid_member_of (#t:qType) (fs_e:fs_val t) (e:value) : Type0 =
  forall (h:history). t ∈ (h, fs_e, e)

let valid_subset_val (#t:qType) (fs_e:fs_val t) (e:value) : Type0 =
  forall (h:history). t ⊆ (h, fs_e, e)

let valid_subset_prod (#t:qType) (fs_e:fs_prod t) (e:closed_exp) : Type0 =
  forall (h:history). t ⫃ (h, fs_e, e)

let rec lem_values_are_values t h fs_e (e:closed_exp) :
  Lemma (requires t ∈ (h, fs_e, e))
        (ensures is_value e)
        (decreases e) =
  match get_rel t with
  | QUnit -> ()
  | QBool -> ()
  | QFileDescriptor -> ()
  | QString -> ()
  | QArr _ _ -> ()
  | QArrIO _ _ -> ()
  | QPair #t1 #t2 qt1 qt2 ->
    let EPair e1 e2 = e in
    lem_values_are_values (pack qt1) h (fst #t1 #t2 fs_e) e1;
    lem_values_are_values (pack qt2) h (snd #t1 #t2 fs_e) e2
  | QSum #t1 #t2 qt1 qt2 ->
    match fs_e, e with
    | Inl fs_e', EInl e' -> lem_values_are_values (pack qt1) h fs_e' e'
    | Inr fs_e', EInr e' -> lem_values_are_values (pack qt2) h fs_e' e'

let steps_val_id (e:value) (e':closed_exp) (h:history)
  : Lemma (requires squash (steps e e' h []))
          (ensures e == e') =
   lem_value_is_irred e;
   (* Return the proof of equality *)
   let sq_eq : squash (e == e') = 
     FStar.Squash.bind_squash #(steps e e' h []) #(squash (e == e')) (FStar.Squash.get_proof (steps e e' h [])) (fun (st:steps e e' h []) ->
       lem_irred_implies_srefl_steps st;
       (* Now we know e == e' here *)
       FStar.Squash.get_proof (e == e')
     )
   in
   ()

let lem_values_valid_subset_val_valid_member_of t (fs_e:fs_val t) (e:value) :
  Lemma (requires valid_subset_val fs_e e)
        (ensures  valid_member_of fs_e e) =
  introduce forall h. t ∈ (h, fs_e, e) with begin
    assert (t ⊆ (h, fs_e, e));
    let p (e':closed_exp) = e_beh e e' h [] /\ t ∈ (h, fs_e, e') in
    assert_norm (t ⊆ (h, fs_e, e) == (exists e'. p e'));
    
    let aux (e':closed_exp) : Lemma
      (requires p e')
      (ensures t ∈ (h, fs_e, e)) =
        assert_norm (e_beh e e' h [] == (steps e e' h [] /\ indexed_irred e' (h++[])));
        steps_val_id e e' h;
        assert (e == e');
        assert (t ∈ (h, fs_e, e))
    in
    eliminate exists e'. p e'
    returns t ∈ (h, fs_e, e)
    with _. aux e'
  end


let lem_values_are_expressions t h fs_e e : (** lemma used by Amal **)
  Lemma (requires t ∈ (h, fs_e, e))
        (ensures  t ⊆ (h, fs_e, e)) =
  lem_values_are_values t h fs_e e;
  lem_value_is_irred e;
  assert (e_beh e e h [])

let lem_values_are_producers t h fs_e e : (** lemma used by Amal **)
  Lemma (requires t ∈ (h, fs_e, e))
        (ensures  t ⫃ (h, io_return fs_e, e)) =
  lem_values_are_values t h fs_e e;
  lem_value_is_irred e;
  introduce forall lt (fs_r:get_Type t). fs_beh (io_return fs_e) h lt fs_r ==>
    (exists e'. t ∈ (h++lt, fs_r, e') /\ e_beh e e' h lt) with begin
    introduce fs_beh (io_return fs_e) h lt fs_r ==>
      (exists e'. t ∈ (h++lt, fs_r, e') /\ e_beh e e' h lt) with fs_beh_k. begin
       theta_monad_morphism_ret fs_e;
       (* Using intermediate assertions to guide the solver *)
       assert (theta (io_return fs_e) == hist_return fs_e); 
       
       let p : hist_post h (get_Type t) = fun lt' r' -> lt' == [] /\ r' == fs_e in
       assert (hist_return fs_e h p); (* definition of hist_return *)
       assert (theta (io_return fs_e) h p); (* rewrite *)
       assert (thetaP (io_return fs_e) h lt fs_r); (* hypothesis fs_beh_k *)
       
       (* Expand definition of thetaP / wp2p *)
       (* thetaP m h lt r <==> forall p. theta m h p ==> p lt r *)
       (* Therefore theta (io_return fs_e) h p ==> p lt fs_r *)
       
       assert (p lt fs_r);
       
       assert (lt == []);
       assert (fs_r == fs_e);

       lem_steps_refl e h;
       assert (e_beh e e h []);
       assert (t ∈ (h++lt, fs_r, e))
    end
  end

let lem_forall_values_are_values t h fs_e :
  Lemma (forall (e:closed_exp). t ∈ (h, fs_e, e) ==> is_value e) =
  introduce forall e. t ∈ (h, fs_e, e) ==> is_value e with begin
    introduce _ ==> _ with _. begin
      lem_values_are_values t h fs_e e
    end
  end

let lem_forall_values_are_values_prod t h :
  Lemma (forall (e:closed_exp) (lt:local_trace h) (fs_r:get_Type t). t ∈ (h++lt, fs_r, e) ==> is_value e) =
  introduce forall e lt fs_r. t ∈ (h++lt, fs_r, e) ==> is_value e with begin
    introduce _ ==> _ with _. begin
      lem_values_are_values t (h++lt) fs_r e
    end
  end

let (≍) (#g:typ_env) #b (h:history) (fsG:eval_env g) (s:gsub g b) : Type0 =
  forall (x:var). Some? (g x) ==>
    Some?.v (g x) ∈ (h, index fsG x, s x)
  (**  TODO      ^^^ not like in Amal's work. she uses an exp relation - but this is what she meant, because index fsG x is necessarily a value **)

(** Cross Language Binary Logical Relation between F* and STLC expressions
     for __open terms__. **)
let subset_oval (#g:typ_env) (t:qType) (fs_e:fs_oval g t) (e:exp) : Type0 =
  fv_in_env g e /\
  forall b (s:gsub g b) (fsG:eval_env g) (h:history).
    fsG `(≍) h` s ==> t ⊆ (h, fs_e fsG, gsubst s e)

let (⊏) (#g:typ_env) (#t:qType) (fs_v:fs_oval g t) (e:exp) : Type0 =
  subset_oval #g t fs_v e

let subset_oprod (#g:typ_env) (t:qType) (fs_e:fs_oprod g t) (e:exp) : Type0 =
  fv_in_env g e /\
  forall b (s:gsub g b) (fsG:eval_env g) (h:history).
    fsG `(≍) h` s ==> t ⫃ (h, fs_e fsG, gsubst s e)

let (⊑) (#g:typ_env) (#t:qType) (fs_v:fs_oprod g t) (e:exp) : Type0 =
  subset_oprod #g t fs_v e

let lem_value_subset_valid_member_of t (fs_e:fs_oval empty t) (e:value) :
  Lemma (requires fs_e ⊏ e)
        (ensures  valid_member_of #t (fs_e empty_eval) e) =
  introduce forall h. t ∈ (h, fs_e empty_eval, e) with begin
    eliminate forall b (s:gsub empty b) (fsG:eval_env empty) (h:history).
      fsG `(≍) h` s ==> t ⊆ (h, fs_e empty_eval, gsubst s e) with false gsub_empty empty_eval h;
    assert (t ⊆ (h, fs_e empty_eval, e));
    lem_values_valid_subset_val_valid_member_of t (fs_e empty_eval) e;
    assert (t ∈ (h, fs_e empty_eval, e))
  end

let rec val_type_closed_under_history_extension (t:qType) (h:history) (fs_v:fs_val t) (e:closed_exp) :
  Lemma (requires t ∈ (h, fs_v, e))
        (ensures forall lt. t ∈ (h++lt, fs_v, e))
        (decreases %[get_rel t;0]) =
  introduce forall lt. t ∈ (h++lt, fs_v, e) with begin
  match get_rel t with
  | QUnit -> ()
  | QBool -> ()
  | QFileDescriptor -> ()
  | QString -> ()
  | QArr #t1 #t2 qt1 qt2 -> begin
    let fs_f : t1 -> t2 = fs_v in
    let ELam e' = e in
    introduce forall (v:value) (fs_v':t1) (lt_v':local_trace (h++lt)). pack qt1 ∈ ((h++lt)++lt_v', fs_v', v) ==> pack qt2 ⊆ ((h++lt)++lt_v', fs_f fs_v', subst_beta v e') with begin
      introduce pack qt1 ∈ ((h++lt)++lt_v', fs_v', v) ==> _ with _. begin
        eliminate forall (v:value) (fs_v:t1) (lt_v:local_trace h). pack qt1 ∈ (h++lt_v, fs_v, v) ==> pack qt2 ⊆ (h++lt_v, fs_f fs_v, subst_beta v e') with v fs_v' (lt @ lt_v');
        trans_history h lt lt_v'
      end
    end
    end
  | QArrIO #t1 #t2 qt1 qt2 -> begin
    let fs_f : t1 -> io t2 = fs_v in
    let ELam e' = e in
    introduce forall (v:value) (fs_v':t1) (lt_v':local_trace (h++lt)). pack qt1 ∈ ((h++lt)++lt_v', fs_v', v) ==> pack qt2 ⫃ ((h++lt)++lt_v', fs_f fs_v', subst_beta v e') with begin
      introduce pack qt1 ∈ ((h++lt)++lt_v', fs_v', v) ==> _ with _. begin
        eliminate forall (v:value) (fs_v:t1) (lt_v:local_trace h). pack qt1 ∈ (h++lt_v, fs_v, v) ==> pack qt2 ⫃ (h++lt_v, fs_f fs_v, subst_beta v e') with v fs_v' (lt @ lt_v');
        trans_history h lt lt_v'
      end
    end
    end
  | QPair #t1 #t2 qt1 qt2 -> begin
    let EPair e1 e2 = e in
    val_type_closed_under_history_extension (pack qt1) h (fst #t1 #t2 fs_v) e1;
    val_type_closed_under_history_extension (pack qt2) h (snd #t1 #t2 fs_v) e2
    end
  | QSum #t1 #t2 qt1 qt2 -> begin
    let fs_v : either t1 t2 = fs_v in
    match fs_v, e with
    | Inl fs_v', EInl e' -> val_type_closed_under_history_extension (pack qt1) h fs_v' e'
    | Inr fs_v', EInr e' -> val_type_closed_under_history_extension (pack qt2) h fs_v' e'
    | _ -> false_elim ()
    end
  end

let lem_shift_type_value_environments (#g:typ_env) #b (h:history) (fsG:eval_env g) (s:gsub g b) :
  Lemma (forall (lt:local_trace h). fsG `(≍) h` s ==> fsG `(≍) (h++lt)` s) =
  introduce forall (lt:local_trace h). fsG `(≍) h` s ==> fsG `(≍) (h++lt)` s with begin
    introduce _ ==> _ with _. begin
      introduce forall (x:var). Some? (g x) ==> Some?.v (g x) ∈ (h++lt, index fsG x, s x) with begin
        introduce _ ==> _ with _. begin
          val_type_closed_under_history_extension (Some?.v (g x)) h (index fsG x) (s x)
        end
      end
    end
  end

let safety_prod (#t:qType) (fs_e:fs_prod t) (e:closed_exp) : Lemma
  (requires (valid_subset_prod fs_e e))
  (ensures safe e) =
  introduce forall (e':closed_exp) (h:history) (lt:local_trace h).
    steps e e' h lt ==> is_value e' \/ indexed_can_step e' (h++lt) with begin
    introduce steps e e' h lt ==> is_value e' \/ indexed_can_step e' (h++lt) with _. begin
      introduce indexed_irred e' (h++lt) ==> is_value e' with _. begin
        eliminate forall b (s:gsub empty b) (fsG:eval_env empty) (h:history).
          fsG `(≍) h` s ==> t ⫃ (h, fs_e, gsubst s e)
        with  true gsub_empty empty_eval h;
        assert (t ⫃ (h, fs_e, e));
        admit ()
  (**
        eliminate exists (fs_r:get_Type t). t ∈ (h++lt, fs_r, e') /\ fs_beh fs_e h lt fs_r
        returns is_value e' with _. begin
          assert (t ∈ (h++lt, fs_r, e'));
          lem_values_are_values t (h++lt) fs_r e';
          assert (is_value e')
        end **)
      end
    end
  end

open FStar.Tactics.V1

let unfold_member_of_arrow (t1 t2:qType) (h:history) (fs_e1:fs_val (t1 ^-> t2)) (e11:exp)
  : Lemma
    (requires (is_closed (ELam e11)) /\ ((t1 ^-> t2) ∈ (h, fs_e1, ELam e11)))
    (ensures (forall (v:value) (fs_v:fs_val t1) (lt_v:local_trace h). t1 ∈ (h++lt_v, fs_v, v) ==> t2 ⊆ (h++lt_v, fs_e1 fs_v, subst_beta v e11)))
  by (explode ();
    bump_nth 4;
    let x = nth_binder (-2) in
    let x', x'' = destruct_and x in
    clear x;
    let (x'0, x'1) = destruct_and x' in
    clear x';
    binder_retype x'1;
      norm [delta_once [`%op_u8712;`%(^->);`%get_rel; `%Mkdtuple2?._2;`%Mkdtuple2?._1]; zeta; delta; iota];
      l_to_r [`lem_pack_get_rel];
    trefl ();
    let x''' = instantiate x'' (fresh_uvar None) in
    clear x'';
    mapply x''';
    clear x''')
    = ()

let unfold_member_of_io_arrow (t1 t2:qType) (fs_e1:fs_val (t1 ^->!@ t2)) (e11:exp) (h:history)
  : Lemma (requires (is_closed (ELam e11)) /\ ((t1 ^->!@ t2) ∈ (h, fs_e1, ELam e11)))
          (ensures (forall (v:value) (fs_v:fs_val t1) (lt_v:local_trace h). t1 ∈ (h++lt_v, fs_v, v) ==> t2 ⫃ (h++lt_v, fs_e1 fs_v, subst_beta v e11)))
  by (explode ();
    bump_nth 4;
    let x = nth_binder (-2) in
    let x', x'' = destruct_and x in
    clear x;
    let (x'0, x'1) = destruct_and x' in
    clear x';
    binder_retype x'1;
      norm [delta_once [`%op_u8712;`%(^->!@);`%get_rel; `%Mkdtuple2?._2;`%Mkdtuple2?._1]; zeta; delta; iota];
      l_to_r [`lem_pack_get_rel];
    trefl ();
    let x''' = instantiate x'' (fresh_uvar None) in
    clear x'';
    mapply x''')
  = ()
