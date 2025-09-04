module EquivRel

open FStar.Classical.Sugar
open FStar.Tactics
open FStar.Calc

open FStar.List.Tot

open STLC
open SyntacticTypes

//#set-options "--print_implicits --print_universes"
let test (f:(x:'a -> PURE Type0 ('w x))) (x:'a) : Type0  =
  FStar.Monotonic.Pure.elim_pure_wp_monotonicity_forall ();
  'w x (fun _ -> True) ==>  f x

let lem_pure_true_monotonic (w:pure_wp 'a) :
  Lemma (requires (w (fun _ -> True)))
        (ensures (forall p. (forall r. p r) ==> w p)) =
  FStar.Monotonic.Pure.elim_pure_wp_monotonicity_forall ();
  ()

let test' (f:(x:'a -> PURE int ('w x))) (x:'a) : int =
 // FStar.Monotonic.Pure.elim_pure_wp_monotonicity_forall ();
 // assert (forall (q p:pure_post int). (forall r. p r ==> q r) ==> ('w x p ==> 'w x q));
//  eliminate forall (q:pure_post int). (forall (p:pure_post int). (forall r. p r ==> q r) ==> ('w x p ==> 'w x q)) with (fun _ -> True);
//  assert (forall (p:pure_post int). (forall r. p r ==>  True) ==> ('w x p ==> 'w x (fun _ -> True)));
//  assert (forall (p:pure_post int). ('w x p ==> 'w x (fun _ -> True)));
  assume ('w x (fun _ -> True));
  f x

(** Cross Language Binary Logical Relation between F* and STLC expressions
     for __closed terms__. **)
let rec (∋) (t:typsr) (p:get_Type t * closed_exp) : Tot Type0 (decreases %[get_rel t;0]) =
  let fs_v = fst p in
  let e = snd p in
  match get_rel t with
  | RUnit -> fs_v == () /\ e == EUnit
  | RBool -> (fs_v == true /\ e == ETrue) \/ (fs_v == false /\ e == EFalse)
  | RArr #t1 #t2 #s1 #s2 r1 r2 -> begin
    let fs_f : s1 -> s2 = fs_v in
    match e with
    | ELam e' ->
      (forall (v:value) (fs_v:s1). (| t1, s1, r1 |) ∋ (fs_v, v) ==>
        (| t2, s2, r2 |) ⦂ (fs_f fs_v, subst_beta v e'))
    | _ -> False
  end
  | RRefined #t' #s' r' p -> begin
    assert (p fs_v);
    (| t', s', r' |) ∋ (fs_v, e)
  end
  | RArrWP #t1 #t2 #s1 #s2 r1 r2 wp -> begin
    let fs_f : (x:s1 -> PURE s2 (wp x)) = fs_v in
    FStar.Monotonic.Pure.elim_pure_wp_monotonicity_forall ();
    match e with
    | ELam e' ->
      (forall (v:value) fs_v.
        (| t1, s1, r1 |) ∋ (fs_v, v) /\ as_requires (wp fs_v) ==>  (** Interesting that we do not need to quantify over post-conditions because of monotonicity **)
         (| t2, s2, r2 |) ⦂ (fs_f fs_v, subst_beta v e'))
    | _ -> False
  end
and (⦂) (t:typsr) (p: get_Type t * closed_exp) : Tot Type0 (decreases %[get_rel t;1]) =
  let fs_e = fst p in
  let e = snd p in
  forall (e':closed_exp). steps e e' ==> irred e' ==> t ∋ (fs_e, e')

let lem_values_are_expressions t fs_e e : (** lemma used by Amal **)
  Lemma (requires t ∋ (fs_e, e))
        (ensures  t ⦂ (fs_e, e)) = admit ()

(** F* Evaluation Environment : variable -> value **)

(** We compile F* values, not F* expressions.
    When compiling F* lambdas, there is no way to match and get
    the body of the lambda.

    To avoid this limitation, we do closure conversion of F* lambdas:
    - be a lambda f:'a -> 'b
    - we wrap f to a function that takes as argument an F* evaluation environment
      that was extended to contain a value of type 'a
    - we take the value from the environment to open f:
        fun fs_s -> f (get_v fs_s 0)

    What is cool about this is to define compilation to STLC the environment is abstract.
 **)

val fs_env (g:env) : Type u#0
val fs_empty : fs_env empty
val get_v : #g:env -> fs_env g -> x:var{Some? (g x)} -> get_Type (Some?.v (g x))
val fs_extend : #g:env -> fs_s:fs_env g -> #t:typsr -> get_Type t -> fs_env (extend t g)
val fs_shrink : #t:typsr -> #g:env -> fs_env (extend t g) -> fs_env g

val lem_fs_extend #g (fs_s:fs_env g) #t (v:get_Type t) : Lemma (
  (forall (x:var). Some? (g x) ==>  get_v fs_s x == get_v (fs_extend fs_s v) (x+1)) /\
  get_v (fs_extend fs_s v) 0 == v)
  [SMTPat (fs_extend fs_s v)]

val lem_fs_shrink #g #t (fs_s:fs_env (extend t g)) : Lemma (
  (forall (x:var). Some? (g x) ==>  get_v fs_s (x+1) == get_v (fs_shrink fs_s) x))
  [SMTPat (fs_shrink fs_s)]

val shrink_extend_inverse #g (fs_s:fs_env g) #t (x:get_Type t) : Lemma (fs_shrink (fs_extend fs_s x) == fs_s)
  [SMTPat (fs_shrink (fs_extend fs_s x))]

let (∽) (#g:env) #b (s:gsub g b) (fs_s:fs_env g) : Type0 =
  forall (x:var). Some? (g x) ==>
    Some?.v (g x) ∋ (get_v fs_s x, s x)

type wp_g (g:env) (a:Type) =
  fs_env g -> pure_wp a

type fs_oexp (#g:env) (a:Type) (wp:wp_g g a) =
  fs_s:(fs_env g) -> PURE a (wp fs_s)
               (**  ^^^^ here probably we have the monad we compile.
                    This will give us the initial state/history over which to state the pre-condition**)

unfold
let helper_fapp wp (f:(x:'a -> PURE 'b (wp x))) (x:'a) : Pure 'b (as_requires (wp x)) (fun _ -> True) =
  FStar.Monotonic.Pure.elim_pure_wp_monotonicity_forall ();
  f x

let intro_pure_wp_monotonicity (#a:Type) (wp:pure_wp' a)
  : Lemma
      (requires FStar.Monotonic.Pure.is_monotonic wp)
      (ensures pure_wp_monotonic a wp)
    [SMTPat (pure_wp_monotonic a wp)]
  = FStar.Monotonic.Pure.intro_pure_wp_monotonicity wp

(** Cross Language Binary Logical Relation between F* and STLC expressions
     for __open terms__. **)
let equiv (#g:env) (t:typsr) (wp:wp_g g (get_Type t)) (fs_e:fs_oexp (get_Type t) wp) (e:exp) : Type0 =
  FStar.Monotonic.Pure.elim_pure_wp_monotonicity_forall ();
  fv_in_env g e /\
  forall b (s:gsub g b) (fs_s:fs_env g).
    s ∽ fs_s /\ as_requires (wp fs_s) ==>  t ⦂ (helper_fapp wp fs_e fs_s, gsubst s e)

let (≈) (#g:env) (#t:typsr) (#wp:wp_g g (get_Type t)) (fs_v:fs_oexp (get_Type t) wp) (e:exp) : Type0 =
  equiv #g t wp fs_v e

let pure_trivial a : pure_wp a = (fun p -> forall r. p r)

(** Equiv closed terms **)
let equiv_closed_terms (#t:typsr) (fs_e:get_Type t) (e:closed_exp) :
  Lemma (requires equiv #empty t (fun _ -> pure_trivial _) (fun _ -> fs_e) e)
        (ensures  t ⦂ (fs_e, e)) =
  eliminate forall b (s:gsub empty b) (fs_s:fs_env empty).
    s ∽ fs_s /\ as_requires (pure_trivial (get_Type t)) ==>  t ⦂ ((fun _ -> fs_e) fs_s, gsubst s e) with true gsub_empty fs_empty

(** Rules **)

let tunit : typsr =
  (| _, _, RUnit |)

let equiv_unit g
  : Lemma ((fun (_:fs_env g) -> ()) `equiv tunit (fun _ -> pure_trivial _)` EUnit)
  =
  introduce forall b (s:gsub g b) fs_s. s ∽ fs_s /\ as_requires (pure_trivial unit) ==>  tunit ⦂ ((), EUnit) with begin
    introduce _ ==> _ with _. begin
      assert (tunit ∋ ((), EUnit));
      lem_values_are_expressions tunit () EUnit
    end
  end

let tbool : typsr =
  (| _, _, RBool |)

let mk_pre_lam #g (#t1 #t2:typsr) (wp:get_Type t1 -> pure_wp (get_Type t2)) (wpG:wp_g g (get_Type (mk_arrow_wp t1 t2 wp))) : wp_g (extend t1 g) (get_Type t2) =
  fun fs_s ->
    let new_wp : pure_wp' (get_Type t2) = fun p -> wpG (fs_shrink fs_s) (fun _ -> wp (get_v fs_s 0) p) in
    assume (FStar.Monotonic.Pure.is_monotonic new_wp);
    new_wp


let equiv_lam
  g
  (t1:typsr) (t2:typsr)
  (body:exp)
  (wp:get_Type t1 -> pure_wp (get_Type t2))
  (wpG: wp_g g (get_Type (mk_arrow_wp t1 t2 wp)))
  (f:fs_oexp (get_Type (mk_arrow_wp t1 t2 wp)) wpG)
  : Lemma
    (requires (equiv #(extend t1 g) t2 (mk_pre_lam wp wpG)
                   (fun fs_s -> FStar.Monotonic.Pure.elim_pure_wp_monotonicity_forall (); f (fs_shrink fs_s) (get_v fs_s 0))
                   body))
    (ensures f ≈ (ELam body))
  = admit ()

(**
  FStar.Monotonic.Pure.elim_pure_wp_monotonicity_forall ();
  lem_fv_in_env_lam g t1 body;
  introduce forall b (s:gsub g b) fs_s. s ∽ fs_s /\ pre fs_s ==> mk_arrow_wp t1 t2 wp ⦂ (f fs_s, gsubst s (ELam body)) with begin
    introduce _ ==> _ with _. begin
      assert (gsubst s (ELam body) == ELam (subst (sub_elam s) body));
      introduce forall (v:value) fs_v. t1 ∋ (fs_v, v) /\ as_requires (wp fs_v) ==>  t2 ⦂ (f fs_s fs_v, subst_beta v (subst (sub_elam s) body)) with begin
        introduce _ ==> _ with _. begin
          let s' = gsub_extend s t1 v in
          let fs_s' = fs_extend fs_s fs_v in
          let g' = extend t1 g in
          let pre' : gpre g' = mk_pre_lam pre wp in
          let f' : fs_oexp pre' (get_Type t2) = fun fs_s -> FStar.Monotonic.Pure.elim_pure_wp_monotonicity_forall (); f (fs_shrink #t1 fs_s) (get_v fs_s 0) in
          eliminate equiv #g' t2 pre' f' body /\ True
          returns t2 ⦂ (f' fs_s', (gsubst s' body)) with _ _. begin
            eliminate forall b (s':gsub g' b) fs_s'. s' ∽ fs_s' /\ pre' fs_s' ==>  t2 ⦂ (f' fs_s', gsubst s' body)
              with false s' fs_s';
            assert (s ∽ fs_s);
            assert (gsub_extend s t1 v ∽ fs_extend fs_s fs_v)
          end;
          let fs_fres = f fs_s fs_v in (** this helps F* **)
          eliminate t2 ⦂ (f' fs_s', gsubst s' body) /\ True
          returns t2 ⦂ (fs_fres, gsubst s' body) with _ _. begin
            assert (get_v (fs_extend fs_s fs_v) 0 == fs_v);
            assert (fs_fres == f' fs_s')
          end;
          lem_substitution s t1 v body;
          assert (t2 ⦂ (fs_fres, subst_beta v (subst (sub_elam s) body)))
        end
      end;
      assert (mk_arrow_wp t1 t2 wp ∋ (f fs_s, gsubst s (ELam body)));
      lem_values_are_expressions (mk_arrow_wp t1 t2 wp) (f fs_s) (gsubst s (ELam body));
      assert (mk_arrow_wp t1 t2 wp ⦂ (f fs_s, gsubst s (ELam body)))
    end
  end

let equiv_true g pre
  : Lemma ((fun (_:fs_env g) -> true) `equiv tbool pre` ETrue)
  = assert ((fun (_:fs_env g) -> true) `equiv tbool pre` ETrue) by (explode ())

let equiv_false g pre
  : Lemma ((fun (_:fs_env g) -> false) `equiv tbool pre` EFalse)
  = assert ((fun (_:fs_env g) -> false) `equiv tbool pre` EFalse) by (explode ())

let equiv_var g (x:var{Some? (g x)}) pre
  : Lemma ((fun (fs_s:fs_env g) -> get_v fs_s x) `equiv (Some?.v (g x)) pre` EVar x)
  = assert ((fun (fs_s:fs_env g) -> get_v fs_s x) `equiv (Some?.v (g x)) pre` EVar x) by (explode ())


let mk_pre_app #g (pre:gpre g) (#t1 #t2:Type) (wp:t1 -> pure_wp t2) (fs_e:fs_oexp pre t1) : gpre g =
  fun fs_s -> pre fs_s /\ as_requires (wp (fs_e fs_s))

let get_rel' = get_rel

let lem_super_lemma (t2:typsr) :
  Lemma (t2._2 == get_Type t2)
         by (norm [delta_only [`%get_Type];iota])= ()

let eliminate_value_arrow (t1 t2:typsr) wp fs_e1 e11 fs_e2 (e2:value) :
  Lemma
    (requires (is_closed (ELam e11) /\ as_requires (wp fs_e2) /\ is_closed e2 /\
               mk_arrow_wp t1 t2 wp ∋ (fs_e1, ELam e11) /\ t1 ∋ (fs_e2, e2)))
    (ensures  (t2 ⦂ (helper_fapp wp fs_e1 fs_e2, subst_beta e2 e11))) =
    calc (<==>) {
      mk_arrow_wp t1 t2 wp ∋ (fs_e1, ELam e11);
      <==> { _ by (
               norm [delta_once [`%mk_arrow_wp; `%op_u8715;`%get_rel;`%Mkdtuple3?._3;`%snd;`%Mktuple2?._2;`%fst;`%Mktuple2?._1];zeta;iota];
               norm [delta_only [`%get_rel';`%helper_fapp];iota]
          )}
      (forall (v:value) (fs_v:t1._2). (| t1._1, t1._2, get_rel' t1 |) ∋ (fs_v, v) /\ as_requires #t2._2 (wp fs_v)  ==>
                 (| t2._1, t2._2, get_rel' t2 |) ⦂ (helper_fapp #t1._2 #t2._2 wp fs_e1 fs_v, subst_beta v e11));
      <==> { _ by (norm [delta_only [`%get_rel'];iota]) }
      (forall (v:value) fs_v. t1 ∋ (fs_v, v) /\ as_requires #t2._2 (wp fs_v)  ==>
                 (| t2._1, t2._2, get_rel t2 |) ⦂ (helper_fapp #t1._2 #t2._2 wp fs_e1 fs_v, subst_beta v e11));
      <==> { _ by (l_to_r [`lem_super_lemma]) }
      (forall (v:value) fs_v. t1 ∋ (fs_v, v) /\ as_requires (wp fs_v)  ==>
                 (| t2._1, t2._2, get_rel t2 |) ⦂ (helper_fapp wp fs_e1 fs_v, subst_beta v e11));
    }

let equiv_app
  g (pre:gpre g)
  (t1:typsr) (t2:typsr) (wp:get_Type t1 -> pure_wp (get_Type t2))
  (e1:exp)
  (fs_e1:fs_oexp pre (get_Type (mk_arrow_wp t1 t2 wp)))
  (e2:exp)
  (fs_e2:fs_oexp pre (get_Type t1))
  (l:squash (forall fs_s. pre fs_s ==>  as_requires (wp (fs_e2 fs_s))))
  : Lemma
    (requires fs_e1 `equiv _ pre` e1 /\ fs_e2 `equiv _ pre` e2)
    (ensures
      equiv #g t2 pre //(mk_pre_app pre wp fs_e2)
        (fun fs_s -> FStar.Monotonic.Pure.elim_pure_wp_monotonicity_forall (); (fs_e1 fs_s) (fs_e2 fs_s))
        (EApp e1 e2)) =
  FStar.Monotonic.Pure.elim_pure_wp_monotonicity_forall ();
  lem_fv_in_env_app g e1 e2;
 // let pre' : gpre g = (mk_pre_app pre wp fs_e2) in
  let fs_e : fs_oexp pre (get_Type t2) = fun fs_s -> (fs_e1 fs_s) (fs_e2 fs_s) in
  introduce forall b (s:gsub g b) fs_s. s ∽ fs_s /\ pre fs_s ==> t2 ⦂ (fs_e fs_s, gsubst s (EApp e1 e2)) with begin
    introduce s ∽ fs_s /\ pre fs_s ==>  _ with _. begin
      let fs_e1' : (x:get_Type t1 -> PURE (get_Type t2) (wp x)) = fs_e1 fs_s in
      let fs_e2' = fs_e2 fs_s in
      assert (as_requires (wp fs_e2'));
      introduce forall (e':closed_exp). steps (gsubst s (EApp e1 e2)) e' /\ irred e' ==> t2 ∋ (fs_e fs_s, e') with begin
        introduce steps (gsubst s (EApp e1 e2)) e' /\ irred e' ==> _ with h. begin
          let steps_e_e' : squash (steps (EApp (gsubst s e1) (gsubst s e2)) e') = () in
          FStar.Squash.map_squash #_ #(squash (t2 ∋ (fs_e fs_s, e'))) steps_e_e' (fun steps_e_e' ->
            let (e11, e2') = destruct_steps_eapp (gsubst s e1) (gsubst s e2) e' steps_e_e' in
            eliminate mk_arrow_wp t1 t2 wp ∋ (fs_e1', ELam e11) /\ t1 ∋ (fs_e2', e2')
            returns t2 ⦂ (helper_fapp wp fs_e1' fs_e2', subst_beta e2' e11) with h1 _. begin
              eliminate_value_arrow t1 t2 wp fs_e1' e11 fs_e2' e2'
            end;
            assert (t2 ⦂ (fs_e fs_s, subst_beta e2' e11));
            assert (t2 ∋ (fs_e fs_s, e'))
          )
        end
      end
    end
  end

(**
let equiv_if g (t:typsr) (e1:exp) (e2:exp) (e3:exp) (fs_e1:fs_env g -> get_Type tbool) (fs_e2:fs_env g -> get_Type t) (fs_e3:fs_env g -> get_Type t) : Lemma
  (requires fs_e1 ≈ e1 /\ fs_e2 ≈ e2 /\ fs_e3 ≈ e3)
  (ensures (fun fs_s -> if fs_e1 fs_s then fs_e2 fs_s else fs_e3 fs_s) ≈ EIf e1 e2 e3) =
  lem_fv_in_env_if g e1 e2 e3;
  introduce forall b (s:gsub g b) fs_s. s ∽ fs_s ==> t ⦂ ((if fs_e1 fs_s then fs_e2 fs_s else fs_e3 fs_s), gsubst s (EIf e1 e2 e3)) with begin
    let fs_e1' = fs_e1 fs_s in
    let fs_e2' = fs_e2 fs_s in
    let fs_e3' = fs_e3 fs_s in
    let fs_e = if fs_e1' then fs_e2' else fs_e3' in
    introduce s ∽ fs_s ==>  t ⦂ (fs_e, gsubst s (EIf e1 e2 e3)) with _. begin
      introduce forall (e':closed_exp). steps (gsubst s (EIf e1 e2 e3)) e' /\ irred e' ==> t ∋ (fs_e, e') with begin
        introduce _ ==> t ∋ (fs_e, e') with h. begin
          let steps_e_e' : squash (steps (EIf (gsubst s e1) (gsubst s e2) (gsubst s e3)) e') = () in
          FStar.Squash.map_squash #_ #(squash (t ∋ (fs_e, e'))) steps_e_e' (fun steps_e_e' ->
            let e1' = destruct_steps_eif (gsubst s e1) (gsubst s e2) (gsubst s e3) e' steps_e_e' in
            assert (tbool ∋ (fs_e1', e1'));
            assert (t ∋ (fs_e, e'))
          )
        end
      end
    end
  end
**)

**)
