module RHC

open FStar.Tactics
open FStar.Tactics.Typeclasses

open STLC
open TypRel
open ExpRel
open Compiler

let my_rel_bool (fs_e:bool) (e:exp) : Type0 =
  (e == ETrue /\ fs_e == true) \/
  (e == EFalse /\ fs_e == false)

let lem_rel_beh' (fs_e: bool) (e:closed_exp) :
  Lemma
    (requires tbool ⦂ (fs_e, e))
    (**     vvv To have an existential here one needs normalization **)
    (ensures forall (e':closed_exp). steps e e' /\ irred e' ==>  my_rel_bool fs_e e')
= ()

assume val lem_rel_beh_arr (fs_e: bool -> bool) (e:closed_exp) :
  Lemma
    (requires (mk_arrow tbool tbool) ⦂ (fs_e, e)) (** here it is tbool because whole programs return booleans **)
    (ensures (forall fs_v (v:value). my_rel_bool fs_v v ==>
      (forall (e':closed_exp). steps (EApp e v) e' /\ irred e' ==>
        my_rel_bool (fs_e fs_v) e')))

noeq type intS = {
  ct : Type; // type of context 
  comp_ct : compile_typ ct; // compiled type of context, F* will crash if ct is not a type for which the compile_typ class has an instance
}

(* CA: this definition of progS is very comical! I have the compiled program inside the guarantee that it can be compiled :D **)
// program parameterized by the type of the context
// program is dependent pair type with:
  // map from the type of context to bool (which represents output of the source program) 
  // (proof of) compiled closed expression - where we pass in the type of ps (#_), the (proof of the) type of the compiled closed expression (#(compile_typ_arrow ...)), and ps
type progS (i:intS) = ps:(i.ct -> bool) & compile_closed #_ #(compile_typ_arrow _ bool #i.comp_ct) ps
type ctxS (i:intS) = i.ct
type wholeS = bool // CA: To be able to compile whole programs requires a proof that it can be compiled

// linking involves taking a program and context, extracting the first part of the dependent pair (so the program i.ct -> bool) and applying it to the context
let linkS (#i:intS) (ps:progS i) (cs:ctxS i) : wholeS =
  (dfst ps) cs

assume type behS_t
assume val behS : wholeS -> behS_t

(** Target **)
// right now, we give the target a source type (which might have pre post conditions, etc.) -> which is not a correct model of unverified code
// unverified code: target + target type (typ) 
// but maybe current typing works? cause you cannot have pre post conditions
// the type of target contexts restricts us to unverified code
noeq type intT = { ct : typsr }

val comp_int : intS -> intT
let comp_int i = { ct = pack i.comp_ct }

type progT (i:intT) = closed_exp

// the typing makes sure that there are no pre post conditions - maybe...
type ctxT (i:intT) = ct:value & typing empty ct i.ct
(** CA: syntactic typing necessary so that one can backtranslate and to know the type.
   **)
type wholeT = closed_exp

let linkT (#i:intT) (pt:progT i) (ct:ctxT i) : wholeT =
  let (| e, h |) = ct in
  let wt = EApp pt e in
  wt

assume type behT_t
assume val behT : wt:wholeT -> behT_t
assume val rel_behs : behS_t -> behT_t -> Type0

// will cause universe problems
let rec typ_to_fstar (t:typ) : Type =
  match t with
  | TUnit -> unit
  | TBool -> bool
  | TArr t1 t2 -> (typ_to_fstar t1) -> (typ_to_fstar t2)
  | TPair t1 t2 -> (typ_to_fstar t1) * (typ_to_fstar t2)

// keep this as typsr to avoid typ_to_fstar
// change typing to be over rrtype_to_ttype t - so typ
let rec exp_to_fstar (g:env) (e:exp) (t:typsr) (h:typing g e t) (fs_g:fs_env g) : (get_Type t) =
  match e with
  | EUnit -> ()
  | ETrue -> true
  | EFalse -> false
  | EIf e1 e2 e3 ->
    let TyIf #_ #_ #_ #_ #t h1 h2 h3 = h in
    let b : bool = exp_to_fstar g e1 tbool h1 fs_g in
    let v1 = exp_to_fstar g e2 t h2 fs_g in
    let v2 = exp_to_fstar g e3 t h3 fs_g in
    if b then v1 else v2
  | EVar x -> get_v fs_g x 
  | ELam body ->
    let TyLam #_ #_ #t1 #t2 hbody = h in
    assert (t == (mk_arrow t1 t2));
    let w : (get_Type t1) -> (get_Type t2) =
      (fun x -> exp_to_fstar (extend t1 g) body t2 hbody (fs_stack fs_g x)) in
    w
  | EApp e1 e2 ->
    let TyApp #_ #_ #_ #t1 #t2 h1 h2 = h in
    assert ((get_Type t) == (get_Type t2));
    let v1 : get_Type (mk_arrow t1 t2) = exp_to_fstar g e1 (mk_arrow t1 t2) h1 fs_g in
    let v2 : get_Type t1 = exp_to_fstar g e2 t1 h2 fs_g in
    v1 v2
  | EPair e1 e2 ->
    let TyPair #_ #_ #_ #t1 #t2 h1 h2 = h in
    let v1 = exp_to_fstar g e1 t1 h1 fs_g in
    let v2 = exp_to_fstar g e2 t2 h2 fs_g in
    (v1, v2)
  | EFst e ->
    let TyFst #_ #_ #t1 #t2 h1 = h in
    let v = exp_to_fstar g e (mk_pair t1 t2) h1 fs_g in
    fst #(get_Type t1) #(get_Type t2) v
  | ESnd e ->
    let TySnd #_ #_ #t1 #t2 h1 = h in
    let v = exp_to_fstar g e (mk_pair t1 t2) h1 fs_g in
    snd #(get_Type t1) #(get_Type t2) v

val backtranslate_ctx : (#i:intS) -> ctxT (comp_int i) -> ctxS i
let backtranslate_ctx (#i:intS) (ctxt:ctxT (comp_int i)) : ctxS i =
  let (| e, h |) = ctxt in
  exp_to_fstar empty e (comp_int i).ct h fs_empty

(** CA: I suppose these two lemmas are the most hard core **)
assume val lem_rel_beh (fs_e: wholeS) (e:wholeT) :
  Lemma
    (requires tbool ⦂ (fs_e, e)) (** here it is tbool because whole programs return booleans **)
    (ensures  (behS fs_e) `rel_behs` (behT e))

// prove that this is equivalent for any fs_g
// proof by induction on the expression (induction in backtranslation)
let exp_to_fstar_unit g
  : Lemma 
  (requires fv_in_env g EUnit)
  (ensures equiv tunit (exp_to_fstar g EUnit tunit TyUnit) EUnit)
  = assert (forall b (s:gsub g b) (fsG:fs_env g).
           fsG ∽ s ==> tunit ⦂ ((exp_to_fstar g EUnit tunit TyUnit) fsG, gsubst s EUnit)) 
    by (explode ())

let exp_to_fstar_true g
  : Lemma
  (requires fv_in_env g ETrue)
  (ensures equiv tbool (exp_to_fstar g ETrue tbool TyTrue) ETrue)
  = assert (forall b (s:gsub g b) (fsG:fs_env g).
           fsG ∽ s ==> tbool ⦂ ((exp_to_fstar g ETrue tbool TyTrue) fsG, gsubst s ETrue)) 
    by (explode ())

let exp_to_fstar_false g
  : Lemma
  (requires fv_in_env g EFalse)
  (ensures equiv tbool (exp_to_fstar g EFalse tbool TyFalse) EFalse)
  = assert (forall b (s:gsub g b) (fsG:fs_env g).
           fsG ∽ s ==> tbool ⦂ ((exp_to_fstar g EFalse tbool TyFalse) fsG, gsubst s EFalse)) 
    by (explode ())

let exp_to_fstar_var g (x:var{Some? (g x)}) h
  : Lemma
  (requires fv_in_env g (EVar x))
  (ensures equiv (Some?.v (g x)) (exp_to_fstar g (EVar x) (Some?.v (g x)) h) (EVar x))
  = 
  introduce forall b (s:gsub g b) fsG. fsG ∽ s ==> (Some?.v (g x)) ⦂ (get_v fsG x, gsubst s (EVar x)) with 
    begin
    introduce _ ==> _ with _.
      begin
      assert (Some?.v (g x) ∋ (get_v fsG x, s x));
      lem_values_are_expressions (Some?.v (g x)) (get_v fsG x) (s x)
      end
    end

let exp_to_fstar_pair g (t1 t2:typsr) (e1:exp) (e2:exp) fs_e1 fs_e2 : Lemma
  (requires equiv t1 fs_e1 e1 /\ equiv t2 fs_e2 e2 /\ fv_in_env g (EPair e1 e2))
  (ensures equiv (mk_pair t1 t2) (fun fsG -> (fs_e1 fsG, fs_e2 fsG)) (EPair e1 e2)) = 
  let t = mk_pair t1 t2 in
  introduce forall b (s:gsub g b) fsG. fsG ∽ s ==> t ⦂ ((fs_e1 fsG, fs_e2 fsG), gsubst s (EPair e1 e2)) with 
      begin
      let fs_e1 = fs_e1 fsG in
      let fs_e2 = fs_e2 fsG in
      let fs_e = (fs_e1, fs_e2) in
      let e = EPair (gsubst s e1) (gsubst s e2) in
      assert (gsubst s (EPair e1 e2) == e); 
      let EPair e1 e2 = e in
      introduce fsG ∽ s ==> t ⦂ (fs_e, e) with _. 
        begin
        introduce forall (e':closed_exp). steps e e' /\ irred e' ==> t ∋ (fs_e, e') with 
          begin
          introduce _ ==> t ∋ (fs_e, e') with h. 
            begin
            let steps_e_e' : squash (steps e e') = () in
            FStar.Squash.map_squash #_ #(squash (t ∋ (fs_e, e'))) steps_e_e' (fun steps_e_e' ->
              let (e1', e2') = destruct_steps_epair e1 e2 e' steps_e_e' in
              assert (t1 ∋ (fs_e1, e1'));
              assert (t2 ∋ (fs_e2, e2'));
              assert (t ∋ (fs_e, EPair e1' e2'));
              lem_destruct_steps_epair e1' e2' e';
              lem_values_are_expressions t fs_e (EPair e1' e2') // can turn this into e' - no?
            )
            end
          end
        end
      end

let exp_to_fstar_if g (t:typsr) (e1:exp) (e2:exp) (e3:exp) fs_e1 fs_e2 fs_e3 : Lemma
  (requires equiv tbool fs_e1 e1 /\ equiv t fs_e2 e2 /\ equiv t fs_e3 e3 /\ fv_in_env g (EIf e1 e2 e3))
  (ensures equiv t (fun fsG -> if (fs_e1 fsG) then (fs_e2 fsG) else (fs_e3 fsG)) (EIf e1 e2 e3)) =
  introduce forall b (s:gsub g b) fsG. fsG ∽ s ==> t ⦂ ((if (fs_e1 fsG) then (fs_e2 fsG) else (fs_e3 fsG)), gsubst s (EIf e1 e2 e3)) with 
      begin
      let fs_e1 : bool = fs_e1 fsG in
      let fs_e2 : (get_Type t) = fs_e2 fsG in
      let fs_e3 : (get_Type t) = fs_e3 fsG in
      let e = EIf (gsubst s e1) (gsubst s e2) (gsubst s e3) in
      assert (gsubst s (EIf e1 e2 e3) == e);
      let EIf e1 e2 e3 = e in
      introduce fsG ∽ s ==>  t ⦂ ((if fs_e1 then fs_e2 else fs_e3), e) with _.
        begin
        introduce forall (e':closed_exp). steps e e' /\ irred e' ==> t ∋ ((if fs_e1 then fs_e2 else fs_e3), e') with
          begin
          introduce _ ==> t ∋ ((if fs_e1 then fs_e2 else fs_e3), e') with h.
            begin
            let steps_e_e' : squash (steps e e') = () in
            FStar.Squash.map_squash #_ #(squash (t ∋ ((if fs_e1 then fs_e2 else fs_e3), e'))) steps_e_e' (fun steps_e_e' -> 
              let e1' = destruct_steps_eif e1 e2 e3 e' steps_e_e' in
              assert (tbool ∋ (fs_e1, e1'));
              assert (t ∋ ((if fs_e1 then fs_e2 else fs_e3), e'))
            )
            end
          end
        end
      end

let exp_to_fstar_fst g (t1 t2:typsr) (e12:exp) fs_e12 : Lemma
  (requires equiv (mk_pair t1 t2) fs_e12 e12 /\ fv_in_env g (EFst e12))
  (ensures equiv t1 (fun fsG -> fst #(get_Type t1) #(get_Type t2) (fs_e12 fsG)) (EFst e12)) =
  introduce forall b (s:gsub g b) fsG. fsG ∽ s ==> t1 ⦂ (fst #(get_Type t1) #(get_Type t2) (fs_e12 fsG), gsubst s (EFst e12)) with
      begin
      let fs_e12 = fs_e12 fsG in
      let fs_e = fst #(get_Type t1) #(get_Type t2) fs_e12 in
      let e = EFst (gsubst s e12) in
      assert (gsubst s (EFst e12) == e);
      let EFst e12 = e in
      introduce fsG ∽ s ==> t1 ⦂ (fs_e, e) with _. 
        begin
        introduce forall (e':closed_exp). steps e e' /\ irred e' ==> t1 ∋ (fs_e, e') with
          begin
          introduce _ ==> t1 ∋ (fs_e, e') with h. 
            begin
            let steps_e_e' : squash (steps e e') = () in
            FStar.Squash.map_squash #_ #(squash (t1 ∋ (fs_e, e'))) steps_e_e' (fun steps_e_e' -> 
              let e12' = destruct_steps_epair_fst e12 e' steps_e_e' in
              eliminate (mk_pair t1 t2) ⦂ (fs_e12, e12) /\ steps e12 e12' /\ irred e12'
              returns (mk_pair t1 t2) ∋ (fs_e12, e12') with _ _. ();
              let EPair e1' e2' = e12' in
              assert (t1 ∋ (fs_e, e1'));
              lem_destruct_steps_epair_fst e1' e2' e';
              assert (t1 ∋ (fs_e, e'))
              ) 
            end
          end
        end
      end

let exp_to_fstar_snd g (t1 t2:typsr) (e12:exp) fs_e12 : Lemma
  (requires equiv (mk_pair t1 t2) fs_e12 e12 /\ fv_in_env g (ESnd e12))
  (ensures equiv t2 (fun fsG -> snd #(get_Type t1) #(get_Type t2) (fs_e12 fsG)) (ESnd e12)) =
      introduce forall b (s:gsub g b) fsG. fsG ∽ s ==> t2 ⦂ (snd #(get_Type t1) #(get_Type t2) (fs_e12 fsG), gsubst s (ESnd e12)) with
      begin
      let fs_e12 = fs_e12 fsG in
      let fs_e = snd #(get_Type t1) #(get_Type t2) fs_e12 in
      let e = ESnd (gsubst s e12) in
      assert (gsubst s (ESnd e12) == e);
      let ESnd e12 = e in
      introduce fsG ∽ s ==> t2 ⦂ (fs_e, e) with _. 
        begin
        introduce forall (e':closed_exp). steps e e' /\ irred e' ==> t2 ∋ (fs_e, e') with
          begin
          introduce _ ==> t2 ∋ (fs_e, e') with h. 
            begin
            let steps_e_e' : squash (steps e e') = () in
            FStar.Squash.map_squash #_ #(squash (t2 ∋ (fs_e, e'))) steps_e_e' (fun steps_e_e' ->
              let e12' = destruct_steps_epair_snd e12 e' steps_e_e' in
              eliminate (mk_pair t1 t2) ⦂ (fs_e12, e12) /\ steps e12 e12' /\ irred e12'
              returns (mk_pair t1 t2) ∋ (fs_e12, e12') with _ _. ();
              let EPair e1' e2' = e12' in
              assert (t2 ∋ (fs_e, e2'));
              lem_destruct_steps_epair_snd e1' e2' e';
              assert (t2 ∋ (fs_e, e'))
              )
            end
          end
        end
      end

let exp_to_fstar_app g (t1 t2:typsr) (e1:exp) (e2:exp) fs_e1 fs_e2 : Lemma
  (requires equiv (mk_arrow t1 t2) fs_e1 e1 /\ equiv t1 fs_e2 e2 /\ fv_in_env g (EApp e1 e2))
  (ensures equiv t2 (fun fsG -> (fs_e1 fsG) (fs_e2 fsG)) (EApp e1 e2)) = 
    introduce forall b (s:gsub g b) fsG. fsG ∽ s ==> t2 ⦂ (((fs_e1 fsG) (fs_e2 fsG)), gsubst s (EApp e1 e2)) with
      begin
      let fs_e1 = fs_e1 fsG in
      let fs_e2 = fs_e2 fsG in
      let fs_e = fs_e1 fs_e2 in
      let e = EApp (gsubst s e1) (gsubst s e2) in
      assert (gsubst s (EApp e1 e2) == e);
      let EApp e1 e2 = e in
      introduce fsG ∽ s ==> t2 ⦂ (fs_e, e) with _.
        begin
        introduce forall (e':closed_exp). steps e e' /\ irred e' ==> t2 ∋ (fs_e, e') with
          begin
          introduce _ ==> t2 ∋ (fs_e, e') with h.
            begin
            let steps_e_e' : squash (steps e e') = () in
            FStar.Squash.map_squash #_ #(squash (t2 ∋ (fs_e, e'))) steps_e_e' (fun steps_e_e' -> 
              let (e11, e2') = destruct_steps_eapp e1 e2 e' steps_e_e' in
              assert (t1 ∋ (fs_e2, e2'));
              assert (irred (ELam e11));
              introduce True ==> t1 ∋ (fs_e2, e2') with _.
                begin
                assert (t1 ⦂ (fs_e2, e2));
                assert (steps e2 e2');
                assert (irred e2')
              end;
              eliminate forall (v:value) (fs_v:get_Type t1). t1 ∋ (fs_v, v) ==> 
                t2 ⦂ (fs_e1 fs_v, subst_beta v e11)
              with e2' fs_e2;
              assert (t2 ⦂ (fs_e, subst_beta e2' e11));
              assert (mk_arrow t1 t2 ∋ (fs_e1, ELam e11));
              assert (t2 ∋ (fs_e, e'))
              )
            end
          end
        end
      end
  

val lem_exp_to_fstar g (e:exp) t (h:typing g e t) : Lemma 
(equiv t (exp_to_fstar g e t h) e)
let rec lem_exp_to_fstar g e t (h:typing g e t) =
  assume(fv_in_env g e); 
   match e with
  | EUnit -> exp_to_fstar_unit g
  | ETrue -> exp_to_fstar_true g
  | EFalse -> exp_to_fstar_false g
  | EVar x -> exp_to_fstar_var g x h
  | EPair e1 e2 -> 
    let TyPair #_ #_ #_ #t1 #t2 h1 h2 = h in
    assume (fv_in_env g e1);
    assume (fv_in_env g e2);
    lem_exp_to_fstar g e1 t1 h1;
    lem_exp_to_fstar g e2 t2 h2;
    let fs_e1 = (exp_to_fstar g e1 t1 h1) in
    let fs_e2 = (exp_to_fstar g e2 t2 h2) in
    exp_to_fstar_pair g t1 t2 e1 e2 fs_e1 fs_e2
  | EIf e1 e2 e3 ->
    let TyIf #_ #_ #_ #_ #t h1 h2 h3 = h in
    assume (fv_in_env g e1);
    assume (fv_in_env g e2);
    assume (fv_in_env g e3);
    lem_exp_to_fstar g e1 tbool h1;
    lem_exp_to_fstar g e2 t h2;
    lem_exp_to_fstar g e3 t h3;
    let fs_e1 = (exp_to_fstar g e1 tbool h1) in
    let fs_e2 = (exp_to_fstar g e2 t h2) in
    let fs_e3 = (exp_to_fstar g e3 t h3) in
    exp_to_fstar_if g t e1 e2 e3 fs_e1 fs_e2 fs_e3
  | EFst e12 ->
    let TyFst #_ #_ #t1 #t2 h1 = h in
    assume (fv_in_env g e12);
    lem_exp_to_fstar g e12 (mk_pair t1 t2) h1;
    let fs_e12 = (exp_to_fstar g e12 (mk_pair t1 t2) h1) in
    exp_to_fstar_fst g t1 t2 e12 fs_e12  
  | ESnd e12 ->
    let TySnd #_ #_ #t1 #t2 h1 = h in
    assume (fv_in_env g e12);
    lem_exp_to_fstar g e12 (mk_pair t1 t2) h1;
    let fs_e12 = (exp_to_fstar g e12 (mk_pair t1 t2) h1) in
    exp_to_fstar_snd g t1 t2 e12 fs_e12
  | EApp e1 e2 ->
    let TyApp #_ #_ #_ #t1 #t2 h1 h2 = h in
    assume (fv_in_env g e1);
    assume (fv_in_env g e2);
    lem_exp_to_fstar g e1 (mk_arrow t1 t2) h1;
    lem_exp_to_fstar g e2 t1 h2;
    let fs_e1 = (exp_to_fstar g e1 (mk_arrow t1 t2) h1) in
    let fs_e2 = (exp_to_fstar g e2 t1 h2) in
    exp_to_fstar_app g t1 t2 e1 e2 fs_e1 fs_e2
  | ELam body ->
    let TyLam #_ #body #t1 #t2 hbody = h in
    assume (fv_in_env (extend t1 g) body);
    lem_exp_to_fstar (extend t1 g) body t2 hbody;
    assert (equiv t2 (exp_to_fstar (extend t1 g) body t2 hbody) body);
    assert (forall b (s:gsub (extend t1 g) b) (fsG:fs_env (extend t1 g)). fsG ∽ s ==> t2 ⦂ ((exp_to_fstar (extend t1 g) body t2 hbody) fsG, gsubst s body)); 
    let g' = extend t1 g in
    introduce forall b (s:gsub g b) (fsG:fs_env g). fsG ∽ s ==> (mk_arrow t1 t2) ⦂ ((fun x -> exp_to_fstar (extend t1 g) body t2 hbody (fs_stack fsG x)), gsubst s (ELam body)) with
      begin
      let f : (get_Type t1) -> (get_Type t2) = (fun x -> exp_to_fstar (extend t1 g) body t2 hbody (fs_stack fsG x)) in 
      let body' = subst (sub_elam s) body in
      assert (gsubst s (ELam body) == ELam body');
      introduce  fsG ∽ s ==> (mk_arrow t1 t2) ⦂ (f, ELam body') with _. 
        begin
        introduce forall (e':closed_exp). steps (ELam body') e' /\ irred e' ==> (mk_arrow t1 t2) ∋ (f, e') with
          begin
          assume ((ELam body') == e');
          introduce _ ==> (mk_arrow t1 t2) ∋ (f, e') with h.
            begin
            let RArr #s1 #s2 r1 r2 = get_rel (mk_arrow t1 t2) in
            introduce forall (v:value) (fs_v:get_Type t1). t1 ∋ (fs_v, v) ==> t2 ⦂ (f fs_v, subst_beta v body') with 
              begin
              introduce  t1 ∋ (fs_v, v) ==> _ with _.
                begin
                let s' = gsub_extend s t1 v in
                let fsG' = fs_stack fsG fs_v in
                lem_substitution s t1 v body;
                assert (t2 ⦂ (f fs_v, gsubst s' body))
                end
              end;
              assert ((mk_arrow t1 t2) ∋ (f, gsubst s (ELam body)));
              lem_values_are_expressions (mk_arrow t1 t2) f (gsubst s (ELam body));
              assert ((mk_arrow t1 t2) ⦂ (f, gsubst s (ELam body))) 
            end
          end
        end
      end

val lem_bt_ctx i ct : Lemma (
  let (| e, h |) = ct in
  pack i.comp_ct ∋ (backtranslate_ctx #i ct, e)
  )
let lem_bt_ctx i ct =
  let (| e, h |) = ct in
  lem_exp_to_fstar empty e (comp_int i).ct h;
  equiv_closed_terms #(comp_int i).ct (exp_to_fstar empty e (comp_int i).ct h fs_empty) e;
  // t : (bt e, e) and the fact that e is a value implies they are in the value relation (the statement of the lemma)
  ()

let compile_prog (#i:intS) (ps:progS i) : progT (comp_int i) =
  (dsnd ps).e

(** The order of the quantifiers makes this RHC (Robust Hyperproperty Preservation) **)
let rhc (#i:intS) (ps:progS i) =
  forall (ct:ctxT (comp_int i)).
    exists (cs:ctxS i). behS (linkS ps cs) `rel_behs` behT (linkT (compile_prog ps) ct)

let rhc_1 (#i:intS) (ps:progS i) =
  forall ct. behS (linkS ps (backtranslate_ctx ct)) `rel_behs` behT (linkT (compile_prog ps) ct)

let proof_rhc i ps : Lemma (rhc_1 #i ps) =
  introduce forall ct. behS (linkS ps (backtranslate_ctx ct)) `rel_behs` behT (linkT (compile_prog ps) ct) with begin
    let t : typsr = pack (i.comp_ct) in
    let pt : exp = (dsnd ps).e in
    let pt : progT (comp_int i) = pt in
    let ws : wholeS = (dfst ps) (backtranslate_ctx ct) in
    let (| e, h |) = ct in
    let wt : exp = EApp pt e in
    let wt : wholeT = wt in
    (dsnd ps).equiv_proof ();
    let ps' = dfst ps in
    lemma_compile_closed_in_equiv_rel ps' #(dsnd ps);
    assert (mk_arrow t tbool ⦂ (ps', pt));
    lemma_compile_closed_arrow_is_elam #_ #_ #i.comp_ct ps' #(dsnd ps);
    assert (ELam? pt /\ is_closed pt /\ irred pt);
    eliminate forall (e':closed_exp). steps pt e' ==> irred e' ==> mk_arrow t tbool ∋ (ps', e') with pt;
    assert (mk_arrow t tbool ∋ (ps', pt));
    eliminate forall (v:value) (fs_v:get_Type t). t ∋ (fs_v, v) ==>
        tbool ⦂ (ps' fs_v, subst_beta v (ELam?.b pt))
      with e (backtranslate_ctx ct);
    lem_bt_ctx i ct;
    assert (tbool ⦂ (ps' (backtranslate_ctx ct), subst_beta e (ELam?.b pt)));
    lem_rel_beh (ps' (backtranslate_ctx ct)) (subst_beta e (ELam?.b pt));
    assume (behT (EApp pt e) == behT (subst_beta e (ELam?.b pt))); (** simple to prove **)
    ()
  end

