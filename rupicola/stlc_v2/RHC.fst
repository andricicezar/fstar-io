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

noeq type intT = { ct : typ }

let rec rtype_to_ttype s (r:rtyp s) : typ = 
  match r with 
  | RUnit -> TUnit
  | RBool -> TBool
  | RArr #s1 #s2 rs1 rs2 -> TArr (rtype_to_ttype s1 rs1) (rtype_to_ttype s2 rs2)
  | RPair #s1 #s2 rs1 rs2 -> TPair (rtype_to_ttype s1 rs1) (rtype_to_ttype s2 rs2)

let rec sem_typing (g:env) (t:typ) (e:exp) : Tot Type 
  (decreases e)
  =
  match (t, e) with
  | (TUnit, EUnit) -> true
  | (TBool, ETrue) -> true
  | (TBool, EFalse) -> true
  | (TPair t1 t2, EPair e1 e2) -> (sem_typing g t1 e1) /\ (sem_typing g t2 e2)
  | (t, EIf e1 e2 e3) -> (sem_typing g TBool e1) /\ (sem_typing g t e2) /\ (sem_typing g t e3)
  | _ -> false

val comp_int : intS -> intT
let comp_int i = { ct = (rtype_to_ttype i.ct (i.comp_ct).r) }

type progT (i:intT) = closed_exp

type ctxT (i:intT) = ct:value{sem_typing empty i.ct ct}
(** CA: syntactic typing necessary so that one can backtranslate and to know the type.
   **)
type wholeT = closed_exp

let linkT (#i:intT) (pt:progT i) (ct:ctxT i) : wholeT =
  let wt = EApp pt ct in
  wt

assume type behT_t
assume val behT : wt:wholeT -> behT_t
assume val rel_behs : behS_t -> behT_t -> Type0

//let num_bind (#i:intS) (ctxt:ctxT (comp_int i)) : nat =
//  snd (free_vars_indx ctxt 0)

//type bt_env : var -> option typ

val backtranslate_ctx : (#i:intS) -> ctxT (comp_int i) -> ctxS i
let rec backtranslate_ctx (#i:intS) (ctxt:ctxT (comp_int i)) : ctxS i =
  match ctxt with 
  | EUnit -> ()
  | ETrue -> true
  | EFalse -> false
  | EPair e1 e2 ->
    let RPair #s1 #s2 r1 r2 = (i.comp_ct).r in
    let comp_ct_1 : compile_typ s1 = admit () in
    let comp_ct_2 : compile_typ s2 = admit () in
    let intS_1 : intS = { ct = s1; comp_ct = comp_ct_1 } in
    let intS_2 : intS = { ct = s2; comp_ct = comp_ct_2 } in
    ((backtranslate_ctx #intS_1 e1), (backtranslate_ctx #intS_2 e2))
  | EIf e1 e2 e3 -> 
    let s = i.ct in
    let intS_b : intS = { ct = bool; comp_ct = compile_typ_bool } in
    let comp_ct_t: compile_typ s = admit () in
    let intS_t : intS = { ct = s; comp_ct = comp_ct_t } in
    let b = backtranslate_ctx #intS_b e1 in
    let _ = assert(b == true \/ b == false) in
    let v1 = backtranslate_ctx #intS_t e2 in
    let v2 = backtranslate_ctx #intS_t e3 in
    if b then v1 else v2
  | _ -> ()
  //  let v2 = backtranslate_ctx #i e3 in
  //  let _ = assert(b == true \/ b == false) in
  //  if b then v1 else v2
  //| EVar v -> ()
  //| ELam b -> fun () -> (backtranslate_ctx #i b)
  (*| EApp e1 e2 -> begin 
    let v1 = backtranslate_ctx e1 n in
    let v2 = backtranslate_ctx e2 n in
    v1 v2
  end*)
  //| EPair e1 e2 -> 
  //  let _ = assume(sem_typing empty (comp_int i).ct e1) in
  (*  let _ = assume(sem_typing empty (comp_int i).ct e2) in
    let ct1: compile_typ (fst i.ct) = solve in
    let ct2: compile_typ (snd i.ct) = solve in
    let i1: intS = { ct = (fst i.ct); comp_ct = ct1 } in
    let i2: intS = { ct = (snd i.ct); comp_ct = ct2 } in
    let v1 = backtranslate_ctx #i1 e1 in
    let v2 = backtranslate_ctx #i2 e2 in
    (v1, v2)*)
  //| EFst e1 -> fst (backtranslate_ctx #i e1 n)
  //| ESnd e1 -> snd (backtranslate_ctx #i e1 n)

(*let i_unit : intS = { ct = unit; comp_ct = compile_typ_unit }
let result_unit = backtranslate_ctx #i_unit EUnit
let _ = assert(result_unit == ())

let i_bool : intS = { ct = bool; comp_ct = compile_typ_bool }
let result_true = backtranslate_ctx #i_bool ETrue
let result_false = backtranslate_ctx #i_bool EFalse
let _ = assert(result_true == true)
let _ = assert(result_false == false)

let i_pair : intS = { ct = unit * unit; comp_ct = compile_typ_pair unit unit #compile_typ_unit #compile_typ_unit }
let result_unit_unit = backtranslate_ctx #i_pair (EPair EUnit EUnit)
let _ = assert(result_unit_unit == ((), ()))*)


(** CA: I suppose these two lemmas are the most hard core **)
assume val lem_rel_beh (fs_e: wholeS) (e:wholeT) :
  Lemma
    (requires tbool ⦂ (fs_e, e)) (** here it is tbool because whole programs return booleans **)
    (ensures  (behS fs_e) `rel_behs` (behT e))

assume val lem_bt_ctx i ct : Lemma (pack i.comp_ct ∋ (backtranslate_ctx #i ct, ct))

(*
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
    let wt : exp = EApp pt ct in
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
      with ct (backtranslate_ctx ct);
    lem_bt_ctx i ct;
    assert (tbool ⦂ (ps' (backtranslate_ctx ct), subst_beta ct (ELam?.b pt)));
    lem_rel_beh (ps' (backtranslate_ctx ct)) (subst_beta ct (ELam?.b pt));
    assume (behT (EApp pt ct) == behT (subst_beta ct (ELam?.b pt))); (** simple to prove **)
    ()
  end
*)
