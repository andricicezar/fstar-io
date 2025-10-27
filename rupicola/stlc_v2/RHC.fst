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

noeq type intT = { ct : typsr }

val comp_int : intS -> intT
let comp_int i = { ct = (| i.ct, (i.comp_ct).r |) }

type progT (i:intT) = closed_exp

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

let rec typ_to_fstar (t:typ) : Type =
  match t with
  | TUnit -> unit
  | TBool -> bool
  | TArr t1 t2 -> (typ_to_fstar t1) -> (typ_to_fstar t2)
  | TPair t1 t2 -> (typ_to_fstar t1) * (typ_to_fstar t2)

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
  | ELam b ->
    let TyLam #_ #_ #t1 #t2 hbody = h in
    assert (t == (mk_arrow t1 t2));
    let w : (get_Type t1) -> (get_Type t2) =
      (fun x -> exp_to_fstar (extend t1 g) b t2 hbody (fs_stack fs_g x)) in
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

assume val lem_bt_ctx i ct : Lemma (
  let (| e, h |) = ct in
  pack i.comp_ct ∋ (backtranslate_ctx #i ct, e)
  )

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

