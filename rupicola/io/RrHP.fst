module RrHP

open FStar.Tactics
open FStar.Tactics.Typeclasses

open STLC
open QTyp
open QExp
open ExpRel
open Trace
open IO
open Compilation
open Backtranslation

noeq type intS = {
  ct : qType;
}

(* CA: this definition of progS is very comical! I have the compiled program inside the guarantee that it can be compiled :D **)
// program parameterized by the type of the context
// program is dependent pair type with:
  // map from the type of context to bool (which represents output of the source program)
  // (proof of) compiled closed expression - where we pass in the type of ps (#_), the (proof of the) type of the compiled closed expression (#(compile_typ_arrow ...)), and ps
type progS (i:intS) =
  ps:(fs_val (i.ct ^->!@ qBool))
  &
  (i.ct ^->!@ qBool) ⊩ ps

type ctxS (i:intS) = fs_val i.ct
type wholeS = fs_prod qBool // CA: To be able to compile whole programs requires a proof that it can be compiled

// linking involves taking a program and context, extracting the first part of the dependent pair (so the program i.ct -> bool) and applying it to the context
let linkS (#i:intS) (ps:progS i) (cs:ctxS i) : wholeS =
  (dfst ps) cs

(** Definition from SCIO*, section 6.2 **)
type behS_t = local_trace [] * bool -> Type0
val behS : wholeS -> behS_t
let behS ws = fun (lt, res) -> forall p. theta ws [] p ==> p lt res

(** Target **)
// right now, we give the target a source type (which might have pre post conditions, etc.) -> which is not a correct model of unverified code
// unverified code: target + target type (typ)
// but maybe current typing works? cause you cannot have pre post conditions
// the type of target contexts restricts us to unverified code
noeq type intT = { ct : qType }

val comp_int : intS -> intT
//let comp_int i = { ct = type_quotation_to_typ i.qct }
let comp_int i = { ct = i.ct }

type progT (i:intT) = closed_exp

// the typing makes sure that there are no pre post conditions - maybe...
type ctxT (i:intT) = ct:value & typing empty ct i.ct
(** syntactic typing necessary to be able to backtranslate **)
type wholeT = closed_exp

let linkT (#i:intT) (pt:progT i) (ct:ctxT i) : wholeT =
  let (| e, h |) = ct in
  let wt = EApp pt e in
  wt

let compile_prog (#i:intS) (ps:progS i) : progT (comp_int i) =
  compile_closed (dsnd ps)

let rel_bools (fs_e:bool) (e:closed_exp) : Type0 =
  (e == ETrue /\ fs_e == true) \/
  (e == EFalse /\ fs_e == false)

type behT_t = local_trace [] * closed_exp -> Type0
val behT : wt:wholeT -> behT_t
let behT wt = fun (lt, r) -> steps wt r [] lt

val rel_behs : behS_t -> behT_t -> Type0
let rel_behs (bs:behS_t) (bt:behT_t) =
  (forall rS lt. bs (lt, rS) ==>  (exists rT. rel_bools rS rT /\ bt (lt, rT))) /\
  (forall rT lt. bt (lt, rT) ==>  (exists rS. rel_bools rS rT /\ bs (lt, rS)))

let lem_rel_beh (fs_e:wholeS) (e:wholeT)
  : Lemma
  (requires forall h. qBool ⪾ (h, fs_e, e))
  (ensures  (behS fs_e) `rel_behs` (behT e))
  = admit ()

(** ** Proof of RrHP **)

val backtranslate_ctx : (#i:intS) -> ctxT (comp_int i) -> ctxS i
let backtranslate_ctx (#i:intS) (ctxt:ctxT (comp_int i)) : ctxS i =
  let (| e, h |) = ctxt in
  backtranslate h empty_eval


val lem_bt_ctx i ct : Lemma (
  forall h.
  let (| e, _ |) = ct in
    (comp_int i).ct ∋ (h, backtranslate_ctx #i ct, e)
  )

let lem_bt_ctx i ct =
  let (| e, h |) = ct in
  lem_value_is_closed e;
  lem_closed_is_no_fv e;
  assert (fv_in_env empty e);
  lem_backtranslate h;
  lem_equiv_val #(comp_int i).ct (backtranslate h empty_eval) e;
  // t : (bt e, e) and the fact that e is a value implies they are in the value relation (the statement of the lemma)
  ()

(** This variant implies RrHP **)
let rrhp_1 (#i:intS) =
  forall (ps:progS i).
    forall ct. behS (linkS ps (backtranslate_ctx ct)) `rel_behs` behT (linkT (compile_prog ps) ct)

let proof_rrhp_1 i : Lemma (rrhp_1 #i) =
  introduce forall ps ct. behS (linkS ps (backtranslate_ctx ct)) `rel_behs` behT (linkT (compile_prog ps) ct) with begin
    let t : qType = i.ct in
    let pt : progT (comp_int i) = compile_prog ps in
    let ws : wholeS = (dfst ps) (backtranslate_ctx ct) in
    let (| e, h |) = ct in
    let wt : exp = EApp pt e in
    let wt : wholeT = wt in
    compile_equiv (dsnd ps);
    let ps' = dfst ps in
    compile_closed_equiv (dsnd ps);
    admit ()
    (**
    assert ((t ^-> qBool) ⦂ (ps', pt));
    lemma_compile_closed_arrow_is_elam (dsnd ps);
    assert (ELam? pt /\ is_closed pt);
    lem_value_is_irred pt;
    eliminate forall (e':closed_exp). steps pt e' ==> irred e' ==>  (t ^-> qBool) ∋ (ps', e') with pt;
    assert ((t ^-> qBool) ∋ (ps', pt));
    eliminate forall (v:value) (fs_v:get_Type t). t ∋ (fs_v, v) ==>
        qBool ⦂ (ps' fs_v, subst_beta v (ELam?.b pt))
      with e (backtranslate_ctx ct);
    lem_bt_ctx i ct;
    assert (qBool ⦂ (ps' (backtranslate_ctx ct), subst_beta e (ELam?.b pt)));
    lem_rel_beh (ps' (backtranslate_ctx ct)) (subst_beta e (ELam?.b pt));
    assume (behT (EApp pt e) == behT (subst_beta e (ELam?.b pt))); (** simple to prove **)
    ()**)
  end
