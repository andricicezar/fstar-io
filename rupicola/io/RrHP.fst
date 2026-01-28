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
type behS_t = hist_post [] bool
val behS : wholeS -> behS_t
let behS ws = fs_beh ws []

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
type ctxT (i:intT) = ct:closed_exp{is_value ct} & typing empty ct i.ct
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
let behT wt = fun (lt, r) -> e_beh wt r [] lt

val rel_behs : behS_t -> behT_t -> Type0
let rel_behs (bs:behS_t) (bt:behT_t) =
  forall rS rT lt. rel_bools rS rT ==>
    (bs lt rS <==>  bt (lt, rT))

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
  let (| e, tyj |) = ct in
  let cs = backtranslate tyj in
  let t = (comp_int i).ct in
  lem_value_is_closed e;
  lem_closed_is_no_fv e;
  assert (fv_in_env empty e);
  lem_backtranslate tyj;
  assert (cs ≈ e);
  lem_equiv_val #t (cs empty_eval) e;
  lem_values_in_exp_rel_are_in_val_rel t (cs empty_eval) e

(** This variant implies RrHP **)
let rrhp_1 (#i:intS) =
  forall (ps:progS i).
    forall ct. behS (linkS ps (backtranslate_ctx ct)) `rel_behs` behT (linkT (compile_prog ps) ct)

val compile_prog_equiv #i (ps:progS i)
  : Lemma (ensures (forall h. (i.ct ^->!@ qBool) ∋ (h, dfst ps, compile_closed (dsnd ps))))
let compile_prog_equiv #i pS =
    let t : qType = i.ct in
    let (| ps, qps |) = pS in
    let pt : progT (comp_int i) = compile_prog pS in
    compile_closed_equiv qps;
    assert (forall h. (t ^->!@ qBool) ⦂ (h, ps, pt));
    lemma_compile_closed_arrow_is_elam qps;
    assert (ELam? pt /\ is_closed pt);
    lem_value_is_irred pt;
    assert (is_value pt);
    lem_value_is_irred pt;
    introduce forall h. (t ^->!@ qBool) ∋ (h, ps, pt) with begin
      eliminate forall (pt':closed_exp) lt.
        steps pt pt' h lt ==> indexed_irred pt' (h++lt) ==>
        ((t ^->!@ qBool) ∋ (h, ps, pt') /\ lt == []) with pt []
    end

let proof_rrhp_1 i : Lemma (rrhp_1 #i) =
  introduce forall pS cT. behS (linkS pS (backtranslate_ctx cT)) `rel_behs` behT (linkT (compile_prog pS) cT) with begin
    let t : qType = i.ct in
    let (| ps, qps |) = pS in
    let pt : progT (comp_int i) = compile_prog pS in
    let cs = backtranslate_ctx cT in
    let (| ct, tyj |) = cT in
    let ws : wholeS = ps cs in
    lemma_compile_closed_arrow_is_elam qps;
    assert (ELam? pt /\ is_closed pt);
    let wt : wholeT = subst_beta ct (ELam?.b pt) in

    compile_prog_equiv pS;
    assert (forall h. (t ^->!@ qBool) ∋ (h, ps, pt)); (** unfold ∋ **)
    unroll_elam_io' t qBool ps (ELam?.b pt);
    assert (forall h (v:value) (fs_v:get_Type t) (lt_v:local_trace h). t ∋ (h++lt_v, fs_v, v) ==>
        qBool ⪾ (h++lt_v, ps fs_v, subst_beta v (ELam?.b pt)));
    (** eliminate v fs_v with ct cs **)
    assert (forall h (lt_v:local_trace h). t ∋ (h++lt_v, cs, ct) ==>
        qBool ⪾ (h++lt_v, ps cs, subst_beta ct (ELam?.b pt)));
    introduce forall h. t ∋ (h, cs, ct) ==> qBool ⪾ (h, ps cs, subst_beta ct (ELam?.b pt)) with begin
      eliminate forall h (lt_v:local_trace h). t ∋ (h++lt_v, cs, ct) ==> qBool ⪾ (h++lt_v, ps cs, subst_beta ct (ELam?.b pt))
      with h []
    end;
    lem_bt_ctx i cT;
    assert (forall h. qBool ⪾ (h, ps cs, subst_beta ct (ELam?.b pt)));
    lem_rel_beh ws (subst_beta ct (ELam?.b pt));
    assume (behT (EApp pt ct) == behT wt); (** simple to prove **)
    ()
  end
