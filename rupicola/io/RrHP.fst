module RrHP

open FStar.Tactics
open FStar.Tactics.Typeclasses

open STLC
open QTyp
open QExp
open ExpRel
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
  // should exp_quotation also carry fs_event trace?
type progS (i:intS) =
  (ps:(get_Type i.ct -> bool) & exp_quotation #(i.ct ^-> qBool) empty (fun _ -> ps))
  * 
  (list fs_event * list event) // might need to change these to be dependent tuples

type ctxS (i:intS) = get_Type i.ct
type wholeS = bool // CA: To be able to compile whole programs requires a proof that it can be compiled

// linking involves taking a program and context, extracting the first part of the dependent pair (so the program i.ct -> bool) and applying it to the context
let linkS (#i:intS) (ps:progS i) (cs:ctxS i) : wholeS =
  let ((| fs_e, e |), (fs_e_tr, e_tr )) = ps in 
  fs_e cs

type behS_t = bool
val behS : wholeS -> behS_t
let behS ws = ws

(** Target **)
// right now, we give the target a source type (which might have pre post conditions, etc.) -> which is not a correct model of unverified code
// unverified code: target + target type (typ)
// but maybe current typing works? cause you cannot have pre post conditions
// the type of target contexts restricts us to unverified code
noeq type intT = { ct : qType }

val comp_int : intS -> intT
//let comp_int i = { ct = type_quotation_to_typ i.qct }
let comp_int i = { ct = i.ct }

type progT (i:intT) = closed_exp * list event

// the typing makes sure that there are no pre post conditions - maybe...
type ctxT (i:intT) = ct:value & typing empty ct i.ct
(** syntactic typing necessary to be able to backtranslate **)
type wholeT = closed_exp

let linkT (#i:intT) (pt:progT i) (ct:ctxT i) : wholeT =
  let (| e, h |) = ct in
  let (e_pt, tr_pt) = pt in
  let wt = EApp e_pt e in
  wt

let compile_prog (#i:intS) (ps:progS i) : progT (comp_int i) =
  let ((| fs_e, e |), (fs_tr, tr)) = ps in
  ((compile_closed e), tr)
  // needs to be fixed to be the list of events from quotation

let rel_bools (fs_e:bool) (e:exp) : Type0 =
  (e == ETrue /\ fs_e == true) \/
  (e == EFalse /\ fs_e == false)

let rel_traces (fs_tr:list fs_event) (tr:list event) : Type0 =
  trace_related fs_tr tr

type behT_t = bool -> Type0
val behT : wt:wholeT -> tr:list event -> behT_t
let behT wt tr = fun x -> // need to change this to rel_traces when we want to start looking at traces
(** vvv To have an existential here one needs normalization **)
  forall (e':closed_exp). steps wt e' tr /\ irred e' ==>
    rel_bools x e'

val rel_behs : behS_t -> behT_t -> Type0
let rel_behs (bs:behS_t) (bt:behT_t) =
  bt bs

let lem_rel_beh (fs_e:wholeS) (fs_tr:list fs_event) (e:wholeT) (tr:list event)  
  : Lemma
  (requires qBool ⦂ ((fs_e, fs_tr), (e, tr)))
  (ensures  (behS fs_e) `rel_behs` (behT e tr))
  = ()

(** ** Proof of RrHP **)

val backtranslate_ctx : (#i:intS) -> ctxT (comp_int i) -> ctxS i
let backtranslate_ctx (#i:intS) (ctxt:ctxT (comp_int i)) : ctxS i =
  let (| e, h |) = ctxt in
  backtranslate empty e (comp_int i).ct h empty_eval


val lem_bt_ctx i ct : Lemma (
  let (| e, h |) = ct in
    (comp_int i).ct ∋ ((backtranslate_ctx #i ct, []), (e, []))
  )
let lem_bt_ctx i ct =
  let (| e, h |) = ct in
  lem_value_is_closed e;
  lem_closed_is_no_fv e;
  assert (fv_in_env empty e);
  lem_backtranslate empty e (comp_int i).ct h #[] #[];
  equiv_closed_terms #[] #[] #(comp_int i).ct (backtranslate empty e (comp_int i).ct h empty_eval) e;
  // t : (bt e, e) and the fact that e is a value implies they are in the value relation (the statement of the lemma)
  ()

(** This variant implies RrHP **)
let rrhp_1 (#i:intS) =
  forall (ps:progS i).
    forall ct. behS (linkS ps (backtranslate_ctx ct)) `rel_behs` behT (linkT (compile_prog ps) ct) (snd (compile_prog ps) @ [])

let proof_rrhp_1 i : Lemma (rrhp_1 #i) =
  introduce forall ps ct. behS (linkS ps (backtranslate_ctx ct)) `rel_behs` behT (linkT (compile_prog ps) ct) (snd (compile_prog ps) @ []) with begin
    let t : qType = i.ct in
    let pt : progT (comp_int i) = compile_prog ps in
    let ((| fs_e_ps, e_ps |), (fs_tr, tr)) = ps in
    let ws : wholeS = fs_e_ps (backtranslate_ctx ct) in
    let (| e, h |) = ct in
    let (e_pt, tr_pt) = pt in
    let wt : exp = EApp e_pt e in
    let wt : wholeT = wt in
    compile_equiv #empty #fs_tr #tr e_ps;
    let ps' = fs_e_ps in
    compile_closed_equiv #(t ^-> qBool) #_  #fs_tr #tr e_ps;
    assert ((t ^-> qBool) ⦂ ((ps', fs_tr), (e_pt, tr_pt)));
    lemma_compile_closed_arrow_is_elam e_ps;
    assert (ELam? e_pt /\ is_closed e_pt /\ irred e_pt);
    eliminate forall (e':closed_exp). steps e_pt e' tr_pt ==> irred e' ==> (t ^-> qBool) ∋ ((ps', fs_tr), (e', tr_pt)) with e_pt;
    assume ((t ^-> qBool) ∋ ((ps', fs_tr), (e_pt, tr_pt)));
    eliminate forall (v:value) (fs_v:get_Type t) (tr':list event) (fs_tr':list fs_event). t ∋ ((fs_v, fs_tr'), (v, tr')) /\ (trace_related fs_tr' tr') ==> exists (tr'':list event) (fs_tr'':list fs_event).
        qBool ⦂ ((ps' fs_v, fs_tr''), (subst_beta v (ELam?.b e_pt), tr'')) /\ (trace_related fs_tr'' tr'') /\ (tr_pt == tr' @ tr'') /\ (fs_tr == fs_tr' @ fs_tr'') 
      with e_pt (backtranslate_ctx ct) [] [];
    lem_bt_ctx i ct;
    assert (qBool ⦂ ((ps' (backtranslate_ctx ct), fs_tr), (subst_beta e (ELam?.b e_pt), tr_pt)));
    lem_rel_beh (ps' (backtranslate_ctx ct)) fs_tr (subst_beta e (ELam?.b e_pt)) tr_pt;
    assume (behT (EApp e_pt e) tr_pt == behT (subst_beta e (ELam?.b e_pt)) tr_pt); (** simple to prove **)
    assume (tr_pt == tr_pt @ []);
    ()
  end
