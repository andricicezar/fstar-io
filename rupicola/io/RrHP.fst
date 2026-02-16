module RrHP

open FStar.Tactics
open FStar.Tactics.Typeclasses

open STLC
open QTyp
open QExp
open Trace
open IO
open Compilation
open Backtranslation
open LogRelSourceTarget
open LogRelTargetSource

noeq type intS = {
  ct : qType;
}

// program parameterized by the type of the context
// program is dependent pair type with:
  // map from the type of context to bool (which represents output of the source program)
  // (proof of) compiled closed expression - where we pass in the type of ps (#_), the (proof of the) type of the compiled closed expression (#(compile_typ_arrow ...)), and ps
type progS (i:intS) =
  ps:(fs_val (i.ct ^->!@ qBool))
  &
  qs:((i.ct ^->!@ qBool) ⊩ ps){ QLambdaProd? qs }

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
  lem_compile_closed_valid (dsnd ps);
  compile (dsnd ps)

let rel_bools (fs_e:bool) (e:closed_exp) : Type0 =
  (e == ETrue /\ fs_e == true) \/
  (e == EFalse /\ fs_e == false)

type behT_t = local_trace [] * closed_exp -> Type0
val behT : wt:wholeT -> behT_t
let behT wt = fun (lt, r) -> e_beh wt r [] lt

unfold val behT_in_behS : behT_t -> behS_t -> Type0
let behT_in_behS bt bs = 
  (forall rT lt. bt (lt, rT) ==> (exists rS. rel_bools rS rT /\ bs lt rS))

val rel_behs : behS_t -> behT_t -> Type0
let rel_behs bs bt =
  (forall rS lt. bs lt rS ==> (exists rT. rel_bools rS rT /\ bt (lt, rT))) /\
  behT_in_behS bt bs

let lem_rel_behTS (fs_e:wholeS) (e:wholeT)
  : Lemma
  (requires valid_superset_prod fs_e e)
  (ensures  (behT e) `behT_in_behS` (behS fs_e))
  =
  introduce forall rT lt. (behT e) (lt, rT) ==> (exists rS. rel_bools rS rT /\ (behS fs_e) lt rS) with begin
    introduce _ ==> _ with _. begin
      ()
    end
  end

let lem_rel_beh (fs_e:wholeS) (e:wholeT)
  : Lemma
  (requires valid_superset_prod fs_e e /\ valid_subset_prod fs_e e)
  (ensures  (behS fs_e) `rel_behs` (behT e))
  =
  introduce forall rS lt. (behS fs_e) lt rS ==> (exists rT. rel_bools rS rT /\ (behT e) (lt, rT)) with begin
    introduce _ ==> _ with _. begin
      assert ((fs_beh fs_e []) lt rS)
    end
  end;
  lem_rel_behTS fs_e e

(** ** Proof of RrHP **)

val backtranslate_ctx : (#i:intS) -> ctxT (comp_int i) -> ctxS i
let backtranslate_ctx (#i:intS) (ctxt:ctxT (comp_int i)) : ctxS i =
  let (| e, h |) = ctxt in
  backtranslate h

let rrhp (i:intS) =
  forall ct. exists cs.
    forall (ps:progS i).
      behS (linkS ps cs) `rel_behs` behT (linkT (compile_prog ps) ct)

let rschc (i:intS) =
  forall (ps:progS i).
    forall ct. exists cs.
      behT (linkT (compile_prog ps) ct) `behT_in_behS` behS (linkS ps cs) 

let r2rtc (i:intS) =
  forall (ps1 ps2:progS i) ct lt1 r1 lt2 r2.
    behT (linkT (compile_prog ps1) ct) (lt1,r1) /\ behT (linkT (compile_prog ps2) ct) (lt2,r2) ==>
      (exists cs rs1 rs2. rel_bools rs1 r1 /\ rel_bools rs2 r2 /\
                         (behS (linkS ps2 cs) lt1 rs1) /\ (behS (linkS ps2 cs) lt2 rs2))

(** Variants that use backtranslation and imply the original criteria **)
let rrhp_1 (i:intS) =
  forall (ps:progS i).
    forall ct. behS (linkS ps (backtranslate_ctx ct)) `rel_behs` behT (linkT (compile_prog ps) ct)

let rrhp_1_implies_rrhp (i:intS) :
  Lemma (requires rrhp_1 i)
        (ensures rrhp i) =
  introduce forall ct. 
    exists cs. forall (ps:progS i). behS (linkS ps cs) `rel_behs` behT (linkT (compile_prog ps) ct)
  with begin
    introduce exists cs. forall (ps:progS i). behS (linkS ps cs) `rel_behs` behT (linkT (compile_prog ps) ct)
    with (backtranslate_ctx ct) and ()
  end

let rschc_1 (i:intS) =
  forall (ps:progS i).
    forall ct.
      behT (linkT (compile_prog ps) ct) `behT_in_behS` behS (linkS ps (backtranslate_ctx ct)) 

let rschc_1_implies_rschs (i:intS) :
  Lemma (requires rschc_1 i)
        (ensures rschc i) = 
  introduce forall (ps:progS i) ct. exists cs. behT (linkT (compile_prog ps) ct) `behT_in_behS` behS (linkS ps cs) with
    introduce exists cs. behT (linkT (compile_prog ps) ct) `behT_in_behS` behS (linkS ps cs)
    with (backtranslate_ctx ct) and ()

let r2rtc_1 (i:intS) =
  forall (ps1 ps2:progS i) ct lt1 r1 lt2 r2.
    behT (linkT (compile_prog ps1) ct) (lt1,r1) /\ behT (linkT (compile_prog ps2) ct) (lt2,r2) ==>
      (exists rs1 rs2. rel_bools rs1 r1 /\ rel_bools rs2 r2 /\
                         (behS (linkS ps2 (backtranslate_ctx ct)) lt1 rs1) /\ (behS (linkS ps2 (backtranslate_ctx ct)) lt2 rs2))
                      
let r2rtc_1_implies_r2rtc (i:intS) :
  Lemma (requires r2rtc_1 i)
        (ensures r2rtc_1 i) =
  introduce forall (ps1 ps2:progS i) ct lt1 r1 lt2 r2.
    behT (linkT (compile_prog ps1) ct) (lt1,r1) /\ behT (linkT (compile_prog ps2) ct) (lt2,r2) ==>
      (exists cs rs1 rs2. rel_bools rs1 r1 /\ rel_bools rs2 r2 /\
                         (behS (linkS ps2 cs) lt1 rs1) /\ (behS (linkS ps2 cs) lt2 rs2))
  with
    introduce _ ==> _ with _.
      introduce exists cs. exists rs1 rs2. rel_bools rs1 r1 /\ rel_bools rs2 r2 /\
                         (behS (linkS ps2 cs) lt1 rs1) /\ (behS (linkS ps2 cs) lt2 rs2)
      with (backtranslate_ctx ct) and ()


let lem_app_eq_subst_beta #i (pt:progT (comp_int i)) (ct:closed_exp)
  : Lemma 
      (requires ELam? pt /\ is_value ct)
      (ensures forall lt r. behT (EApp pt ct) (lt, r) <==> behT (subst_beta ct (ELam?.b pt)) (lt, r)) = 
  let h0 : history = [] in
  let b = ELam?.b pt in
  let sb = subst_beta ct b in
  lem_value_is_irred (ELam b);
  lem_value_is_irred ct;
  (* Establish the Beta step *)
  let _beta = FStar.Squash.return_squash (Beta b ct h0) in
  (* Backward: steps sb r [] lt ==> steps (EApp (ELam b) ct) r [] lt *)
  introduce forall (r:closed_exp) (lt:local_trace h0).
    steps sb r h0 lt ==> steps (EApp (ELam b) ct) r h0 lt
  with begin
    introduce _ ==> _ with _. begin
      lem_step_implies_steps (EApp (ELam b) ct) sb h0 None;
      lem_steps_transitive (EApp (ELam b) ct) sb r h0 ([] <: local_trace h0) lt
    end
  end;
  (* Forward: steps (EApp (ELam b) ct) r [] lt /\ indexed_irred r ([]++lt)
              ==> steps sb r [] lt
     Case analysis: SRefl is impossible (Beta fires), STrans must start with Beta
     (AppRight/AppLeft impossible since ct and ELam b are values/irred) *)
  introduce forall (r:closed_exp) (lt:local_trace h0).
    (steps (EApp (ELam b) ct) r h0 lt /\ indexed_irred r (h0++lt)) ==>
    steps sb r h0 lt
  with begin
    introduce _ ==> _ with _. begin
      FStar.Squash.bind_squash
        #(steps (EApp (ELam b) ct) r h0 lt)
        #(steps sb r h0 lt)
        ()
        (fun (st : steps (EApp (ELam b) ct) r h0 lt) ->
          match st with
          | SRefl _ _ -> false_elim ()
          | STrans step1 rest ->
            (match step1 with
            | Beta _ _ _ -> FStar.Squash.return_squash rest
            | AppRight _ hst -> false_elim ()
            | AppLeft _ hst -> false_elim ()))
    end
  end;
  (* Pointwise equivalence of behT: follows from steps equivalence *)
  introduce forall (lt:local_trace h0) (r:closed_exp).
    behT (EApp pt ct) (lt, r) <==> behT sb (lt, r)
  with ()
  
let proof_rschc_1 i : Lemma (rschc_1 i) =
  introduce forall pS cT. behT (linkT (compile_prog pS) cT) `behT_in_behS` behS (linkS pS (backtranslate_ctx cT)) with begin
    let t : qType = i.ct in
    let ps = dfst pS in
    let qps = dsnd pS in
    let pt : progT (comp_int i) = compile_prog pS in
    assert (pt == compile qps);
    let cs = backtranslate_ctx cT in
    let (| ct, tyj |) = cT in
    let ws : wholeS = ps cs in
    lem_compile_closed_arrow_is_elam qps;
    assert (ELam? pt /\ is_closed pt);
    let wt : wholeT = subst_beta ct (ELam?.b pt) in

    eliminate True /\ True
    returns valid_superset_prod ws (subst_beta ct (ELam?.b pt)) with _ _. begin
      lem_compile_closed_valid qps;
      assert (valid_contains ps pt);
      Classical.forall_intro (Classical.move_requires (unfold_contains_io_arrow t qBool ps (ELam?.b pt))); (** unfold ∋ **)
      assert (forall h (v:value) (fs_v:get_Type t) (lt_v:local_trace h). t ∋ (h++lt_v, fs_v, v) ==>
                qBool ⫄ (h++lt_v, ps fs_v, subst_beta v (ELam?.b pt)));
        (** eliminate v fs_v with ct cs **)
      assert (forall h (lt_v:local_trace h). t ∋ (h++lt_v, cs, ct) ==>
                qBool ⫄ (h++lt_v, ps cs, subst_beta ct (ELam?.b pt)));
      introduce forall h. t ∋ (h, cs, ct) ==> qBool ⫄ (h, ps cs, subst_beta ct (ELam?.b pt)) with begin
        eliminate forall h (lt_v:local_trace h). t ∋ (h++lt_v, cs, ct) ==> qBool ⫄ (h++lt_v, ps cs, subst_beta ct (ELam?.b pt))
        with h []
      end;
      lem_backtranslate (dsnd cT);
      assert (valid_superset_prod (ps cs) (subst_beta ct (ELam?.b pt)))
    end;
    lem_rel_behTS ws (subst_beta ct (ELam?.b pt));
    lem_app_eq_subst_beta pt ct;
    ()
  end

let proof_r2rtc_1 i : Lemma (r2rtc_1 i) =
  admit ()

let proof_rrhp_1 i : Lemma (rrhp_1 i) =
  introduce forall pS cT. behS (linkS pS (backtranslate_ctx cT)) `rel_behs` behT (linkT (compile_prog pS) cT) with begin
    let t : qType = i.ct in
    let ps = dfst pS in
    let qps = dsnd pS in
    let pt : progT (comp_int i) = compile_prog pS in
    assert (pt == compile qps);
    let cs = backtranslate_ctx cT in
    let (| ct, tyj |) = cT in
    let ws : wholeS = ps cs in
    lem_compile_closed_arrow_is_elam qps;
    assert (ELam? pt /\ is_closed pt);
    let wt : wholeT = subst_beta ct (ELam?.b pt) in

    eliminate True /\ True
    returns valid_superset_prod ws (subst_beta ct (ELam?.b pt)) with _ _. begin
      lem_compile_closed_valid qps;
      assert (valid_contains ps pt);
      Classical.forall_intro (Classical.move_requires (unfold_contains_io_arrow t qBool ps (ELam?.b pt))); (** unfold ∋ **)
      assert (forall h (v:value) (fs_v:get_Type t) (lt_v:local_trace h). t ∋ (h++lt_v, fs_v, v) ==>
                qBool ⫄ (h++lt_v, ps fs_v, subst_beta v (ELam?.b pt)));
        (** eliminate v fs_v with ct cs **)
      assert (forall h (lt_v:local_trace h). t ∋ (h++lt_v, cs, ct) ==>
                qBool ⫄ (h++lt_v, ps cs, subst_beta ct (ELam?.b pt)));
      introduce forall h. t ∋ (h, cs, ct) ==> qBool ⫄ (h, ps cs, subst_beta ct (ELam?.b pt)) with begin
        eliminate forall h (lt_v:local_trace h). t ∋ (h++lt_v, cs, ct) ==> qBool ⫄ (h++lt_v, ps cs, subst_beta ct (ELam?.b pt))
        with h []
      end;
      lem_backtranslate (dsnd cT);
      assert (valid_superset_prod (ps cs) (subst_beta ct (ELam?.b pt)))
    end;
    eliminate True /\ True
    returns valid_subset_prod ws (subst_beta ct (ELam?.b pt)) with _ _. begin
      lem_compile_closed_valid qps;
      assert (valid_member_of ps pt);
      Classical.forall_intro (Classical.move_requires (unfold_member_of_io_arrow t qBool ps (ELam?.b pt))); (** unfold ∈ **)
      assert (forall h (v:value) (fs_v:get_Type t) (lt_v:local_trace h). t ∈ (h++lt_v, fs_v, v) ==>
                qBool ⫃ (h++lt_v, ps fs_v, subst_beta v (ELam?.b pt)));
      (** eliminate v fs_v with ct cs **)
      assert (forall h (lt_v:local_trace h). t ∈ (h++lt_v, cs, ct) ==>
                qBool ⫃ (h++lt_v, ps cs, subst_beta ct (ELam?.b pt)));
      introduce forall h. t ∈ (h, cs, ct) ==> qBool ⫃ (h, ps cs, subst_beta ct (ELam?.b pt)) with begin
        eliminate forall h (lt_v:local_trace h). t ∈ (h++lt_v, cs, ct) ==> qBool ⫃ (h++lt_v, ps cs, subst_beta ct (ELam?.b pt))
        with h []
      end;
      lem_backtranslate (dsnd cT);
      assert (valid_subset_prod (ps cs) (subst_beta ct (ELam?.b pt)))
    end;
    lem_rel_beh ws (subst_beta ct (ELam?.b pt));
    lem_app_eq_subst_beta pt ct;
    ()
  end
