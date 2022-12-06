module Compiler.Model

open FStar.Ghost
open FStar.Tactics
open FStar.Tactics.Typeclasses
open FStar.FunctionalExtensionality

open BeyondCriteria

open IO.Sig
  
open Compiler.Languages
open Compile.IIO.To.ILang

type typ_io_cmds (fl:erased tflag) (pi:monitorable_prop) =
  (cmd : io_cmds) ->
  (arg : io_sig.args cmd) ->
  IIO (io_resm cmd arg) fl
    (requires (fun _ -> True))
    (ensures (fun h r lt ->
      enforced_locally pi h lt /\
      (match r with
       | Inr Contract_failure -> lt == []
       | r' -> lt == [convert_call_to_event cmd arg r'])))

val inst_io_cmds : pi:monitorable_prop -> typ_io_cmds AllActions pi
let inst_io_cmds pi cmd arg = 
  let h = get_trace () in
  if pi cmd arg h then (
    assume (io_pre cmd arg h);
    static_cmd cmd arg)
  else Inr Contract_failure

val convert_insts : (inst_pi:monitorable_prop) -> (spec_pi:monitorable_prop) -> (_:squash (forall h lt. enforced_locally inst_pi h lt ==> enforced_locally spec_pi h lt)) ->
  (cmd_call:typ_io_cmds AllActions inst_pi) -> (typ_io_cmds AllActions spec_pi) 
let convert_insts inst_pi spec_pi c1 cmd_call (cmd:io_cmds) arg = 
  cmd_call cmd arg

(** **** interfaces **)
noeq
type src_interface = {
  ct : erased tflag -> Type;
  pt : erased tflag -> Type;

  ct_rcs : tree pck_rc;
  //pt_rc : tree pck_rc;

  spec_pi : monitorable_prop;
  inst_pi : monitorable_prop;
  inst_pi_stronger_spec_pi : squash (forall h lt. enforced_locally inst_pi h lt ==> enforced_locally spec_pi h lt);

  //pt_exportable : exportable pt inst_pi pt_rc AllActions;
  ct_importable : fl:erased tflag -> safe_importable (ct fl) spec_pi ct_rcs fl;
}

noeq
type tgt_interface = {
  ct : erased tflag -> Type u#a;
  pt : Type u#b;

  spec_pi : monitorable_prop;
  inst_pi : monitorable_prop;
  inst_pi_stronger_spec_pi : squash (forall h lt. enforced_locally inst_pi h lt ==> enforced_locally spec_pi h lt);
  
  //pt_ilang : ilang pt inst_pi;
  ct_ilang : fl:erased tflag -> ilang (ct fl) spec_pi;
}
  
(** **** languages **)

assume val traces_of : #a:Type -> a ^-> trace_property #IO.Sig.event

type ctx_src (i:src_interface)  = #fl:erased tflag -> typ_io_cmds fl i.inst_pi -> typ_eff_rcs fl i.ct_rcs -> i.ct fl
type prog_src (i:src_interface) = #fl:erased tflag -> i.ct (IOActions + fl) -> i.pt (IOActions + fl)

let src_language : language = {
  interface = src_interface;

  ctx = ctx_src;
  pprog = prog_src;
  whole = (i:src_interface & i.pt AllActions);

  link = (fun #i p c -> 
    (| i, p #AllActions (c #AllActions (inst_io_cmds i.inst_pi) (make_rcs_eff i.ct_rcs)) |));
  event_typ = IO.Sig.event;

  beh = (on_domain _ (fun (| i, w |) -> traces_of w)); 
}

type ctx_tgt (i:tgt_interface) = #fl:erased tflag -> typ_io_cmds fl i.inst_pi -> i.ct fl
type prog_tgt (i:tgt_interface) = i.ct AllActions -> i.pt

let tgt_language : language = {
  interface = tgt_interface;

  ctx = ctx_tgt;
  pprog = prog_tgt;
  whole = (i:tgt_interface & i.pt);

  link = (fun #i p c -> (| i, p (c #AllActions (inst_io_cmds i.inst_pi)) |));
  event_typ = IO.Sig.event;

  beh = (on_domain  (i:tgt_interface & i.pt) (fun (| i, w |) -> traces_of w)); 
}

(** ** Compile interfaces **)
let comp_int_src_tgt (i:src_interface) : tgt_interface = {
 // pt = resexn i.pt_exportable.etype;
  ct = (fun fl -> (i.ct_importable fl).sitype);
  pt = i.pt AllActions;
  spec_pi = i.spec_pi;
  inst_pi = i.inst_pi;
  inst_pi_stronger_spec_pi = i.inst_pi_stronger_spec_pi;

//  pt_ilang = ilang_resexn i.inst_pi i.pt_exportable.etype #i.pt_exportable.c_etype;
  ct_ilang = (fun fl -> (i.ct_importable fl).c_sitype);
}


(** ** Compilation **)
val backtranslate_ctx : (#i:src_interface) -> (c_t:ctx_tgt (comp_int_src_tgt i)) -> src_language.ctx i
let backtranslate_ctx #i c_t #fl acts eff_rcs =
  (i.ct_importable fl).safe_import (c_t #fl acts) eff_rcs
  
val compiler_pprog : (#i:src_interface) -> (p_s:prog_src i) -> tgt_language.pprog (comp_int_src_tgt i)
let compiler_pprog #i p_s c_t = 
  let eff_rcs = make_rcs_eff i.ct_rcs in
  let c_s : i.ct AllActions = (i.ct_importable AllActions).safe_import c_t eff_rcs in
  let p : i.pt AllActions = p_s #AllActions c_s in
  // let eff_rc = make_all_rc_eff i.pt_rc in
  // (i.pt_exportable.export eff_rc p)
  p

let comp : compiler = {
  source = src_language;
  target = tgt_language;

  comp_int = comp_int_src_tgt;

  compile_pprog = compiler_pprog;

  rel_traces = (==);
}

(** ** RrHC **)
let comp_rrhc_2 (i:src_interface) (ct:ctx_tgt (comp_int_src_tgt i)) (ps:prog_src i) : Lemma (
  let cs : ctx_src i = backtranslate_ctx #i ct in
  let it = comp_int_src_tgt i in
  let pt : prog_tgt it = (compiler_pprog #i ps) in
  traces_of (ps #AllActions (cs #AllActions (inst_io_cmds i.inst_pi) (make_rcs_eff i.ct_rcs))) ==
  traces_of (pt (ct #AllActions (inst_io_cmds it.inst_pi)))) = ()

let comp_rrhc_1 (i:comp.source.interface) (ct:comp.target.ctx (comp.comp_int i)) (ps:comp.source.pprog i) : Lemma (
  let cs : comp.source.ctx i = backtranslate_ctx #i ct in
  comp.source.beh (ps `comp.source.link #i` cs) `comp.rel_traces` comp.target.beh (comp.compile_pprog #i ps `comp.target.link #(comp.comp_int i)` ct)) =
  comp_rrhc_2 i ct ps
  
let comp_rrhc_0 (i:comp.source.interface) (ct:comp.target.ctx (comp.comp_int i)) : Lemma (
      exists (cs:comp.source.ctx i).
        forall (ps:comp.source.pprog i).
          comp.source.beh (ps `comp.source.link #i` cs) `comp.rel_traces` comp.target.beh (comp.compile_pprog #i ps `comp.target.link #(comp.comp_int i)` ct)) = 
 introduce exists (cs:comp.source.ctx i).
        (forall (ps:comp.source.pprog i).
          comp.source.beh (ps `comp.source.link #i` cs) `comp.rel_traces` comp.target.beh (comp.compile_pprog #i ps `comp.target.link #(comp.comp_int i)` ct)) 
  with (backtranslate_ctx #i ct)
  and Classical.forall_intro (comp_rrhc_1 i ct)
          
val comp_rrhc : unit -> Lemma (rrhc comp)
let comp_rrhc () : Lemma (rrhc comp) by (norm [delta_only [`%rrhc]]) = 
  Classical.forall_intro_2 (comp_rrhc_0)
