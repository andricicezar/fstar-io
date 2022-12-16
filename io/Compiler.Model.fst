module Compiler.Model

open FStar.Ghost
open FStar.Tactics
open FStar.Tactics.Typeclasses
open FStar.FunctionalExtensionality

open BeyondCriteria

open IIO.Sig
  
open Compiler.Languages
open Compiler.IIO.To.TLang

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
  spec_pi : monitorable_prop;
  ct_rcs : tree pck_rc;
  ct : erased tflag -> Type;
  ct_importable : fl:erased tflag -> safe_importable (ct fl) spec_pi ct_rcs fl;

  inst_pi : monitorable_prop;
  inst_pi_stronger_spec_pi : squash (forall h lt. enforced_locally inst_pi h lt ==> enforced_locally spec_pi h lt);

  p_post : list string -> trace -> int -> trace -> Type0;
}

noeq
type tgt_interface = {
  spec_pi : monitorable_prop;
  ct : erased tflag -> Type u#a;
  ct_tlang : fl:erased tflag -> tlang (ct fl) spec_pi;

  inst_pi : monitorable_prop;
  inst_pi_stronger_spec_pi : squash (forall h lt. enforced_locally inst_pi h lt ==> enforced_locally spec_pi h lt);
}
  
(** **** languages **)
assume val beh : (list string -> IIO int AllActions (fun _ -> True) (fun _ _ _ -> True)) ^-> trace_property #event

type ctx_src (i:src_interface)  = #fl:erased tflag -> typ_io_cmds fl i.inst_pi -> typ_eff_rcs fl i.ct_rcs -> i.ct fl
type prog_src (i:src_interface) = #fl:erased tflag -> i.ct (IOActions + fl) -> argv:list string -> IIO int (IOActions + fl) (fun _ -> True) (i.p_post argv)
type whole_src = post:(list string -> trace -> int -> trace -> Type0) & (argv:list string -> IIO int AllActions (fun _ -> True) (post argv))

let link_src (#i:src_interface) (p:prog_src i) (c:ctx_src i) : whole_src = 
  (| i.p_post, p #AllActions (c #AllActions (inst_io_cmds i.inst_pi) (make_rcs_eff i.ct_rcs)) |)

val beh_src : whole_src ^-> trace_property #event
let beh_src = on_domain whole_src (fun (| _, ws |) -> beh ws)

let src_language : language = {
  interface = src_interface;
  ctx = ctx_src; pprog = prog_src; whole = whole_src;
  link = link_src;
  event_typ = event;  beh = beh_src; 
}

type ctx_tgt (i:tgt_interface) = #fl:erased tflag -> typ_io_cmds fl i.inst_pi -> i.ct fl
type prog_tgt (i:tgt_interface) = i.ct AllActions -> list string -> IIO int AllActions (fun _ -> True) (fun _ _ _ -> True)
type whole_tgt = list string -> IIO int AllActions (fun _ -> True) (fun _ _ _ -> True)

let link_tgt (#i:tgt_interface) (p:prog_tgt i) (c:ctx_tgt i) : whole_tgt =
  p (c #AllActions (inst_io_cmds i.inst_pi))

val beh_tgt : whole_tgt ^-> trace_property #event
let beh_tgt = beh 

let tgt_language : language = {
  interface = tgt_interface;
  ctx = ctx_tgt; pprog = prog_tgt; whole = whole_tgt;
  link = link_tgt;
  event_typ = event; beh = beh_tgt; 
}

(** ** Compile interfaces **)
let comp_int_src_tgt (i:src_interface) : tgt_interface = {
  ct = (fun fl -> (i.ct_importable fl).sitype);

  spec_pi = i.spec_pi;
  inst_pi = i.inst_pi;
  inst_pi_stronger_spec_pi = i.inst_pi_stronger_spec_pi;

  ct_tlang = (fun fl -> (i.ct_importable fl).c_sitype);
}

(** ** Compilation **)
val backtranslate_ctx : (#i:src_interface) -> (c_t:ctx_tgt (comp_int_src_tgt i)) -> src_language.ctx i
let backtranslate_ctx #i c_t #fl acts eff_rcs =
  (i.ct_importable fl).safe_import (c_t #fl acts) eff_rcs

val compile_whole : whole_src -> whole_tgt
let compile_whole (| _, ws |) = ws

val compile_pprog : (#i:src_interface) -> (p_s:prog_src i) -> prog_tgt (comp_int_src_tgt i)
let compile_pprog #i p_s c_t = 
  let eff_rcs = make_rcs_eff i.ct_rcs in
  let c_s : i.ct AllActions = (i.ct_importable AllActions).safe_import c_t eff_rcs in
  p_s #AllActions c_s

let comp : compiler = {
  source = src_language;
  target = tgt_language;

  comp_int = comp_int_src_tgt;

  compile_pprog = compile_pprog;

  rel_traces = (==);
}

(** ** RrHC **)
let syntactic_equality (i:src_interface) (ct:ctx_tgt (comp_int_src_tgt i)) (ps:prog_src i) : Lemma (
  let it = comp_int_src_tgt i in
  let cs : ctx_src i = backtranslate_ctx #i ct in
  let pt : prog_tgt it = (compile_pprog #i ps) in
  let wt : whole_tgt = (pt `link_tgt` ct) in
  let ws : whole_src = (ps `link_src` cs) in
  compile_whole ws == wt
) = ()
  
let comp_rrhc_2 (i:src_interface) (ct:ctx_tgt (comp_int_src_tgt i)) (ps:prog_src i) : Lemma (
  let it = comp_int_src_tgt i in
  let cs : ctx_src i = backtranslate_ctx #i ct in
  let pt : prog_tgt it = (compile_pprog #i ps) in
  let wt : whole_tgt = (pt `link_tgt` ct) in
  let ws : whole_src = (ps `link_src` cs) in
  beh_src ws == beh_tgt wt) = 
  syntactic_equality i ct ps

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
