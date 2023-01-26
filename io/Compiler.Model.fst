module Compiler.Model

open FStar.Ghost
open FStar.Tactics
open FStar.Tactics.Typeclasses
open FStar.FunctionalExtensionality

open BeyondCriteria

open Compiler.Languages
open Compiler.IIO.To.TLang
open IIO.Behavior

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
  (** The interface contains two pi's: spec_pi and inst_pi. 
      inst_pi is the pi used to instrument the context.
      One usually wants to instrument the context with a strong pi,
      but that is not necessary the spec wanted for the context since
      one can not write a precise pi. One
      could limit the direct access of the context to the IO actions 
      using inst_pi, but still want the context to have a more 
      relaxed indirect access to IO actions. 
      For example calling a statically verified callback, 
      then the callback also has to respect the strong pi (otherwise 
      the context can not call it). We found
      that having a weaker second pi (spec_pi) used only at the
      spec level, works well and solves the problem.
      spec_pi is weaker than inst_pi and it represents the spec 
      one obtains in the target language. **)
  spec_pi : monitorable_prop;
  inst_pi : monitorable_prop;
  inst_pi_stronger_spec_pi : squash (forall h lt. enforced_locally inst_pi h lt ==> enforced_locally spec_pi h lt);

  (** The type of the "context" --- not sure if it is the best name.
      It is more like the type of the interface which the two share to communicate. **)
  ct : erased tflag -> Type;
  ct_rcs : tree pck_rc;
  ct_importable : fl:erased tflag -> safe_importable (ct fl) spec_pi ct_rcs fl;

  (** The partial program can have a post-condition that becomes the
      post-condition of the whole program after linking in the source.
      This post-condition is erased during compilation **)
  p_post : trace -> int -> trace -> Type0;
}

noeq
type tgt_interface = {
  spec_pi : monitorable_prop;

  ct : erased tflag -> monitorable_prop -> Type u#a;
  ct_tlang : fl:erased tflag -> tlang (ct fl spec_pi) spec_pi;

  inst_pi : monitorable_prop;
  inst_pi_stronger_spec_pi : squash (forall h lt. enforced_locally inst_pi h lt ==> enforced_locally spec_pi h lt);
}
  
(** **** languages **)
type ctx_src (i:src_interface)  = #fl:erased tflag -> typ_io_cmds fl i.inst_pi -> typ_eff_rcs fl i.ct_rcs -> i.ct fl
type prog_src (i:src_interface) = #fl:erased tflag -> i.ct (IOActions + fl) -> unit -> IIO int (IOActions + fl) (fun _ -> True) i.p_post
type whole_src = post:(trace -> int -> trace -> Type0) & (unit -> IIO int AllActions (fun _ -> True) post)

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

type ctx_tgt (i:tgt_interface) = #fl:erased tflag -> #pi:erased monitorable_prop -> typ_io_cmds fl pi -> i.ct fl pi
type prog_tgt (i:tgt_interface) = i.ct AllActions i.spec_pi -> unit -> IIO int AllActions (fun _ -> True) (fun _ _ _ -> True)
type whole_tgt = unit -> IIO int AllActions (fun _ -> True) (fun _ _ _ -> True)

let link_tgt (#i:tgt_interface) (p:prog_tgt i) (c:ctx_tgt i) : whole_tgt =
  p (c #AllActions #i.spec_pi (inst_io_cmds i.inst_pi))

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
  ct = (fun fl pi -> (i.ct_importable fl).sitype);
  ct_tlang = (fun fl -> (i.ct_importable fl).c_sitype);

  spec_pi = i.spec_pi;
  inst_pi = i.inst_pi;
  inst_pi_stronger_spec_pi = i.inst_pi_stronger_spec_pi;
}

(** ** Compilation **)
val backtranslate_ctx : (#i:src_interface) -> (c_t:ctx_tgt (comp_int_src_tgt i)) -> src_language.ctx i
let backtranslate_ctx #i c_t #fl acts eff_rcs =
  (i.ct_importable fl).safe_import (c_t #fl #i.spec_pi acts) eff_rcs

val compile_whole : whole_src -> whole_tgt
let compile_whole (| _, ws |) = ws

val compile_pprog : (#i:src_interface) -> (p_s:prog_src i) -> prog_tgt (comp_int_src_tgt i)
let compile_pprog #i p_s c_t = 
  let eff_rcs = make_rcs_eff i.ct_rcs in
  let c_s : i.ct AllActions = (i.ct_importable AllActions).safe_import c_t eff_rcs in
  let ws : whole_src = (| i.p_post, p_s #AllActions c_s |) in
  let wt : whole_tgt = compile_whole ws in
  wt

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
