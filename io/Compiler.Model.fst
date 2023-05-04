module Compiler.Model

open FStar.Ghost
open FStar.Tactics
open FStar.Tactics.Typeclasses
open FStar.FunctionalExtensionality

open BeyondCriteria

include Compiler.Languages
include Compiler.MIO.To.Weak
open MIO.Behavior

type policy (mst:mst) (pi:policy_spec) =
  s:mst.cst -> cmd:io_cmds -> arg:io_sig.args cmd -> r:bool{r ==> (forall h. mst.models s h ==> pi h false cmd arg)}

type acts (mst:mst) (fl:erased tflag) (pi:policy_spec) (caller:bool) =
  (cmd : io_cmds) ->
  (arg : io_sig.args cmd) ->
  MIO (io_resm cmd arg) mst fl
    (requires (fun _ -> True))
    (ensures (fun h r lt ->
      enforced_locally pi h lt /\
      (match r with
       | Inr Contract_failure -> lt == []
       | r' -> lt == [convert_call_to_event caller cmd arg r'])))

type acts' (mst:mst) (fl:erased tflag) (#pi:policy_spec) (phi:policy mst pi) (caller:bool) =
  (cmd : io_cmds) ->
  (arg : io_sig.args cmd) ->
  MIO (io_resm cmd arg) mst fl
    (requires (fun _ -> True))
    (ensures (fun h r lt ->
      enforced_locally pi h lt /\
      //enforced_locally (fun h _ cmd arg -> phi h cmd arg) h lt /\
      // ^ really needed?
      (match r with
       | Inr Contract_failure -> lt == []
       | r' -> lt == [convert_call_to_event caller cmd arg r'])))

val inst_io_cmds : #mst:mst -> #pi:policy_spec -> phi:policy mst pi -> acts' mst AllActions phi false

#push-options "--compat_pre_core 1"
let inst_io_cmds phi cmd arg = 
  let h = get_state true in
  if phi h cmd arg then (
    // Need the letbinding here it won't typecheck... why?
    let r : io_resm' cmd arg = static_cmd false cmd arg in
    r
  ) else Inr Contract_failure
#pop-options

(** **** interfaces **)
noeq
type src_interface (mst:mst) = {
  (* pi is in Type0 and it is used at the level of the spec,
     it describes both the events done by the partial program and the context **)
  pi : policy_spec;
  (* phi is in bool and it is used to enforce the policy on the context,
     it describes only the events of the context and it has to imply pi **)
  phi : policy mst pi;

  (** The type of the "context" --- not sure if it is the best name.
      It is more like the type of the interface which the two share to communicate. **)
  ct : erased tflag -> Type;
  ct_rcs : tree (pck_rc mst);
  ct_importable : fl:erased tflag -> safe_importable (ct fl) mst pi ct_rcs fl;

  (** The partial program can have a post-condition that becomes the
      post-condition of the whole program after linking in the source.
      This post-condition is erased during compilation **)
  psi : trace -> int -> trace -> Type0;
}

noeq
type tgt_interface (mst:mst) = {
  pi : policy_spec;
  phi : policy mst pi;

  ct : erased tflag -> Type u#a;
  ct_weak : fl:erased tflag -> weak (ct fl) mst fl pi;
}
  
(** **** languages **)
type ctx_src mst (i:src_interface mst)  = #fl:erased tflag -> acts' mst fl i.phi false -> typ_eff_rcs mst fl i.ct_rcs -> i.ct fl
type prog_src mst (i:src_interface mst) = #fl:erased tflag -> i.ct (IOActions + fl) -> unit -> MIO int mst (IOActions + fl) (fun _ -> True) i.psi
type whole_src = mst:mst & post:(trace -> int -> trace -> Type0) & (unit -> MIO int mst AllActions (fun _ -> True) post)

let link_src #mst (#i:src_interface mst) (p:prog_src mst i) (c:ctx_src mst i) : whole_src = 
  (| mst, i.psi, p #AllActions (c #AllActions (inst_io_cmds i.phi) (make_rcs_eff i.ct_rcs)) |)

val beh_src : whole_src ^-> trace_property #event
let beh_src = on_domain whole_src (fun (| mst, _, ws |) -> beh mst ws)

let src_language (mst:mst) : language = {
  interface = src_interface mst;
  ctx = ctx_src mst; pprog = prog_src mst; whole = whole_src;
  link = link_src;
  event_typ = event;  beh = beh_src; 
}

type ctx_tgt mst (i:tgt_interface mst) = #fl:erased tflag -> acts mst fl i.pi false -> i.ct fl
type prog_tgt mst (i:tgt_interface mst) = i.ct AllActions -> unit -> MIO int mst AllActions (fun _ -> True) (fun _ _ _ -> True)
type whole_tgt mst = unit -> MIO int mst AllActions (fun _ -> True) (fun _ _ _ -> True)

let link_tgt #mst (#i:tgt_interface mst) (p:prog_tgt mst i) (c:ctx_tgt mst i) : whole_tgt mst =
  p (c #AllActions (inst_io_cmds i.phi))

val beh_tgt : #mst:mst -> whole_tgt mst ^-> trace_property #event
let beh_tgt #mst = beh mst

let tgt_language (mst:mst) : language = {
  interface = tgt_interface mst;
  ctx = ctx_tgt mst; pprog = prog_tgt mst; whole = whole_tgt mst;
  link = link_tgt;
  event_typ = event; beh = beh_tgt; 
}

(** ** Compile interfaces **)
let comp_int_src_tgt mst (i:src_interface mst) : tgt_interface mst = {
  ct = (fun fl -> (i.ct_importable fl).swtyp);
  ct_weak = (fun fl -> (i.ct_importable fl).c_swtyp);

  pi = i.pi;
  phi = i.phi;
}

(** ** Compilation **)
val backtranslate_ctx : #mst:mst -> (#i:src_interface mst) -> (c_t:ctx_tgt mst (comp_int_src_tgt mst i)) -> (src_language mst).ctx i
let backtranslate_ctx #mst #i c_t #fl acts eff_rcs =
  (i.ct_importable fl).safe_import (c_t #fl acts) eff_rcs

val compile_whole : s:whole_src -> whole_tgt s._1
let compile_whole (| _, _, ws |) = ws

val compile_pprog : #mst:mst -> (#i:src_interface mst) -> (p_s:prog_src mst i) -> prog_tgt mst (comp_int_src_tgt mst i)
let compile_pprog #mst #i p_s c_t = 
  let eff_rcs = make_rcs_eff i.ct_rcs in
  let c_s : i.ct AllActions = (i.ct_importable AllActions).safe_import c_t eff_rcs in
  let ws : whole_src = (| mst, i.psi, p_s #AllActions c_s |) in
  let wt : whole_tgt mst = compile_whole ws in
  wt

val compile_ctx : #mst:mst -> (#i:src_interface mst) -> (c_s:ctx_src mst i) -> ctx_tgt mst (comp_int_src_tgt mst i)
let compile_ctx #mst #i c_s = 
  (** TODO: the context should be also exportable besides importable,
      which would be a pain because one has to define a second tree of rcs. **)

  (** The point of defining C↓ is to prove SCC (from Beyond Full Abstraction). 
      Since, C↓ = export C, and P↓ = fun c -> P (import c),
      then C↓[P↓] = P↓ (C↓) = P↓ (export C) = P (import (export C)) = P C.
      The last step is true if we can prove that `import (export f) = f`, see
      LawImportableExportable.fst **)
  admit ()

let comp (mst:mst) : compiler = {
  source = src_language mst;
  target = tgt_language mst;

  comp_int = comp_int_src_tgt mst;

  compile_pprog = compile_pprog;

  rel_traces = (==);
}

(** ** Soundness **)
let soundness (mst:mst) (i:src_interface mst) (ct:ctx_tgt mst (comp_int_src_tgt mst i)) (ps:prog_src mst i) : Lemma (
  let it = comp_int_src_tgt mst i in
  let cs : ctx_src mst i = backtranslate_ctx #mst #i ct in
  let pt : prog_tgt mst it = (compile_pprog #mst #i ps) in
  let wt : whole_tgt mst = (pt `link_tgt` ct) in
  let ws : whole_src = (ps `link_src` cs) in
  (tgt_language mst).beh (wt) `subset_of` (src_language mst).beh (ws) 
) = ()

(** ** RrHC **)
let syntactic_equality (mst:mst) (i:src_interface mst) (ct:ctx_tgt mst (comp_int_src_tgt mst i)) (ps:prog_src mst i) : Lemma (
  let it = comp_int_src_tgt mst i in
  let cs : ctx_src mst i = backtranslate_ctx #mst #i ct in
  let pt : prog_tgt mst it = (compile_pprog #mst #i ps) in
  let wt : whole_tgt mst = (pt `link_tgt` ct) in
  let ws : whole_src = (ps `link_src` cs) in
  compile_whole ws == wt
) = ()
  
let comp_rrhc_2 (mst:mst) (i:src_interface mst) (ct:ctx_tgt mst (comp_int_src_tgt mst i)) (ps:prog_src mst i) : Lemma (
  let it = comp_int_src_tgt mst i in
  let cs : ctx_src mst i = backtranslate_ctx #mst #i ct in
  let pt : prog_tgt mst it = (compile_pprog #mst #i ps) in
  let wt : whole_tgt mst = (pt `link_tgt` ct) in
  let ws : whole_src = (ps `link_src` cs) in
  beh_src ws == beh_tgt wt) = 
  syntactic_equality mst i ct ps

let comp_rrhc_1 (mst:mst) (i:(comp mst).source.interface) (ct:(comp mst).target.ctx ((comp mst).comp_int i)) (ps:(comp mst).source.pprog i) : Lemma (
  let cs : (comp mst).source.ctx i = backtranslate_ctx #mst #i ct in
  (comp mst).source.beh (ps `(comp mst).source.link #i` cs) `(comp mst).rel_traces` (comp mst).target.beh ((comp mst).compile_pprog #i ps `(comp mst).target.link #((comp mst).comp_int i)` ct)) =
  comp_rrhc_2 mst i ct ps
  
let comp_rrhc_0 (mst:mst) (i:(comp mst).source.interface) (ct:(comp mst).target.ctx ((comp mst).comp_int i)) : Lemma (
      exists (cs:(comp mst).source.ctx i).
        forall (ps:(comp mst).source.pprog i).
          (comp mst).source.beh (ps `(comp mst).source.link #i` cs) `(comp mst).rel_traces` (comp mst).target.beh ((comp mst).compile_pprog #i ps `(comp mst).target.link #((comp mst).comp_int i)` ct)) = 
 introduce exists (cs:(comp mst).source.ctx i).
        (forall (ps:(comp mst).source.pprog i).
          (comp mst).source.beh (ps `(comp mst).source.link #i` cs) `(comp mst).rel_traces` (comp mst).target.beh ((comp mst).compile_pprog #i ps `(comp mst).target.link #((comp mst).comp_int i)` ct)) 
  with (backtranslate_ctx #mst #i ct)
  and Classical.forall_intro (comp_rrhc_1 mst i ct)
          
val comp_rrhc : mst:mst -> Lemma (rrhc (comp mst))
let comp_rrhc mst : Lemma (rrhc (comp mst)) by (norm [delta_only [`%rrhc]]) = 
  Classical.forall_intro_2 (comp_rrhc_0 mst)
