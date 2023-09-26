module Compiler.Model1

open FStar.Ghost
open FStar.Tactics
open FStar.Tactics.Typeclasses
open FStar.FunctionalExtensionality

open BeyondCriteria

include Compiler.Languages
include Compiler.MIO.To.Interm
open MIO.Behavior

(** **** interfaces **)
noeq
type src_interface = {
  mst : mst;
  (* sgm is in Type0 and it is used at the level of the spec,
     it describes both the events done by the partial program and the context **)
  sgm : policy_spec;
  (* pi is in bool and it is used to enfodce the policy on the context,
     it describes only the events of the context and it has to imply sgm **)
  pi : policy mst sgm;

  (** The type of the "context" --- not sure if it is the best name.
      It is more like the type of the interface which the two share to communicate. **)
  ct : erased tflag -> Type;
  ct_dcs : tree (pck_dc mst);
  ct_importable : fl:erased tflag -> safe_importable (ct fl) fl sgm mst ct_dcs;

  (** The partial program can have a post-condition that becomes the
      post-condition of the whole program after linking in the source.
      This post-condition is erased during compilation **)
  psi : trace -> int -> trace -> Type0;
}

noeq
type tgt_interface = {
  mst : mst;
  sgm : policy_spec;
  pi : policy mst sgm;

  ct : erased tflag -> Type u#a;
  ct_weak : fl:erased tflag -> interm (ct fl) fl sgm mst;
}

(** **** languages **)
type ctx_src (i:src_interface)  = #fl:erased tflag -> io_lib fl i.sgm i.mst Ctx -> typ_eff_dcs i.mst fl i.ct_dcs -> i.ct fl
type prog_src (i:src_interface) = #fl:erased tflag -> i.ct (IOActions + fl) -> unit -> MIO int i.mst (IOActions + fl) (fun _ -> True) i.psi
type whole_src = mst:mst & post:(trace -> int -> trace -> Type0) & (unit -> MIO int mst AllActions (fun _ -> True) post)

let link_src (#i:src_interface) (p:prog_src i) (c:ctx_src i) : whole_src =
  (| i.mst, i.psi,  p #AllActions (c #AllActions (inst_io_cmds i.pi) (make_dcs_eff i.ct_dcs)) |)

val beh_src : whole_src ^-> trace_property #event
let beh_src = on_domain whole_src (fun (| mst, _, ws |) -> beh mst ws)

let src_language : language = {
  interface = src_interface;
  ctx = ctx_src; pprog = prog_src; whole = whole_src;
  link = link_src;
  event_typ = event;  beh = beh_src;
}

// TODO: SMT problems with this def in AdversarialHandlers:
//type ctx_tgt (i:tgt_interface) = #fl:erased tflag -> #pi':erased policy_spec -> io_lib fl sgm' i.mst Ctx -> i.ct fl
type ctx_tgt (i:tgt_interface) = #fl:erased tflag -> io_lib fl i.sgm i.mst Ctx -> i.ct fl
type prog_tgt (i:tgt_interface) = i.ct AllActions -> unit -> MIO int i.mst AllActions (fun _ -> True) (fun _ _ _ -> True)
type whole_tgt = mst:mst & (unit -> MIO int mst AllActions (fun _ -> True) (fun _ _ _ -> True))

let link_tgt (#i:tgt_interface) (p:prog_tgt i) (c:ctx_tgt i) : whole_tgt =
  (| i.mst , p (c #AllActions (inst_io_cmds i.pi)) |)

val beh_tgt : whole_tgt ^-> trace_property #event
let beh_tgt = on_domain whole_tgt (fun (| mst, wt |) -> beh mst wt)

let tgt_language : language = {
  interface = tgt_interface;
  ctx = ctx_tgt; pprog = prog_tgt; whole = whole_tgt;
  link = link_tgt;
  event_typ = event; beh = beh_tgt;
}

(** ** Compile interfaces **)
let comp_int_src_tgt (i:src_interface) : tgt_interface = {
  ct = (fun fl -> (i.ct_importable fl).ityp);
  ct_weak = (fun fl -> (i.ct_importable fl).c_ityp);

  mst = i.mst;
  sgm = i.sgm;
  pi = i.pi;
}

(** ** Compilation **)
val backtranslate_ctx : (#i:src_interface) -> (c_t:ctx_tgt (comp_int_src_tgt i)) -> src_language.ctx i
let backtranslate_ctx #i c_t #fl io_lib eff_dcs =
  (i.ct_importable fl).safe_import (c_t #fl io_lib) eff_dcs

val compile_whole : whole_src -> whole_tgt
let compile_whole (| mst, _, ws |) = (| mst, ws |)

val compile_pprog : (#i:src_interface) -> (p_s:prog_src i) -> prog_tgt (comp_int_src_tgt i)
let compile_pprog #i p_s c_t =
  let eff_dcs = make_dcs_eff i.ct_dcs in
  let c_s : i.ct AllActions = (i.ct_importable AllActions).safe_import c_t eff_dcs in
  let ws : whole_src = (| i.mst, i.psi, p_s #AllActions c_s |) in
  let (| _, pt |) : whole_tgt = compile_whole ws in
  pt

// val compile_ctx : (#i:src_interface) -> (c_s:ctx_src i) -> ctx_tgt (comp_int_src_tgt i)
// let compile_ctx #i c_s =
//   (** TODO: the context should be also exportable besides importable,
//       which would be a pain because one has to define a second tree of dcs. **)

//   (** The point of defining C↓ is to prove SCC (from Beyond Full Abstraction).
//       Since, C↓ = export C, and P↓ = fun c -> P (import c),
//       then C↓[P↓] = P↓ (C↓) = P↓ (export C) = P (import (export C)) = P C.
//       The last step is true if we can prove that `import (export f) = f`, see
//       LawImportableExportable.fst **)

let comp : compiler = {
  source = src_language;
  target = tgt_language;

  comp_int = comp_int_src_tgt;

  compile_pprog = compile_pprog;

  rel_traces = (==);
}

(** ** Soundness **)
let soundness (i:src_interface) (ct:ctx_tgt (comp_int_src_tgt i)) (ps:prog_src i) : Lemma (
  let it = comp_int_src_tgt i in
  let cs : ctx_src i = backtranslate_ctx #i ct in
  let pt : prog_tgt it = (compile_pprog #i ps) in
  let wt : whole_tgt = (pt `link_tgt` ct) in
  let ws : whole_src = (ps `link_src` cs) in
  tgt_language.beh (wt) `subset_of` src_language.beh (ws)
) = ()

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
  Classical.forall_intro_2 comp_rrhc_0
