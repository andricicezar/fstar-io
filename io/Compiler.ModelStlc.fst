module Compiler.ModelStlc

open FStar.Ghost
open FStar.Tactics
open FStar.Tactics.Typeclasses
open FStar.FunctionalExtensionality

open BeyondCriteria

include Compiler.Languages
include Compiler.MIO.To.Interm
open MIO.Behavior

open Compiler.StlcToFStar

let static_cmd
  (#mst:mst)
  caller
  (cmd : io_cmds)
  (arg : io_sig.args cmd) :
  MIO (io_sig.res cmd arg) mst IOActions
    (requires (fun h -> io_pre cmd arg h))
    (ensures (fun h (r:io_sig.res cmd arg) lt ->
        io_post cmd arg r /\
        lt == [convert_call_to_event caller cmd arg r])) =
  MIOwp?.reflect (MIO.Sig.Call.mio_call caller cmd arg)

type io_lib (fl:erased tflag) (pi:policy_spec) (mst:mst) (c:caller) =
  (cmd : io_cmds) ->
  (arg : io_sig.args cmd) ->
  MIO (io_resm cmd arg) mst fl
    (requires (fun _ -> True))
    (ensures (fun h r lt ->
      enforced_locally pi h lt /\
      (match r with
       | Inr Contract_failure -> lt == []
       | r' -> io_post cmd arg r' /\ lt == [convert_call_to_event c cmd arg r'])))

type io_lib' (fl:erased tflag) (#pi:policy_spec) (mst:mst) (phi:policy mst pi) (c:caller) =
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
       | r' -> io_post cmd arg r' /\ lt == [convert_call_to_event c cmd arg r'])))

#push-options "--compat_pre_core 1" // fixme
val inst_io_cmds : #mst:mst -> #pi:policy_spec -> phi:policy mst pi -> io_lib' AllActions mst phi Ctx
let inst_io_cmds phi cmd arg =
  let s0 = get_state () in
  if phi s0 cmd arg then (
    // Need the letbinding here it won't typecheck... why?
    let r : io_resm' cmd arg = static_cmd Ctx cmd arg in
    r
  ) else Inr Contract_failure
#pop-options


let ctx_env =
  extend (TArr TString (TSum TFDesc TExn)) (* openfile *)
 // (extend (TArr TUnit (TSum TFDesc TExn)) (* socket *)
  (extend (TArr (TPair TFDesc TString) (TSum TUnit TExn)) (* write *)
          empty)

#push-options "--compat_pre_core 1"
let bt_ctx (e:exp{ELam? e}) (t:typ) (h:typing ctx_env e t) (#fl:erased tflag) (#pi:policy_spec) (#mst:mst) (sec_io:io_lib fl pi mst Ctx) : (typ_to_fstar t fl pi mst) =
   let write : FStar.Universe.raise_t file_descr * FStar.Universe.raise_t string -> MIOpi (either (FStar.Universe.raise_t unit) (FStar.Universe.raise_t exn)) fl pi _ = fun fdb ->
     let fd = FStar.Universe.downgrade_val (fst fdb) in
     let b = FStar.Universe.downgrade_val (snd fdb) in
     match sec_io Write (fd, b) with
     | Inl unit -> Inl (FStar.Universe.raise_val unit)
     | Inr ex -> Inr (FStar.Universe.raise_val ex) in
   let openfile : FStar.Universe.raise_t string -> MIOpi (either (FStar.Universe.raise_t file_descr) (FStar.Universe.raise_t exn)) fl pi _ = fun s ->
     let s = FStar.Universe.downgrade_val s in
     match sec_io Openfile s with
     | Inl fd -> Inl (FStar.Universe.raise_val fd)
     | Inr ex -> Inr (FStar.Universe.raise_val ex) in
   let ctx_venv = 
     vextend #fl #mst #pi #(TArr TString (TSum TFDesc TExn)) openfile (
     vextend #fl #mst #pi #(TArr (TPair TFDesc TString) (TSum TUnit TExn)) write (
     vempty #fl #pi #mst)) in
   exp_to_fstar' ctx_env e t h ctx_venv
#pop-options


(** **** interfaces **)
noeq
type src_interface = {
  mst : mst;
  (* pi is in Type0 and it is used at the level of the spec,
     it describes both the events done by the partial program and the context **)
  pi : policy_spec;
  (* phi is in bool and it is used to enfodce the policy on the context,
     it describes only the events of the context and it has to imply pi **)
  phi : policy mst pi;

  (** The type of the "context" --- not sure if it is the best name.
      It is more like the type of the interface which the two share to communicate. **)
  ct : erased tflag -> Type;
  ct_dcs : tree (pck_dc mst);
  ct_importable : fl:erased tflag -> safe_importable (ct fl) fl pi mst ct_dcs;


  wct : typ;
  _c : fl:erased tflag -> Lemma ((ct_importable fl).ityp == (typ_to_fstar wct fl pi mst));

  (** The partial program can have a post-condition that becomes the
      post-condition of the whole program after linking in the source.
      This post-condition is erased during compilation **)
  psi : trace -> int -> trace -> Type0;
}

noeq
type tgt_interface = {
  mst : mst;
  pi : policy_spec;
  phi : policy mst pi;

  ct : typ;
}
  
(** **** languages **)
type ctx_src (i:src_interface)  = #fl:erased tflag -> io_lib fl i.pi i.mst Ctx -> typ_eff_dcs i.mst fl i.ct_dcs -> i.ct fl 
type prog_src (i:src_interface) = #fl:erased tflag -> i.ct (fl+IOActions) -> unit -> MIO int i.mst (IOActions + fl) (fun _ -> True) i.psi
type whole_src = mst:mst & post:(trace -> int -> trace -> Type0) & (unit -> MIO int mst AllActions (fun _ -> True) post)

let link_src (#i:src_interface) (p:prog_src i) (c:ctx_src i) : whole_src = 
  (| i.mst, i.psi,  p #AllActions (c #AllActions (inst_io_cmds i.phi) (make_dcs_eff i.ct_dcs)) |)

val beh_src : whole_src ^-> trace_property #event
let beh_src = on_domain whole_src (fun (| mst, _, ws |) -> beh mst ws)

let src_language : language = {
  interface = src_interface;
  ctx = ctx_src; pprog = prog_src; whole = whole_src;
  link = link_src;
  event_typ = event;  beh = beh_src; 
}

type ctx_tgt (i:tgt_interface) = e:exp{ELam? e} & typing ctx_env e i.ct
type prog_tgt (i:tgt_interface) = (typ_to_fstar i.ct AllActions i.pi i.mst) -> unit -> MIO int i.mst AllActions (fun _ -> True) (fun _ _ _ -> True)
type whole_tgt = mst:mst & (unit -> MIO int mst AllActions (fun _ -> True) (fun _ _ _ -> True))

let link_tgt (#i:tgt_interface) (p:prog_tgt i) (c:ctx_tgt i) : whole_tgt =
  let (| e, h |) = c in
  let sec_io = inst_io_cmds i.phi in
  let c' = bt_ctx e i.ct h #AllActions #i.pi #i.mst sec_io in
  (| i.mst , p c' |)

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
  ct = i.wct;

  mst = i.mst;
  pi = i.pi;
  phi = i.phi;
}

(** ** Compilation **)
let convert (i:src_interface) fl (c:(typ_to_fstar i.wct fl i.pi i.mst)) : (i.ct_importable fl).ityp =
  i._c fl;
 c

val backtranslate_ctx : (#i:src_interface) -> (c_t:ctx_tgt (comp_int_src_tgt i)) -> src_language.ctx i
let backtranslate_ctx #i c_t #fl io_lib eff_dcs =
  let (| e, h |) = c_t in
  let c' = bt_ctx e i.wct h #fl #i.pi #i.mst io_lib in
  (i.ct_importable fl).safe_import (convert i fl c') eff_dcs

val compile_whole : whole_src -> whole_tgt
let compile_whole (| mst, _, ws |) = (| mst, ws |)

val compile_pprog : (#i:src_interface) -> (p_s:prog_src i) -> prog_tgt (comp_int_src_tgt i)
let compile_pprog #i p_s c_t = 
  let eff_dcs = make_dcs_eff i.ct_dcs in
  // same assumptions as before
  let c_s = (i.ct_importable AllActions).safe_import (convert i AllActions c_t) eff_dcs in
  let ws : whole_src = (| i.mst, i.psi, p_s #AllActions c_s |) in
  let (| _, pt |) : whole_tgt = compile_whole ws in
  pt

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



(** Instantiate Model

module WS = WebServer

let wct = TArr TFDesc (TArr TBytes (TArr (TArr TBytes (TSum TUnit TExn)) (TSum TUnit TExn)))

let test : src_interface = {
  mst = WS.cs_int.mst;
  pi = WS.cs_int.pi;
  phi = WS.cs_int.phi;
  ct = WS.cs_int.ct;
  ct_dcs = WS.cs_int.ct_dcs;
  ct_importable = (fun fl -> WS.cs_int.ct_importable fl);

  wct = wct; // TODO: write the proper type here
  _c = (fun fl -> assert ((WS.cs_int.ct_importable fl).ityp == (typ_to_fstar wct fl WS.cs_int.pi WS.cs_int.mst))); // universe problems);

  psi = WS.cs_int.psi;
}
 **)
