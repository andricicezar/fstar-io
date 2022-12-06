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


(** * Tests **)
open FStar.List

(** ** Test 1 - FO **)
let ex1_ct_post = (fun () h (rfd:resexn file_descr) lt -> (forall fd'. ~((EOpenfile "/etc/passwd" fd') `List.memP` lt)) /\ (Inl? rfd ==> is_open (Inl?.v rfd) (rev lt @ h)))
let ex1_spec_pi : monitorable_prop = (fun cmd arg h -> match cmd, arg with | Openfile, s -> if s = "/etc/passwd" then false else true | _ -> true)
let ex1_inst_pi : monitorable_prop = ex1_spec_pi
let ex1_ct_rc = (fun () h (rfd:resexn file_descr) lt -> Inl? rfd && (is_open (Inl?.v rfd) (rev lt @ h)))

let rec ex1_c1post0 (h:trace) (lt:trace) : Lemma
  (requires (enforced_locally ex1_spec_pi h lt))
  (ensures (ex1_ct_post () h (Inr Contract_failure) lt))
  (decreases lt) =
  match lt with
  | [] -> ()
  | e :: tail -> ex1_c1post0 (e::h) tail

val ex1_c1post : squash (forall h lt. enforced_locally ex1_spec_pi h lt ==> (ex1_ct_post () h (Inr Contract_failure) lt))
let ex1_c1post = Classical.forall_intro_2 (Classical.move_requires_2 ex1_c1post0)

val ex1_c2post : squash (forall x h r lt. enforced_locally ex1_spec_pi h lt /\ (ex1_ct_rc x h r lt) ==> ex1_ct_post x h r lt)
let ex1_c2post = ()

let rec ex1_stronger_pis0 (h:trace) (lt:trace) : Lemma
  (requires (enforced_locally ex1_inst_pi h lt))
  (ensures (enforced_locally ex1_spec_pi h lt))
  (decreases lt) =
  match lt with
  | [] -> ()
  | e :: tail -> ex1_stronger_pis0 (e::h) tail
                                                  
val ex1_stronger_pis : squash (forall h lt. enforced_locally ex1_inst_pi h lt ==> enforced_locally ex1_spec_pi h lt)
let ex1_stronger_pis = Classical.forall_intro_2 (Classical.move_requires_2 ex1_stronger_pis0)

let ex1_interface : src_interface = {
  spec_pi = ex1_spec_pi;
  inst_pi = ex1_inst_pi;

  pt = (fun fl -> (unit -> IIO (resexn unit) (fl + IOActions) (fun _ -> True) (fun _ _ _ -> True)));

  ct = (fun fl -> unit -> IIO (resexn file_descr) fl (fun _ -> True) (ex1_ct_post ()));
  ct_rcs = Node (| unit, resexn file_descr, ex1_ct_rc |) Leaf Leaf;


  ct_importable = (fun fl -> 
    safe_importable_arrow_pre_post unit file_descr #_ #_ #fl #exportable_unit #importable_file_descr (fun _ _ -> True) ex1_ct_post ex1_c1post ex1_c2post);
  
  inst_pi_stronger_spec_pi = ex1_stronger_pis;
}

val ex1_prog : prog_src ex1_interface
let ex1_prog #fl ctx () : IIO (resexn unit) (fl + IOActions) (fun _ -> True) (fun _ _ _ -> True) =
  let _ = ctx () in
  Inl ()

val ex1_ctx : ctx_src ex1_interface
let ex1_ctx #fl io_acts eff_rcs () : IIO (resexn file_descr) fl (fun _ -> True) (ex1_ct_post ()) = 
  io_acts Openfile "/etc/passwd"

val ex1_ctx_t : ctx_tgt (comp_int_src_tgt ex1_interface)
let ex1_ctx_t #fl io_acts () : IIOpi (resexn file_descr) fl (comp_int_src_tgt ex1_interface).spec_pi = 
  io_acts Openfile "/etc/passwd"

(** ** Test 3 - HO 1 **)

let test_ho_interface : src_interface = {
  spec_pi = (fun _ _ _ -> true);
  inst_pi = (fun _ _ _ -> true);
  inst_pi_stronger_spec_pi = ();

  pt = (fun fl -> (unit -> IIO (resexn unit) (fl + IOActions) (fun _ -> True) (fun _ _ _ -> true)));

  ct = (fun fl -> (fd:file_descr -> IIO (resexn unit) fl (fun h -> is_open fd h) (fun _ _ lt -> lt == [])) -> IIO (resexn file_descr) fl (fun _ -> True) (fun h rfd lt -> Inl? rfd ==> is_open (Inl?.v rfd) (rev lt @ h)));
  ct_rcs = Node (| unit, resexn file_descr, (fun () h (rfd:resexn file_descr) lt -> Inl? rfd && (is_open (Inl?.v rfd) (rev lt @ h))) |) 
              (Node (| file_descr, resexn unit, (fun fd h _ _ -> is_open fd h) |) Leaf Leaf)
              Leaf;

  ct_importable = admit () ;
   (**(fun fl -> 
    let exportable_cb = exportable_arrow_pre_post file_descr unit #_ #(Node (| file_descr, resexn unit, (fun fd h _ _ -> is_open fd h) |) Leaf Leaf) #fl #importable_file_descr #exportable_unit (fun fd h -> is_open fd h) (fun fd _ _ lt -> lt == []) #() #() in

    let c1post : unit -> squash (forall h lt. enforced_locally (fun _ _ _ -> true) h lt ==> (exists (rfd:resexn file_descr). Inl? rfd ==> is_open (Inl?.v rfd) (rev lt @ h))) = (fun () ->
 //     assert (forall h lt. enforced_locally (fun _ _ _ -> true) h lt ==> (exists (rfd:resexn file_descr). Inl? rfd ==> is_open (Inl?.v rfd) (rev lt @ h)));
    admit ()) in
 //   let c2post : squash (forall h (rfd:resexn file_descr) lt. Inl? rfd && (is_open (Inl?.v rfd) (rev lt @ h)) ==> (Inl? rfd ==> is_open (Inl?.v rfd) (rev lt @ h))) = () in
    safe_importable_arrow_pre_post _ file_descr #_ #_ #fl #exportable_cb #importable_file_descr (fun _ _ -> True) (fun () h rfd lt -> Inl? rfd ==> is_open (Inl?.v rfd) (rev lt @ h)) (c1post ()) ());**)
}


val test_ho_prog : prog_src test_ho_interface
let test_ho_prog #fl ctx () : IIO (resexn unit) (fl + IOActions) (fun _ -> True) (fun _ _ _ -> True) =
  let _ = ctx (fun fd -> Inl ()) in
  Inl ()

val test_ho_ctx : ctx_src test_ho_interface
let test_ho_ctx #fl io_acts eff_rcs cb : IIO (resexn file_descr) fl (fun _ -> True) (fun h rfd lt -> Inl? rfd ==> is_open (Inl?.v rfd) (rev lt @ h)) = 
  let post1 = root eff_rcs in
  let (| _, pre1 |) = root (left eff_rcs) in 
  let rfd = io_acts Openfile "/etc/passwd" in
  match rfd with
  | Inl fd -> let _ = pre1 fd in rfd
  | _ -> rfd

(** can't type this without defining ct_importable
val test_ho_ctx_t : ctx_ilang (comp_int_iio_ilang test_ho_interface)
let test_ho_ctx_t #fl io_acts cb : IIOpi (resexn file_descr) fl (comp_int_iio_ilang test_ho_interface).spec_pi = 
  io_acts Openfile "/etc/passwd"
**)
