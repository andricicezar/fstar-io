module Compiler.Model

#set-options "--print_universes"

open FStar.Ghost
open FStar.Tactics
open FStar.Tactics.Typeclasses

open BeyondCriteria

open IO.Sig
open TC.Monitorable.Hist
  
open Compiler.Languages
open Compile.IIO.To.ILang

type typ_io_cmds (fl:erased tflag) (pi:monitorable_prop) =
  (cmd : io_cmds) ->
  (arg : io_sig.args cmd) ->
  IIO (io_resm cmd arg) fl
    (requires (fun _ -> True))
    (ensures (fun h r lt ->
      (match r with
       | Inr Contract_failure -> ~(pi cmd arg h) /\ lt == []
       | r' -> pi cmd arg h /\ lt == [convert_call_to_event cmd arg r'])))

val inst_io_cmds : pi:monitorable_prop -> typ_io_cmds AllActions pi
let inst_io_cmds pi cmd arg = 
  let h = get_trace () in
  if pi cmd arg h then (
    assume (io_pre cmd arg h);
    static_cmd cmd arg)
  else Inr Contract_failure

(**
val convert_insts : (ipi:monitorable_prop) -> (epi:monitorable_prop) -> (_:squash (forall h cmd arg. epi cmd arg h ==> ipi cmd arg h)) ->
  (cmd_call:typ_io_cmds AllActions ipi) -> (typ_io_cmds AllActions epi) 
let convert_insts ipi epi () cmd_call cmd arg = 
  assert (forall h. epi cmd arg h ==> ipi cmd arg h);
  cmd_call cmd arg 
**)

(** *** IIO interface **)
noeq
type iio_interface = {
  ct : erased tflag -> Type;
  pt : erased tflag -> Type;

  ct_rcs : tree pck_rc;
  //pt_rc : tree pck_rc;

  epi : monitorable_prop;
 // ipi : monitorable_prop;
//  ipi_stronger_epi : squash (forall h cmd arg. ipi cmd arg h ==> epi cmd arg h);

  //pt_exportable : exportable pt ipi pt_rc AllActions;
  ct_importable : fl:erased tflag -> safe_importable (ct fl) epi ct_rcs fl;
}

let make_rcs_eff (rcs:tree pck_rc) : typ_posts AllActions rcs =
  let r : tree (pck_eff_rc AllActions) = map_tree rcs make_rc_eff in
  assume (equal_trees rcs (map_tree r dfst));
  r

type ctx_iio (i:iio_interface)  = #fl:erased tflag -> typ_posts fl i.ct_rcs -> typ_io_cmds fl i.epi -> i.ct fl 

type prog_iio (i:iio_interface) = #fl:erased tflag -> i.ct (IOActions + fl) -> i.pt (IOActions + fl)

let iio_language : language = {
  interface = iio_interface;

  ctx = ctx_iio;
  pprog = prog_iio;
  whole = (i:iio_interface & i.pt AllActions);

  link = (fun #i p c -> 
    let eff_rcs = make_rcs_eff i.ct_rcs in
    (| i, p #AllActions (c #AllActions eff_rcs (inst_io_cmds i.epi)) |));
  event_typ = IO.Sig.event;

  beh = admit ()
}

(** *** ILang interface **)
noeq
type ilang_interface = {
  ct : erased tflag -> Type u#a;
  pt : Type u#b;

  epi : monitorable_prop;
  
  //pt_ilang : ilang pt ipi;
  ct_ilang : fl:erased tflag -> ilang (ct fl) epi;
}

type ctx_ilang (i:ilang_interface) = #fl:erased tflag -> typ_io_cmds fl i.epi -> i.ct fl
type prog_ilang (i:ilang_interface) = i.ct AllActions -> i.pt

let ilang_language : language = {
  interface = ilang_interface;

  ctx = ctx_ilang;
  pprog = prog_ilang;
  whole = (i:ilang_interface & i.pt);

  link = (fun #i p c -> (| i, p (c (inst_io_cmds i.epi)) |));
  event_typ = IO.Sig.event;

  beh = admit ();
}

(** ** Compile interfaces **)
let comp_int_iio_ilang (i:iio_interface) : ilang_interface = {
 // pt = resexn i.pt_exportable.etype;
  ct = (fun fl -> (i.ct_importable fl).sitype);
  pt = i.pt AllActions;
  epi = i.epi;

//  pt_ilang = ilang_resexn i.ipi i.pt_exportable.etype #i.pt_exportable.c_etype;
  ct_ilang = (fun fl -> (i.ct_importable fl).c_sitype);
}


(** ** Phases of compilation **)
val compiler_pprog_iio_ilang : (#i:iio_interface) -> (p_s:prog_iio i) -> ilang_language.pprog (comp_int_iio_ilang i)
let compiler_pprog_iio_ilang #i p_s c_t = 
  let eff_rcs = make_rcs_eff i.ct_rcs in
  let c_s : i.ct AllActions = (i.ct_importable AllActions).safe_import c_t eff_rcs in
  let p : i.pt AllActions = p_s #AllActions c_s in
  // let eff_rc = make_all_rc_eff i.pt_rc in
  // (i.pt_exportable.export eff_rc p)
  p

let phase1 : compiler = {
  source = iio_language;
  target = ilang_language;

  comp_int = comp_int_iio_ilang;

  compile_pprog = compiler_pprog_iio_ilang;

  rel_traces = (==);
}

val backtranslate : (#i:iio_interface) -> (c_t:ctx_ilang (comp_int_iio_ilang i)) -> iio_language.ctx i
let backtranslate #i c_t #fl eff_rcs acts =
  let c_s = (i.ct_importable fl).safe_import (c_t #fl acts) eff_rcs in
  c_s

open FStar.List

(** Tests **)

(** ** Test 1 - FO **)
let test_interface : iio_interface = {
  epi = (fun _ _ _ -> true);

  pt = (fun fl -> (unit -> IIO (resexn unit) (fl + IOActions) (fun _ -> True) (fun _ _ _ -> true)));

  ct = (fun fl -> unit -> IIO (resexn file_descr) fl (fun _ -> True) (fun h rfd lt -> Inl? rfd ==> is_open (Inl?.v rfd) (rev lt @ h)));
  ct_rcs = Node (| unit, resexn file_descr, (fun () h (rfd:resexn file_descr) lt -> Inl? rfd && (is_open (Inl?.v rfd) (rev lt @ h))) |) Leaf Leaf;


  ct_importable = (fun fl -> 
    let c1post : unit -> squash (forall h lt. enforced_locally (fun _ _ _ -> true) h lt ==> (exists (rfd:resexn file_descr). Inl? rfd ==> is_open (Inl?.v rfd) (rev lt @ h))) = (fun () ->
 //     assert (forall h lt. enforced_locally (fun _ _ _ -> true) h lt ==> (exists (rfd:resexn file_descr). Inl? rfd ==> is_open (Inl?.v rfd) (rev lt @ h)));
    admit ()) in
 //   let c2post : squash (forall h (rfd:resexn file_descr) lt. Inl? rfd && (is_open (Inl?.v rfd) (rev lt @ h)) ==> (Inl? rfd ==> is_open (Inl?.v rfd) (rev lt @ h))) = () in
    safe_importable_arrow_pre_post unit file_descr #_ #_ #fl #exportable_unit #importable_file_descr (fun _ _ -> True) (fun () h rfd lt -> Inl? rfd ==> is_open (Inl?.v rfd) (rev lt @ h)) (c1post ()) ());
}

val test_prog : prog_iio test_interface
let test_prog #fl ctx () : IIO (resexn unit) (fl + IOActions) (fun _ -> True) (fun _ _ _ -> True) =
  let _ = ctx () in
  Inl ()

val test_ctx : ctx_iio test_interface
let test_ctx #fl eff_rcs io_acts () : IIO (resexn file_descr) fl (fun _ -> True) (fun h rfd lt -> Inl? rfd ==> is_open (Inl?.v rfd) (rev lt @ h)) = 
  io_acts Openfile "/etc/passwd"

val test_ctx_t : ctx_ilang (comp_int_iio_ilang test_interface)
let test_ctx_t #fl io_acts () : IIOpi (resexn file_descr) fl (comp_int_iio_ilang test_interface).epi = 
  io_acts Openfile "/etc/passwd"
  

let test_ho_interface : iio_interface = {
  epi = (fun _ _ _ -> true);

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


val test_ho_prog : prog_iio test_ho_interface
let test_ho_prog #fl ctx () : IIO (resexn unit) (fl + IOActions) (fun _ -> True) (fun _ _ _ -> True) =
  let _ = ctx (fun fd -> Inl ()) in
  Inl ()

val test_ho_ctx : ctx_iio test_ho_interface
let test_ho_ctx #fl eff_rcs io_acts cb : IIO (resexn file_descr) fl (fun _ -> True) (fun h rfd lt -> Inl? rfd ==> is_open (Inl?.v rfd) (rev lt @ h)) = 
  let post1 = root eff_rcs in
  let (| _, pre1 |) = root (left eff_rcs) in 
  let rfd = io_acts Openfile "/etc/passwd" in
  match rfd with
  | Inl fd -> let _ = pre1 fd in rfd
  | _ -> rfd

val test_ho_ctx_t : ctx_ilang (comp_int_iio_ilang test_ho_interface)
let test_ho_ctx_t #fl io_acts cb : IIOpi (resexn file_descr) fl (comp_int_iio_ilang test_ho_interface).epi = 
  io_acts Openfile "/etc/passwd"
