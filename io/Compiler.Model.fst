module Compiler.Model

open FStar.Ghost
open FStar.Tactics
open FStar.Tactics.Typeclasses

open BeyondCriteria

open IO.Sig
open TC.Monitorable.Hist
  
open Compiler.Languages
open Compile.IIO.To.ILang

(** *** IIO interface **)
noeq
type iio_interface = {
  pt : Type;
  ct : erased tflag -> Type;

  ct_rc : tree pck_rc;
  pt_rc : tree pck_rc;

  ipi : monitorable_prop;

  pt_exportable : exportable pt ipi pt_rc AllActions;
  ct_importable : fl:erased tflag -> importable (ct fl) ipi ct_rc fl;
}

let make_all_rc_eff (rcs:tree pck_rc) : typ_posts AllActions rcs =
  let r : tree (pck_eff_rc AllActions) = map_tree rcs make_rc_eff in
  assume (equal_trees rcs (map_tree r dfst));
  r

type ctx_iio (i:iio_interface) = #fl:erased tflag -> typ_posts fl i.ct_rc -> i.ct fl 

type prog_iio (i:iio_interface) = i.ct AllActions -> i.pt

let iio_language : language = {
  interface = iio_interface;

  ctx = ctx_iio;
  pprog = prog_iio;
  whole = (i:iio_interface & i.pt);

  link = (fun #i p c -> 
    let eff_rc = make_all_rc_eff i.ct_rc in
    (| i, p (c #AllActions eff_rc) |));
  event_typ = IO.Sig.event;

  beh = admit ()
}

(** *** ILang interface **)
noeq
type ilang_interface = {
  pt : Type;
  ct : erased tflag -> Type;

  ipi : monitorable_prop;
  
  pt_ilang : ilang pt ipi;
  ct_ilang : fl:erased tflag -> ilang (ct fl) ipi;
}

type ctx_ilang (i:ilang_interface) = #fl:erased tflag -> i.ct fl
type prog_ilang (i:ilang_interface) = i.ct AllActions -> i.pt

let ilang_language : language = {
  interface = ilang_interface;

  ctx = ctx_ilang;
  pprog = prog_ilang;
  whole = (i:ilang_interface & i.pt);

  link = (fun #i p c -> (| i, p c |));
  event_typ = IO.Sig.event;

  beh = admit ();
}

(** ** Compile interfaces **)
let comp_int_iio_ilang (i:iio_interface) : ilang_interface = {
  pt = resexn i.pt_exportable.etype;
  ct = (fun fl -> (i.ct_importable fl).itype);
  ipi = i.ipi;

  pt_ilang = ilang_resexn i.ipi i.pt_exportable.etype #i.pt_exportable.c_etype;
  ct_ilang = (fun fl -> (i.ct_importable fl).c_itype);
}


(** ** Phases of compilation **)
let compiler_pprog_iio_ilang (#i:iio_interface) (p_s:prog_iio i) : ilang_language.pprog (comp_int_iio_ilang i) = 
  fun c_t -> 
    let eff_rc = make_all_rc_eff i.ct_rc in
    match (i.ct_importable AllActions).import c_t eff_rc with
    | Inl (c_s:i.ct AllActions) -> begin
       let p : i.pt = p_s c_s in
       let eff_rc = make_all_rc_eff i.pt_rc in
       Inl (i.pt_exportable.export eff_rc p)
    end
    | Inr err -> Inr err

let phase1 : compiler = {
  source = iio_language;
  target = ilang_language;

  comp_int = comp_int_iio_ilang;

  compile_pprog = compiler_pprog_iio_ilang;

  rel_traces = (==);
}

open FStar.List

(** Tests **)
let test_interface : iio_interface = {
  ipi = (fun _ _ _ -> true);

  pt = unit -> IIOpi (resexn unit) AllActions (fun _ _ _ -> true);
  pt_rc = EmptyNode Leaf Leaf;

  ct = (fun fl -> unit -> IIO (resexn file_descr) fl (fun _ -> True) (fun h rfd lt -> Inl? rfd ==> is_open (Inl?.v rfd) (rev lt @ h)));
  ct_rc = Node (| unit, resexn file_descr, (fun () h (rfd:resexn file_descr) lt -> Inl? rfd && (is_open (Inl?.v rfd) (rev lt @ h))) |) Leaf Leaf;


  pt_exportable = exportable_arrow_with_no_pre_and_no_post unit #importable_unit unit #exportable_unit;
  ct_importable = admit () //safe_importable_is_importable (safe_importable_arrow_pre_post file_descr unit );
}

val test_prog : prog_iio test_interface
let test_prog ctx () : IIOpi (resexn unit) AllActions (fun _ _ _ -> true) by (unfold_def (`pi_as_hist); unfold_def (`hist_return); explode (); bump_nth 3; dump "H") =
  let _ = ctx () in
  Inl ()
