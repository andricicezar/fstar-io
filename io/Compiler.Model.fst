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
  ct : erased tflag -> Type;
  pt : Type;

  ct_rc : tree pck_rc;
  pt_rc : tree pck_rc;

  ipi : monitorable_prop;

  pt_exportable : fl:erased tflag -> exportable pt ipi pt_rc fl;
  ct_importable : fl:erased tflag -> importable (ct fl) ipi ct_rc fl;
}

let make_all_rc_eff (i:iio_interface) : typ_posts AllActions i.ct_rc =
  let r : tree (pck_eff_rc AllActions) = map_tree i.ct_rc make_rc_eff in
  assume (equal_trees i.ct_rc (map_tree r dfst));
  r

type ctx_iio (i:iio_interface) = #fl:erased tflag -> typ_posts fl i.ct_rc -> i.ct fl 

type prog_iio (i:iio_interface) = i.ct AllActions -> i.pt

let iio_language : language = {
  interface = iio_interface;

  ctx = ctx_iio;
  pprog = prog_iio;
  whole = (i:iio_interface & i.pt);

  link = (fun #i p c -> 
    let eff_rc = make_all_rc_eff i in
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

(** *** RILang interface **)
noeq
type rilang_interface = {
  pt : Type;
  ct : Type;

  ipi : monitorable_prop;
  
  pt_rilang : rilang pt ipi;
  ct_rilang : rilang ct ipi;
}

type rilang_ctx (i:rilang_interface) = i.ct
type rilang_prog (i:rilang_interface) = rilang_ctx i -> i.pt

let rilang_language : language = {
  interface = rilang_interface;

  ctx = rilang_ctx;
  pprog = rilang_prog;
  whole = (i:rilang_interface & i.pt);

  link = (fun #i p c -> (| i, p c |));
  event_typ = IO.Sig.event;

  beh = admit ();
}

(** *** TLang interface **)
noeq
type tlang_interface = {
  pt : Type u#a;
  ct : (Type u#b ->Type u#(max 1 b))->Type;

  ipi : monitorable_prop;
  
  pt_rilang : rilang pt ipi;
  ct_rilang : rilang (ct (dm_mon ipi).m) ipi;
}

type tlang_ctx (i:tlang_interface) = mon:monad -> acts mon -> i.ct mon.m
type tlang_prog (i:tlang_interface) = i.ct ((dm_mon i.ipi).m) -> i.pt

let tlang_language : language = {
  interface = tlang_interface;

  ctx = tlang_ctx;
  pprog = tlang_prog;
  whole = (i:tlang_interface & i.pt);

  link = (fun #i p c -> (| i, p (c (dm_mon i.ipi) (dm_acts i.ipi)) |));
  event_typ = IO.Sig.event;

  beh = admit ();
}

(** ** Compile interfaces **)
let comp_int_iio_ilang (i:iio_lang_interface) : ilang_interface = {
    pt = resexn i.pt_exportable.etype;
    ct = i.ct_importable.itype;
    ipi = i.ipi;

    pt_ilang = ilang_resexn i.ipi i.pt_exportable.etype #i.pt_exportable.c_etype;
    ct_ilang = i.ct_importable.c_itype;

    pt_reifiable = reify_resexn i.ipi i.pt_exportable.etype #i.pt_reifiable;
    ct_reflectable = i.ct_reflectable; 
}

let comp_int_ilang_rilang (i:ilang_interface) : rilang_interface = {
    pt = i.pt_reifiable.reify_out;
    ct = i.ct_reflectable.reflect_in;
    ipi = i.ipi;

    pt_rilang = i.pt_reifiable.rilang_reify_out;
    ct_rilang = i.ct_reflectable.rilang_reflect_in;
}

let comp_int_rilang_tlang (i:rilang_interface) : tlang_interface = {
    pt = i.pt;
    ct = (fun m -> i.ct); // is this ok?
    ipi = i.ipi;

    pt_rilang = i.pt_rilang;
    ct_rilang = i.ct_rilang; // I suppose yes because of this constraint
}

(** ** Phases of compilation **)
let compiler_pprog_iio_ilang (#i:iio_lang_interface) (p_s:iio_lang_language.pprog i) : ilang_language.pprog (comp_int_iio_ilang i) = fun c_t -> 
    match i.ct_importable.import c_t with
    | Inl c_s -> begin 
      let (| _, ws |) = iio_lang_language.link #i p_s c_s in
      Inl (i.pt_exportable.export ws)
    end
    | Inr err -> Inr err

let phase1 : compiler = {
  source = iio_lang_language;
  target = ilang_language;

  comp_int = comp_int_iio_ilang;

  compile_pprog = compiler_pprog_iio_ilang;

  rel_traces = (==);
}

let compiler_pprog_ilang_rilang (#i:ilang_interface) (p_s:ilang_language.pprog i) : rilang_language.pprog (comp_int_ilang_rilang i) = fun c_t -> 
  let c_s = i.ct_reflectable._reflect c_t in
  let (| _, ws |) = ilang_language.link #i p_s c_s in
  i.pt_reifiable._reify ws

let phase2 : compiler = {
  source = ilang_language;
  target = rilang_language;

  comp_int = comp_int_ilang_rilang;

  compile_pprog = compiler_pprog_ilang_rilang;

  rel_traces = (==);
}

let compiler_pprog_rilang_tlang (#i:rilang_interface) (p_s:rilang_language.pprog i) : tlang_language.pprog (comp_int_rilang_tlang i) = p_s

let phase3 : compiler = {
  source = rilang_language;
  target = tlang_language;

  comp_int = comp_int_rilang_tlang;

  compile_pprog = compiler_pprog_rilang_tlang;

  rel_traces = (==);
}

let compiler = (phase1 `chain_compilers` phase2) `chain_compilers` phase3

(** Tests **)
let test_interface : iio_lang_interface = {
  pt = unit -> IIO unit (fun h -> True) (fun h r lt -> True);
  ct = (x:file_descr) -> IIO unit (fun h -> is_open x h) (fun h r lt -> is_open x (apply_changes h lt));

  ipi = (fun _ _ _ -> true);

  pt_exportable = admit ();
  ct_importable = admit ();
  pt_reifiable = admit ();
  ct_reflectable = admit ();
}

val test_prog : iio_lang_prog test_interface
let test_prog ctx () =
  let fd = static_cmd Openfile "../Makefile" in
  if Inl? fd then ctx (Inl?.v fd)
  else ()
