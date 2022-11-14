module Compiler.Model

open FStar.Tactics
open FStar.Tactics.Typeclasses

open IO.Sig
open TC.Monitorable.Hist
  
open Compiler.Languages

open Compile.IIO.To.ILang

noeq
type iio_lang_interface = {
  ct : Type;
  pt : Type;

  vpi : monitorable_prop;

  c1 : exportable pt vpi;
  c2 : importable ct vpi;
}

let test_interface : iio_lang_interface = {
  pt = unit -> IIO unit (fun h -> True) (fun h r lt -> True);
  ct = (x:file_descr) -> IIO unit (fun h -> is_open x h) (fun h r lt -> is_open x (apply_changes h lt));

  vpi = (fun _ _ _ -> true);

  c1 = admit ();
  c2 = admit ();
}

type iio_lang_ctx (i:iio_lang_interface) = i.ct
type iio_lang_prog (i:iio_lang_interface) = iio_lang_ctx i -> i.pt

let iio_lang_language : BeyondCriteria.language = {
  interface = iio_lang_interface;

  ctx = iio_lang_ctx;
  pprog = iio_lang_prog;
  whole = (i:iio_lang_interface & i.pt);

  link = (fun #i p c -> (| i, p c |));
  event_typ = IO.Sig.event;

  beh = admit ()
}

val test_prog : iio_lang_prog test_interface
let test_prog ctx () =
  let fd = static_cmd Openfile "../Makefile" in
  if Inl? fd then ctx (Inl?.v fd)
  else ()

noeq
type ilang_interface = {
  pt : Type;
  ct : Type;

  vpi : monitorable_prop;
}

type ilang_ctx (i:ilang_interface) = i.ct
type ilang_prog (i:ilang_interface) = ilang_ctx i -> i.pt

let ilang_language : BeyondCriteria.language = {
  interface = ilang_interface;

  ctx = ilang_ctx;
  pprog = ilang_prog;
  whole = (i:ilang_interface & i.pt);

  link = (fun #i p c -> (| i, p c |));
  event_typ = IO.Sig.event;

  beh = admit ();
}

let comp_int (i:iio_lang_interface) : ilang_interface = {
    pt = resexn i.c1.etype;
    ct = i.c2.itype;
    vpi = i.vpi;
}

let compiler_pprog (#i:iio_lang_interface) (p:iio_lang_language.pprog i) : ilang_language.pprog (comp_int i) = fun c -> 
    match i.c2.import c with
    | Inl c' -> begin 
      let (| _, pt |) = iio_lang_language.link #i p c' in
      Inl (i.c1.export pt)
    end
    | Inr err -> Inr err

let phase1 : BeyondCriteria.compiler = {
  source = iio_lang_language;
  target = ilang_language;

  comp_int = comp_int;

  compile_pprog = (fun #i p c -> 
    match i.c2.import c with
    | Inl c' -> begin 
      let (| _, pt |) = iio_lang_language.link #i p c' in
      (** WTF **)
      assert False;
      Inl (i.c1.export pt)
    end
    | Inr err -> Inr err);

  rel_traces = admit ();
}

