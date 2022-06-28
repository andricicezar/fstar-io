module ILang.CompileTo.MLang

open FStar.List.Tot
open FStar.Tactics
open FStar.Tactics.Typeclasses

open Common

open TC.Checkable
open TC.Monitorable.Hist

open IO.Sig
open IIO

open ILang
open MLang

class compilable (comp_in:Type u#a) (pi:monitorable_prop) = {
  comp_out : Type u#a;
  compile: comp_in -> comp_out;

  [@@@no_method]
  ilang_comp_in : ilang comp_in pi;
  [@@@no_method]
  mlang_comp_out : mlang comp_out;
}

class backtranslateable (btrans_out:Type u#a) (pi:monitorable_prop) = {
  btrans_in : Type u#a;
  backtranslate: btrans_in -> btrans_out;

  [@@@no_method]
  ilang_btrans_out : ilang btrans_out pi;
  [@@@no_method]
  mlang_btrans_in : mlang btrans_in;
  [@@@no_method]
  cc_pi:squash (forall h cmd arg. pi cmd arg h ==> io_pre cmd arg h);
}

class instrumentable (inst_in_in inst_in_out:Type) (pi:monitorable_prop) = {
  inst_out_in : Type;
  inst_out_out : Type;

  instrument: (unverified_arrow inst_out_in inst_out_out pi) -> Tot (verified_arrow inst_in_in inst_in_out pi); 

  [@@@no_method]
  mlang_inst_in : mlang (unverified_arrow inst_out_in inst_out_out pi);
  [@@@no_method]
  ilang_inst_out : ilang (verified_arrow inst_in_in inst_in_out pi) pi;
  [@@@no_method]
  c_pi:squash (forall h cmd arg. pi cmd arg h ==> io_pre cmd arg h);
}

instance instrumentable_is_backtranslateable #t1 #t2 #pi (d1: instrumentable t1 t2 pi) : backtranslateable (verified_arrow t1 t2 pi) pi = {
  btrans_in = unverified_arrow d1.inst_out_in d1.inst_out_out pi;
  mlang_btrans_in = d1.mlang_inst_in;
  backtranslate = d1.instrument;
  ilang_btrans_out = d1.ilang_inst_out;
  cc_pi = d1.c_pi;
}

(** *** Compilable base types **)

instance compile_resexn pi (t:Type) {| d1:compilable t pi |} : compilable (resexn t) pi = {
  ilang_comp_in = ilang_resexn pi t #d1.ilang_comp_in;

  comp_out = resexn (d1.comp_out);
  mlang_comp_out = mlang_resexn d1.comp_out #(d1.mlang_comp_out);

  compile = (fun x ->
    match x with
    | Inl r -> Inl (compile r)
    | Inr err -> Inr err)
}

(** *** Compilable arrows **)

(** TODO: t1 and t2 are in universe 0. is that a problem? can we do HO? **)
instance compile_verified_arrow
  pi
  (t1:Type) {| d1:backtranslateable t1 pi |} 
  (t2:Type) {| d2:compilable t2 pi |} :
  Tot (compilable (verified_arrow t1 t2 pi) pi) = {
  ilang_comp_in = ilang_arrow pi t1 #d1.ilang_btrans_out t2 #d2.ilang_comp_in;

  comp_out = d1.btrans_in -> MIIO (resexn d2.comp_out);
  mlang_comp_out = mlang_arrow d1.mlang_btrans_in d2.mlang_comp_out;

  compile = (fun (f:verified_arrow t1 t2 pi) (x:d1.btrans_in) ->
    let r : unit -> IIOpi _ pi = fun () -> Universe.raise_val (compile #_ #pi #(compile_resexn pi t2 #d2) (f (d1.backtranslate x))) in
    let x : dm_iio _ _ = reify (r ()) in
    let x' : dm_iio (Universe.raise_t (resexn d2.comp_out)) (fun p h -> forall r lt. b2t(enforced_locally pi h lt) ==> p lt r) = x in
    assert (forall h. dm_iio_theta x' (fun lt r -> enforced_locally pi h lt) h);
    let dm : dm_iio (resexn d2.comp_out) trivial_hist = Decorated (fun h lt -> b2t (enforced_locally pi h lt)) x' Return in
    IIOwp?.reflect dm
  );
}

(** *** Backtranslate types **)
instance backtranslateable_resexn pi (t:Type) {| d1:backtranslateable t pi |} : backtranslateable (resexn t) pi = {
  ilang_btrans_out = ilang_resexn pi t #d1.ilang_btrans_out;

  btrans_in = resexn (d1.btrans_in);
  mlang_btrans_in = mlang_resexn d1.btrans_in #d1.mlang_btrans_in;

  cc_pi = d1.cc_pi;
  backtranslate = (fun x ->
    match x with
    | Inl r -> Inl (backtranslate r)
    | Inr err -> Inr err)
}

(** *** Instrumentable arrows **)
instance instrumentable_unverified_arrow 
  pi
  t1 {| d1:compilable t1 pi |}
  t2 {| d2:backtranslateable t2 pi |} : 
  instrumentable t1 t2 pi = {
  mlang_inst_in = mlang_unverified_arrow pi d1.mlang_comp_out d2.mlang_btrans_in;

  inst_out_in = d1.comp_out;
  inst_out_out = d2.btrans_in;
  ilang_inst_out = ilang_arrow pi t1 #d1.ilang_comp_in t2 #d2.ilang_btrans_out;

  c_pi = d2.cc_pi;

  instrument = (fun (f:unverified_arrow d1.comp_out d2.btrans_in pi) (x:t1) -> 
    let (dm : (dm_iio (resexn d2.btrans_in) trivial_hist){ special_tree pi dm }) = reify (f (compile x)) in
    let r  : resexn d2.btrans_in = MLang.InstrumentTo.ILang.instrument_mio dm pi #() #() #d2.cc_pi in 
    backtranslate #_ #pi #(backtranslateable_resexn pi t2 #d2) r 
  )
}
