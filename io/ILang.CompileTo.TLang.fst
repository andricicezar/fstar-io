module ILang.CompileTo.TLang

open FStar.Tactics
open FStar.Tactics.Typeclasses

open Common

open ILang
open TLang
open Hist
open TC.Monitorable.Hist

open IO.Sig
open DM.IIO
open TC.Checkable

class compilable (t:Type) (pi:monitorable_prop) = {
  c_t_ilang : ilang t pi;
  comp_type : Type;
  c_comp_type : tlang comp_type;
  compile: t -> comp_type
  // CC theorem?
  // c_compile: squash (forall (wS:t). theta (reify (compile wS)) `hist_ord` theta (reify wS)) 
}

class instrumentable (t:Type) (pi:monitorable_prop) = {
  cc_t_ilang : ilang t pi;
  inst_type : Type;
  c_inst_type : tlang inst_type;
  c_pi:squash (forall h cmd arg. pi cmd arg h ==> io_pre cmd arg h);
  instrument: inst_type -> t 
}

(** *** Compilable base types **)

instance compile_resexn pi (t:Type) {| d1:compilable t pi |} : compilable (resexn t) pi = {
  c_t_ilang = ilang_resexn pi t #d1.c_t_ilang;
  comp_type = resexn (d1.comp_type);
  c_comp_type = tlang_resexn d1.comp_type #d1.c_comp_type;
  compile = (fun x ->
    match x with
    | Inl r -> Inl (compile r)
    | Inr err -> Inr err)
}

(** *** Compilable arrows **)

(** TODO: t1 and t2 are in universe 0. is that a problem? can we do HO? **)
instance compile_ilang_base (t1:Type u#0) (t2:Type u#0) pi {| d1:instrumentable t1 pi |} {| d2:compilable t2 pi |} : compilable (t1 -> IIOpi (resexn t2) pi) pi = {
  c_t_ilang = ilang_arrow pi t1 #d1.cc_t_ilang t2 #d2.c_t_ilang;
  comp_type = d1.inst_type -> MIIO (resexn d2.comp_type);
  c_comp_type = tlang_arrow d1.inst_type d2.comp_type #d1.c_inst_type #d2.c_comp_type;
  compile = (fun (f:(t1 -> IIOpi (resexn t2) pi)) (x:d1.inst_type) ->
    let r : unit -> IIOpi _ pi = fun () -> Universe.raise_val (compile #_ #pi #(compile_resexn pi t2 #d2) (f (instrument x))) in
    let x : dm_iio _ _ = reify (r ()) in
    let x' : dm_iio (Universe.raise_t (resexn d2.comp_type)) (fun p h -> forall r lt. b2t(enforced_locally pi h lt) ==> p lt r) = x in
    assert (forall h. dm_iio_theta x' (fun lt r -> enforced_locally pi h lt) h);
    (** TODO: I have no idea what happens with the raise_t of the result. 
        I suppose for now it does not care. There is a Universe.downgrade_val in the theta and I suppose there will be another
        downgrade_val when interpreting the tree. **)
    let dm : dm_iio (resexn d2.comp_type) (trivial_hist ()) = Decorated (fun h lt -> b2t (enforced_locally pi h lt)) x' Return in
    IIOwp?.reflect dm
  );
}

(** *** Insturmentable types **)
instance instrumentable_resexn pi (t:Type) {| d1:instrumentable t pi |} : instrumentable (resexn t) pi = {
  cc_t_ilang = ilang_resexn pi t #d1.cc_t_ilang;
  inst_type = resexn (d1.inst_type);
  c_inst_type = tlang_resexn d1.inst_type #d1.c_inst_type;
  c_pi = d1.c_pi;
  instrument = (fun x ->
    match x with
    | Inl r -> Inl (instrument r)
    | Inr err -> Inr err)
}


(** *** Instrumentable arrows **)
assume val dynamic_cmd :
  (cmd : io_cmds) ->
  (d1 : checkable2 (io_pre cmd)) ->
  (arg : io_sig.args cmd) ->
  IIOwp (io_resm cmd)
    (fun p h ->
      (forall (r:(io_sig.res cmd arg)) lt.
        (match r with
         | Inr Contract_failure -> ~(d1.check2 arg h) /\ lt == []
         | _ -> d1.check2 arg h /\ lt == [convert_call_to_event cmd arg r]) ==> p lt r))

let run_m
  (pi:monitorable_prop)
  (tree : dm_iio 'b (fun p h -> forall lt r. enforced_locally pi h lt ==> p lt r)) :
  IIOpi 'b pi =
  let tree : dm_iio 'b (fun p h -> forall (r: 'b) (lt: trace). enforced_locally pi h lt ==> p lt r) = tree in
  IIOwp?.reflect tree

let rec _instrument
  (tree : dm_iio (resexn 'a) (trivial_hist ()))
  (pi    : monitorable_prop)
  (c_pi:squash (forall h cmd arg. pi cmd arg h ==> io_pre cmd arg h)) :
  IIOpi (resexn 'a) pi =
  match tree with
  | Return r -> r
  | Call GetTrace argz fnc -> Inr Contract_failure
  | PartialCall pre fnc -> Inr Contract_failure
  | Decorated d #b m k ->
      assume (forall h. dm_iio_theta m (fun lt r -> enforced_locally pi h lt) h);
      let r : b = FStar.Universe.downgrade_val (run_m pi m) in
      let z' : iio (resexn 'a) = k r in
      assume (trivial_hist () `hist_ord` dm_iio_theta z');
      admit ();
      _instrument z' pi c_pi
  | Call cmd argz fnc -> begin
    let d : checkable2 (io_pre cmd) = (
      implies_is_checkable2 (io_sig.args cmd) trace (pi cmd) (io_pre cmd) c_pi) in
    (** Check if the runtime check failed, and if yes, return the error **)
    let rez = dynamic_cmd cmd d argz in
    let z' : iio (resexn 'a) = fnc rez in
    assume (trivial_hist () `hist_ord` dm_iio_theta z');
    _instrument z' pi c_pi
  end

instance instrumentable_arrow t1 t2 pi {| d1:compilable t1 pi |} {| d2:instrumentable t2 pi |} : instrumentable (t1 -> IIOpi (resexn t2) pi) pi = {
  cc_t_ilang = ilang_arrow pi t1 #d1.c_t_ilang t2 #d2.cc_t_ilang;
  inst_type = d1.comp_type -> MIIO (resexn d2.inst_type);
  c_inst_type = tlang_arrow d1.comp_type d2.inst_type #d1.c_comp_type #d2.c_inst_type;
  c_pi = d2.c_pi;
  instrument = (fun (f:d1.comp_type -> MIIO (resexn d2.inst_type)) (x:t1) -> 
    let tree : dm_iio (resexn d2.inst_type) (trivial_hist ()) = reify (f (compile x)) in
    let r  : resexn d2.inst_type = _instrument #d2.inst_type tree pi d2.c_pi in 
    instrument #_ #pi #(instrumentable_resexn pi t2 #d2) r 
  )
}
