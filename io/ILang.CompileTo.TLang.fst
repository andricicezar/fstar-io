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
  (tree : iio 'b) :
  IIOpi 'b pi =
  admit ();
  let tree : dm_iio 'b (fun p h -> forall (r: 'b) (lt: trace). enforced_locally pi h lt ==> p lt r) = tree in
  IIOwp?.reflect tree

let rec _instrument
  (tree : iio (resexn 'a))
  ('p    : monitorable_prop)
  (piprop:squash (forall h cmd arg. 'p cmd arg h ==> io_pre cmd arg h)) :
  IIOpi (resexn 'a) 'p =
  match tree with
  | Return r -> r
  | Call GetTrace argz fnc -> Inr Contract_failure
  | PartialCall pre fnc -> Inr Contract_failure
  | Decorated d #b m k ->
      let r : b = FStar.Universe.downgrade_val (run_m 'p m) in
      admit ();
      _instrument (k r) 'p piprop
  | Call cmd argz fnc -> begin
    let d : checkable2 (io_pre cmd) = (
      implies_is_checkable2 (io_sig.args cmd) trace ('p cmd) (io_pre cmd) piprop) in
    (** Check if the runtime check failed, and if yes, return the error **)
    let rez = dynamic_cmd cmd d argz in
    let z' : iio (resexn 'a) = fnc rez in
    _instrument z' 'p piprop
  end



class compilable (t:Type) (pi:monitorable_prop) = {
  c_t_ilang : ilang t pi;
  comp_type : Type;
  c_comp_type : tlang comp_type;
  compile: t -> comp_type
  // CC theorem?
  // c_compile: squash (forall (wS:t). theta (reify (compile wS)) `hist_ord` theta (reify wS)) 
}

instance compile_resexn pi (t:Type) {| d1:compilable t pi |} : compilable (resexn t) pi = {
  c_t_ilang = ilang_resexn pi t #d1.c_t_ilang;
  comp_type = resexn (d1.comp_type);
  c_comp_type = tlang_resexn d1.comp_type #d1.c_comp_type;
  compile = (fun x ->
    match x with
    | Inl r -> Inl (compile r)
    | Inr err -> Inr err)
}

class instrumentable (t:Type) (pi:monitorable_prop) = {
  cc_t_ilang : ilang t pi;
  inst_type : Type;
  c_inst_type : tlang inst_type;
  instrument: inst_type -> t 
}

#push-options "--print_universes"
(** TODO: t1 and t2 are in universe 0. is that a problem? can we do HO? **)
instance compile_ilang_base (t1:Type u#0) (t2:Type u#0) pi {| d1:instrumentable t1 pi |} {| d2:compilable t2 pi |} : compilable (t1 -> IIOpi (resexn t2) pi) pi  = {
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
