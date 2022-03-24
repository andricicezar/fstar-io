module Instrument

open FStar.List
open FStar.Tactics

open Common
open IO.Sig
open DM
open TC.Checkable
open TC.Monitorable
open TC.Instrumentable.IIO

let rev_append_rev_append () : Lemma (
  forall (h le1 le2:trace).
    ((List.rev le2) @ (List.rev le1) @ h) ==
      ((List.rev (le1@le2)) @ h))
   by (FStar.Tactics.Derived.l_to_r [`List.append_assoc;`List.rev_append])
      = ()

let rec npnode (t:iio 'a) =
  match t with
  | Return _ -> True
  | PartialCall _ _ -> False
  | Call cmd arg fnc -> forall r. npnode (fnc r)
  
type npiio 'a = t:(iio 'a){npnode t}

let rec _instrument
  (tree : npiio 'a)
  ('p    : monitorable_prop)
  (piprop:squash (forall h cmd arg. 'p cmd arg h ==> io_pre cmd arg h)) :
  IIOpi (maybe 'a) 'p (fun _ -> True) (fun _ _ _ -> True) =
  match tree with
  | Return r -> (Inl r)
  | Call GetTrace argz fnc ->
    let h = get_trace () in
    let z' : npiio 'a = fnc h in
    _instrument z' 'p piprop
  | Call cmd argz fnc -> begin
    let d : checkable2 (io_pre cmd) = (
      implies_is_checkable2 (io_sig.args cmd) trace ('p cmd) (io_pre cmd) piprop) in
    (** Check if the runtime check failed, and if yes, return the error **)
    match dynamic_cmd cmd d argz with
    | Inl rez ->
      let z' : npiio 'a = fnc rez in
      _instrument z' 'p piprop
    | Inr err -> Inr err
  end

let instrument_MIIO = _instrument
