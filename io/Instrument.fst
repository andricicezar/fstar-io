module Instrument

open Common
open Free
open Free.IO
open DM

let rec _instrument
  (tree : iio 'a)
  ('p:monitorable_prop) :
  IIO (maybe 'a) 'p (fun _ -> True) (fun _ _ _ -> True) =
  match tree with
  | Return r -> (Inl r)
  | Call GetTrace argz fnc ->
    let h = get_trace () in
    let z' : iio 'a = fnc h in
    rev_append_rev_append ();
    _instrument z' 'p
  | Call cmd argz fnc -> begin
    (** Check if the runtime check failed, and if yes, return the error **)
    match dynamic_cmd cmd 'p argz with
    | Inl rez ->
      let z' : iio 'a = fnc rez in
      rev_append_rev_append ();
      _instrument z' 'p
    | Inr err -> Inr err
  end

let instrument_MIIO = _instrument
