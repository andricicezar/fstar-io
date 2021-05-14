module Instrument

open FStar.All

open Free.IO
open DM

let rec _instrument
  (tree : iio 'a)
  ('p:monitorable_prop) :
  IIO 'a 'p (fun _ -> True) (fun _ _ _ -> True) =
  match tree with
  | Return r -> r
  | Call GetTrace argz fnc ->
      let h = get_trace () in
      let z' : iio 'a = fnc h in
      rev_append_rev_append ();
      _instrument z' 'p
  | Call cmd argz fnc ->
      let rez = dynamic_cmd cmd 'p argz in
      let z' : iio 'a = fnc rez in
      rev_append_rev_append ();
      _instrument z' 'p

let instrument_MIIO = _instrument
