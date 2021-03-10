module Handle

open IO.Free
open IO.Effect
open IIO.Effect
open MIIO.Effect
open FStar.All
open Minterop

let rec _import_pi_IIO
  (tree : iio 'a)
  ('p:monitorable_prop) :
  IIO 'a 'p (fun _ -> True) (fun _ _ _ -> True) =
  match tree with
  | Return (Inl r) -> r
  | Return (Inr err) -> IIO.Effect.throw err
  | Call GetTrace argz fnc ->
      let h = IIO.Effect.get_trace () in
      let z' : iio 'a = fnc (Inl h) in
      rev_append_rev_append ();
      _import_pi_IIO z' 'p
  | Call cmd argz fnc ->
      let rez : res cmd = IIO.Effect.dynamic_cmd cmd 'p argz in
      let rezm : resm cmd = Inl rez in
      let z' : iio 'a = fnc rezm in
      rev_append_rev_append ();
      _import_pi_IIO z' 'p

let handle = _import_pi_IIO

let ctx_t_to_ctx_p
  (pi:monitorable_prop)
  (f:'a -> MIIO 'b)
  (x:'a) :
  IIO 'b pi (fun _ -> True) (fun _ _ _ -> True) =
    handle ((* MIIO.*)reify (f x) [] (fun _ _ -> True)) pi

open Hist

effect IIO
  (a:Type)
  (pi : monitorable_prop) =
  IIOwp a (fun (h:trace) (p:hist_post a) ->
    enforced_globally pi h /\
    (forall res lt. (
      enforced_globally pi (apply_changes h lt) ==>  p res lt)))


let _export_hgh
  (pi:monitorable_prop)
  (f:('a -> IIO 'b pi) -> IIO 'c pi)
  (p:('a -> IIO 'b pi)) :
  MIIO 'c =
    let h = get_trace () in
    if enforced_globally pi h then
      f p
    else IIO.Effect.throw Contract_failure

let _import_tot
  {| d1:exportable 'a |}
  {| d2:importable 'b |}
  (pi:monitorable_prop)
  (f:d1.etype -> Tot d2.itype)
  (x:'a) :
  IIO 'b pi =
    match import (f (export x)) with
    | Some x -> x
    | None -> IIO.Effect.throw Contract_failure

let _export_hgh_ML
  {| d1:exportable 'a |}
  {| d2:importable 'b |}
  {| d3:exportable 'c |}
  (pi:monitorable_prop)
  (f:('a -> IIO 'b pi) -> MIIO 'c)
  (p:(d1.etype -> Tot d2.itype)) :
  ML d3.etype =
   let p' : 'a -> IIO 'b pi = _import_tot pi p in
   let tree : iio 'c = reify (f p') [] (fun _ _ -> True) in
   let r : 'c = iio_interpreter tree in
   export r
