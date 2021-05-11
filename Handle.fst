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
  ('p:monitorable_prop)
  (f:d1.etype -> Tot d2.itype)
  (x:'a) :
  IIO 'b 'p =
    match import (f (export x)) with
    | Some x -> x
    | None -> IIO.Effect.throw Contract_failure

(** Why 'a -> IIO 'b pi -> MIIO y and not MIIO everywhere?
    Because if the argument is an arrow, then we can not do
    anything in ML to instrument it. So, we have to assume
    that the arrow we get as an argument is linked with the
    proper library and triggers only the events we care
    about. **)
let _export_hgh_ML
  {| d1:ml 'a |}
  {| d2:ml 'b |}
  {| d3:ml 'c |}
  ('p:monitorable_prop)
  (f:('a -> IIO 'b 'p) -> MIIO 'c)
  (p:('a -> Tot 'b)) :
  ML 'c =
   let tree : iio 'c = reify (f p) [] (fun _ _ -> True) in
   iio_interpreter tree
