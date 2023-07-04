module Callback

open FStar.Tactics

open Common
open DM 
open TC.ML
open TC.ML.HO
open TC.Checkable
open TC.Export
open TC.MLify.IIOwp
open TC.Monitorable.Hist
open TC.Instrumentable.IIOwp

(** ** Case 1 - function map **)
(** *** accepts a first-order function **)
type map_iio =
  (#a:Type) ->
  (#b:Type) ->
  (#pre:(a -> trace -> bool)) ->
  (#post:(a -> trace -> b -> trace -> Type0)) ->
  (f:(x:a -> IIO b (fun h -> pre x h) (post x))) ->
  (xs:list a) ->
  IIO (list b) 
    (requires (fun h -> forall x. x `List.Tot.memP` xs ==> pre x h))
    (ensures (fun _ _ _ -> True)) (** it is hard to write a useful post-condition. However, we're not interested in it **)

let map_is_mlifyable : mlifyable map_iio = admit ()
(** Todo:
  1. a must be importable
  2. b must be exportable
  3. pre must be checkable
  4. post must be monitorable
  5. show that map's pre is checkable by having f's pre being checkable
**)

(** ** Case 3 - apply **)
(** ***  - returns a function **)

(** ** Case 4 - HO Callback **)
(** ***  - callback with a callback **)
