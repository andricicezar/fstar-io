module Execute

open FStar.All
open Compiler.Model1
open Utils

let the_p #a : hist_post #event a = fun lt r -> True

exception Something_went_really_bad

let rec skip_partial_calls (tree: mio mymst int { forall h. dm_mio_theta tree the_p h }) : ML int =
  match tree with
  | Return y -> y
  | PartialCall pre k -> begin
    (** The intuition here is that the pre-condition is true,
    thus, all asserts are true **)
   assert (dm_mio_theta tree the_p []);
   assert pre;
   skip_partial_calls (k ())
  end
  (** during extraction, MIO.Call is replaced with an actual
  implementation of the commands, therefore, the `Call` constructor
  does not exist **)
  | _ -> raise Something_went_really_bad

open FStar.Tactics

let cast_mio (wp : hist 'a) (t : dm_mio mymst 'a wp) : (x : mio mymst 'a { wp `hist_ord` dm_mio_theta x }) =
  t

let execute (w:unit -> MIO int AllActions mymst (fun _ -> True) (fun _ _ _ -> True)) : ML int by (compute ()) =
  let dm_tree : dm_gmio int mymst AllActions trivial_hist = reify (w ()) in
  let dm_tree' : dm_mio mymst int trivial_hist = dm_tree in
  let dm_tree2 : (x : mio mymst int { trivial_hist `hist_ord` dm_mio_theta x }) = cast_mio trivial_hist dm_tree' in
  skip_partial_calls dm_tree2
