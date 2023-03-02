module Execute

open FStar.All
open Compiler.Model

let the_p #a : hist_post #event a = fun lt r -> True

exception Something_went_really_bad

let rec skip_partial_calls (tree:mio int) (_:squash (forall h. dm_mio_theta tree the_p h)) : ML int =
  match tree with
  | Return y -> y
  | PartialCall pre k -> begin
    (** The intuition here is that the pre-condition is true,
    thus, all asserts are true **)
   assert (dm_mio_theta tree the_p []);
   assert pre;
   skip_partial_calls (k ()) ()
  end
  (** during extraction, Free.IO.Call is replaced with an actual
  implementation of the commands, therefore, the `Call` constructor
  does not exist **)
  | _ -> raise Something_went_really_bad

let execute (w:unit -> MIO int AllActions (fun _ -> True) (fun _ _ _ -> True)) : ML int =
  let dm_tree : dm_gmio int AllActions trivial_hist = reify (w ()) in
  let dm_tree' : dm_mio int trivial_hist = dm_tree in
  admit ();
  skip_partial_calls dm_tree' ()
