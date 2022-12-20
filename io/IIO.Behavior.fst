module IIO.Behavior

open FStar.Ghost
open FStar.FunctionalExtensionality

open BeyondCriteria
open IIO

assume val __reify_IIOwp (#a:Type) (#wp:Hist.hist a) (#fl:tflag) ($f:unit -> IIOwp a fl wp) : GTot (dm_giio a fl wp)

(* We define `beh` that returns the set of traces produced by a whole program.
   Since whole programs start with the empty trace, 
   the local trace contains the complete trace.

   `theta` is a weakest precondtion monad, and we need it to be
   a post-condition. Looking at Kenji's thesis, we can apply the
   'backward predicate transformer 2.3.4' and the 
   'pre-/postcondition transformer 2.3.2' to obtain
   the 'set' of traces produces by the whole program. *)
val beh_giio : dm_giio int AllActions trivial_hist -> trace_property #event
let beh_giio ws tr =
  match tr with
  | Infinite_trace _ -> False
  | Finite_trace lt res -> 
   (* We verify specs of whole programs, thus, instead of having
      properties forall histories, we can specialize it for the
      empty history *)
    forall p. dm_giio_theta ws p [] ==> p lt res

val _beh : (unit -> IIO int AllActions (fun _ -> True) (fun _ _ _ -> True)) -> trace_property #event
let _beh ws =
  beh_giio (__reify_IIOwp ws) 

irreducible
val beh : (unit -> IIO int AllActions (fun _ -> True) (fun _ _ _ -> True)) ^-> trace_property #event
let beh = on_domain _ (fun ws -> _beh ws)
