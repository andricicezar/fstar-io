module IIO.Behavior

open FStar.Ghost
open FStar.FunctionalExtensionality

open BeyondCriteria
open IIO

(** reify is not implemented in F* *)
(** our reify is ghost because we want to use it only when reasoning *)
assume val __reify_IIOwp (#a:Type) (#wp:Hist.hist a) (#fl:tflag) ($f:unit -> IIOwp a fl wp) : GTot (dm_giio a fl wp)

(** Confusing elements:
1) there are two definitions of trace. one from IIO.Sig.trace and one from BeyondCriteria.trace
2) prefixed_trace_property may be confusing 
**)

(** The idea of prefixed_trace_property comes from the need to reason 
about the behavior of contexts. When reasoning about contexts,
we have to take in account that the context is called by the partial
program which already produced some events --- that can affect the 
behavior of the context / the instrumentation **)
type prefixed_trace_property (pre:IIO.Sig.trace -> Type0) = 
  h:IIO.Sig.trace -> (#_:squash (pre h)) -> BeyondCriteria.trace #event -> Type0

type prefixed_trace (pre:trace->Type0) = h:trace{pre h} * BeyondCriteria.trace #event  

let pt_mem (#pre:trace->Type0) ((h, tr):prefixed_trace pre) (s1:prefixed_trace_property pre) =
  s1 h tr

(* We define `beh_giio` that returns the set of traces produced by a program
   starting from a given history `h`.

   `theta` is a weakest precondtion monad, and we need it to be
   a post-condition. Looking at Kenji's thesis, we can apply the
   'backward predicate transformer 2.3.4' and the 
   'pre-/postcondition transformer 2.3.2' to obtain
   the 'set' of traces produces by the whole program. *)
val beh_giio : #pre:(trace -> Type0) -> #fl:erased tflag -> dm_giio int fl (to_hist pre (fun _ _ _ -> True)) -> prefixed_trace_property pre 
let beh_giio ws h tr =
  match tr with
  | Infinite_trace _ -> False
  | Finite_trace lt res -> 
    forall p. dm_giio_theta ws p h ==> p lt res

(* _beh is used on whole programs, thus, 
   we specialize it with the empty history *)
val _beh : (unit -> IIO int AllActions (fun _ -> True) (fun _ _ _ -> True)) -> trace_property #event
let _beh ws =
  beh_giio (__reify_IIOwp ws) []

(** used for whole programs **)
[@@ "opaque_to_smt"]
val beh : (unit -> IIO int AllActions (fun _ -> True) (fun _ _ _ -> True)) ^-> trace_property #event
let beh = on_domain _ (fun ws -> _beh ws)

val _beh_ctx : #pre:(trace -> Type0) -> (unit -> IIO int AllActions pre (fun _ _ _ -> True)) -> prefixed_trace_property pre 
let _beh_ctx ws h =
  beh_giio (__reify_IIOwp ws) h 

(** used for contexts **)
//[@@ "opaque_to_smt"]
val beh_ctx : #pre:(trace -> Type0) -> (unit -> IIO int AllActions pre (fun _ _ _ -> True)) ^-> prefixed_trace_property pre 
let beh_ctx #pre = on_domain _ (fun ws -> _beh_ctx #pre ws)