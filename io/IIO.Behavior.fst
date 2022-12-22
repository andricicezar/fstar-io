module IIO.Behavior

open FStar.Ghost
open FStar.FunctionalExtensionality

open BeyondCriteria
open IIO

assume val __reify_IIOwp (#a:Type) (#wp:Hist.hist a) (#fl:tflag) ($f:unit -> IIOwp a fl wp) : GTot (dm_giio a fl wp)

(** Confusing elements:
1) there are two definitions of trace. one from IIO.Sig.trace and one from BeyondCriteria.trace
2) prefixed_trace_property may be confusing 
**)

type prefixed_trace_property (pre:IIO.Sig.trace -> Type0) = h:IIO.Sig.trace -> (#_:squash (pre h)) -> BeyondCriteria.trace #event -> Type0

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

irreducible
val beh : (unit -> IIO int AllActions (fun _ -> True) (fun _ _ _ -> True)) ^-> trace_property #event
let beh = on_domain _ (fun ws -> _beh ws)

val _beh_ctx : #pre:(trace -> Type0) -> (unit -> IIO int AllActions pre (fun _ _ _ -> True)) -> prefixed_trace_property pre 
let _beh_ctx ws h =
  beh_giio (__reify_IIOwp ws) h 

//irreducible
val beh_ctx : #pre:(trace -> Type0) -> (unit -> IIO int AllActions pre (fun _ _ _ -> True)) ^-> prefixed_trace_property pre 
let beh_ctx #pre = on_domain _ (fun ws -> _beh_ctx #pre ws)

type prefixed_trace (pre:trace->Type0) = h:trace{pre h} * BeyondCriteria.trace #event  

let mem (#pre:trace->Type0) ((h, tr):prefixed_trace pre) (s1:prefixed_trace_property pre) =
  s1 h tr

open FStar.Tactics

val lemma0 : #pre:(trace -> Type0) -> ctx:(fl:erased tflag -> unit -> IIO int fl pre (fun _ _ _ -> True)) -> h1:trace{pre h1} -> h2:trace{pre h2} -> tr:BeyondCriteria.trace -> Lemma (
  let reified_ctx = __reify_IIOwp (ctx AllActions) in
  beh_giio #pre reified_ctx h1 tr ==> beh_giio #pre reified_ctx h2 tr
)

let lemma0 #pre ctx h1 h2 tr =
  let reified_ctx = __reify_IIOwp (ctx AllActions) in
  introduce beh_giio #pre reified_ctx h1 tr 
  ==> beh_giio #pre reified_ctx h2 tr 
  with _. begin
    assume (beh_giio #pre reified_ctx h2 tr)
  end

(* h is non-interfering for flag polymorphic ctx
  -- should be true since a flag polymorphic ctx can do no actions *)
val test : #pre:(trace -> Type0) -> ctx:(fl:erased tflag -> unit -> IIO int fl pre (fun _ _ _ -> True)) ->
  Lemma (
    let bh = beh_ctx #pre (ctx AllActions) in
    forall t1 t2. t1 `mem` bh /\ t2 `mem` bh ==>
      (exists t3. t3 `mem` bh /\ fst t1 == fst t3 /\ snd t2 == snd t3))

let test #pre ctx = 
  let bh = beh_ctx #pre (ctx AllActions) in
  let reified_ctx : dm_giio int AllActions (to_hist pre (fun _ _ _ -> True)) = __reify_IIOwp (ctx AllActions) in
  introduce forall (t1 t2:prefixed_trace pre).
  t1 `mem` bh /\ t2 `mem` bh 
  ==> (exists (t3:prefixed_trace pre). t3 `mem` bh /\ fst t1 == fst t3 /\ snd t2 == snd t3) 
  with begin
    introduce t1 `mem` bh /\ t2 `mem` bh
    ==> (exists (t3:prefixed_trace pre). t3 `mem` bh /\ fst t1 == fst t3 /\ snd t2 == snd t3)
    with _. begin
      let t3 : prefixed_trace pre = (fst t1, snd t2) in 
      assert (t2 `mem` bh);
      lemma0 #pre ctx (fst t2) (fst t1) (snd t2);
      assert (beh_giio #pre reified_ctx (fst t2) (snd t2) ==> beh_giio #pre reified_ctx (fst t1) (snd t2));
      assert (t3 `mem` bh)
    end
  end
