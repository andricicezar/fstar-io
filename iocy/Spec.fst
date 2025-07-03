module Spec

open FStar.Tactics
open FStar.List.Tot
open ParallelTraces

(** The following refinement tries to capture the idea that pts is complete: contains
    all the defined promises.

CA: Not sure if it achieves that.   **)
let w_pre e = h:atrace e -> pts:parallel_traces e{
  closed_atrace pts h
  // /\ (forall pr. pr `mem` pts ==> (sel pr pts) `suffix_of` pr.lt)
  // we cannot have this refinement since we don't store the trace on the promise anymore
} -> Type0


let w_post e a h pts =
  a -> lt:atrace e -> pts':parallel_traces e{
      pts `ord` pts' /\
      closed_atrace pts' ((rev lt) @ h)
  } -> Type0

let w e a = h:atrace e -> pts:parallel_traces e{closed_atrace pts h} -> w_post e a h pts -> Type0

(** We would like to be able to verify that {empty} 1;2;3;4 {empty} *)


(** One may need some extra constraint between how pts evolves to pts':
let w e a = h:atrace e -> pts:parallel_traces e{closed_atrace pts h} -> c:(pts:_ -> pts':_ -> Type0) -> w_post e a h pts c -> Type0
**)

unfold
let w_return e #a (x:a) : w e a =
  fun h pts p -> p x [] pts

(** Return may also need a forall,

    What about Bind? hopefully, it is covered .
    similar to framing in pulse, steel? **)

unfold
let w_bind #e #a #b (m:w e a) (f: a -> w e b) : w e b =
  fun h pts post ->
    m h pts (fun r' lt' pts' ->
        f r' ((rev lt')@h) pts' (fun r'' lt'' pts'' ->
        post r'' (lt'@lt'') pts''))

(** collecting - vs
    scheduling - **)

unfold
let w_async #e #a (wf:w e a) : w e (promise e a) =
  fun h pts post ->
    (** CA: I think passing `h` and `pts` to `wf` is wrong,

        wf can have as a pre that h and pts are empty,
        which could be when wf is asynced.
        However, one can always bind things later, which would
        make h and pts not empty.

        My guess is that one would have to do a
          forall h' pts'. h < h' /\ pts < pts' ==> wf h' pts' ...

        Probably all operations need this quantification.
    *)
    wf h pts (fun r' lt' pts' ->
      let prpts'' = async r' lt' pts' in
      post (fst prpts'') [EAsync a (fst prpts'')] (snd prpts''))

unfold
let w_await #e #a (pr:promise e a) : w e a =
  fun h pts post ->
    pr `mem` pts /\
    post (sel_r pr pts) [EAwait pr] (await pr pts)

unfold
let w_produce #e (ev:e) : w e unit =
  fun h pts post ->
    post () [Ev ev] pts

unfold
let w_ord #e #a (w1 w2:w e a) =
  forall h pts post. w2 h pts post ==> w1 h pts post

unfold
let encode_pre_post_in_w #e #a
  (pre:w_pre e)
  (post:(h:atrace e -> pts:parallel_traces e -> w_post e a h pts))
  : w e a
  = (fun h pts p -> pre h pts /\ (forall r' lt' pts'. post h pts r' lt' pts' ==> p r' lt' pts'))

unfold
let (let!) #e #a #b (m:w e a) (f: a -> w e b) : w e b = w_bind m f

let _ =
  assert (
    (w_produce 0)
    `w_ord`
    encode_pre_post_in_w (fun _ _ -> True) (fun _ _ _ lt _ -> lt == [Ev 0]))

let _ =
  assert (
    (w_produce 0 ;! w_produce 1 ;! w_produce 2)
    `w_ord`
    encode_pre_post_in_w (fun _ _ -> True) (fun _ _ _ lt _ -> lt == [Ev 0; Ev 1; Ev 2]))

#push-options "--fuel 10"
let _ =
  assert (
    (w_produce 0 ;! w_produce 1 ;! w_produce 2;! w_produce 2;! w_produce 2;! w_produce 2;! w_produce 2;! w_produce 2)
    `w_ord`
    encode_pre_post_in_w (fun _ _ -> True) (fun _ _ _ lt _ -> lt == [Ev 0; Ev 1; Ev 2; Ev 2; Ev 2; Ev 2; Ev 2; Ev 2]))
#pop-options

let test_await (pr:promise int unit) =
  assert (
    (w_await pr)
    `w_ord`
    encode_pre_post_in_w (fun _ pts -> pr `mem` pts) (fun _ _ _ lt _ -> lt == [EAwait pr]))

let test_ev_await (pr:promise int unit) =
  assert (
    (w_await pr ;! w_produce 0)
    `w_ord`
    encode_pre_post_in_w (fun _ pts -> pr `mem` pts) (fun _ _ _ lt _ -> lt == [EAwait pr; Ev 0]))

let test_async () =
  assert (
    (w_async (w_produce 5))
    `w_ord`
    encode_pre_post_in_w (fun _ _ -> True) (fun _ _ pr lt _ -> lt == [EAsync unit pr]))

let test_async_ev () =
  assert (
    (let! _ = w_async (w_produce 5) in w_produce 2)
    `w_ord`
    encode_pre_post_in_w (fun _ _ -> True) (fun _ _ _ lt _ -> exists pr. lt == [EAsync unit pr; Ev 2]))

let test_async_await () =
  assert (
    (let! pr = w_async (w_produce 5) in w_await pr)
    `w_ord`
    encode_pre_post_in_w (fun _ _ -> True) (fun _ _ _ lt _ -> exists pr. lt == [EAsync unit pr; EAwait pr]))

let test_async_ev_await () =
  assert (
    (let! pr = w_async (w_produce 5) in w_produce 0 ;! w_await pr)
    `w_ord`
    encode_pre_post_in_w (fun _ _ -> True) (fun _ _ _ lt _ -> exists pr. lt == [EAsync unit pr; Ev 0; EAwait pr]))

unfold
let f (pr:promise int unit) : w int unit =
  w_await pr ;!
  w_produce 0

unfold
let g () : w int unit =
  let! pr'  = w_async (let! pr = w_async (w_produce (-2)) in f pr) in
  let! pr'' = w_async (w_produce (-1)) in
  w_await pr' ;!
  w_await pr''

let _ =
  assert (
    (let! pr = w_async (w_produce (-2)) in f pr)
    `w_ord`
    encode_pre_post_in_w (fun _ _ -> True) (fun _ _ _ lt _ ->
      exists pr. lt == [EAsync unit pr; EAwait pr; Ev 0])
  )

let _ =
  assert (
    (let! _ = w_async (w_async (w_return int ())) in w_return int ())
    `w_ord`
    encode_pre_post_in_w (fun _ _ -> True) (fun _ _ () lt _ ->
      exists pr. lt == [EAsync (promise int unit) pr])
  )

let _ =
  assert (
    (let! pr = w_async (w_async (w_return int ())) in w_await pr ;! w_return int pr)
    `w_ord`
    encode_pre_post_in_w (fun _ _ -> True) (fun _ _ pr lt _ ->
      lt == [EAsync (promise int unit) pr; EAwait pr])
  )

let _ =
  assert (
    (w_async (let! pr = w_async (w_return int ()) in w_await pr) ;! w_return int ())
    `w_ord`
    encode_pre_post_in_w (fun _ _ -> True) (fun _ _ () lt _ ->
      exists pr'. lt == [EAsync unit pr'])
  )

let _ =
  assert (
    g ()
    `w_ord`
    encode_pre_post_in_w (fun _ _ -> True) (fun _ _ _ lt _ ->
      exists pr' pr''. lt == [EAsync unit pr'; EAsync unit pr''; EAwait pr'; EAwait pr''])
  )
