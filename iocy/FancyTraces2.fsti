module FancyTraces2

open FStar.Tactics
open FStar.List.Tot

val promise (e:Type u#a) (a:Type u#b) : Type u#(max a b)

noeq
type event (e: Type0) : Type u#1 =
| Ev : e -> event e
| EAsync : #b:Type0 -> pr:promise e b -> r:b -> lt:atrace e -> event e
| EAwait : #b:Type0 -> pr:promise e b -> event e
and atrace e : Type u#1 = list (event e)

type trace e = list e

val suffix_of : atrace 'e -> atrace 'e -> Type0
val lemma_suffix_of_reflexive : l:atrace 'e -> Lemma (suffix_of l l) [SMTPat (suffix_of l l)]
val lemma_suffix_of_transitive :
  l1:atrace 'e -> l2:atrace 'e -> l3:atrace 'e ->
  Lemma (suffix_of l1 l2 /\ suffix_of l2 l3 ==> suffix_of l1 l3)
  [SMTPat (suffix_of l1 l2); SMTPat (suffix_of l2 l3); SMTPat (suffix_of l1 l3)]

val parallel_traces (e:Type0) : Type u#1 (* promise_id -> atrace e *)

val mem (pr:promise 'e 'a) (pts:parallel_traces 'e) : Type0
val sel_lt (pr:promise 'e 'a) (pts:(parallel_traces 'e){pr `mem` pts}) : atrace 'e
val sel_r (pr:promise 'e 'a) (pts:(parallel_traces 'e){pr `mem` pts}) : 'a


let ord #e (pts pts':parallel_traces e) =
  (forall a (x:promise e a). x `mem` pts ==> x `mem` pts') /\
  (forall a (x:promise e a). x `mem` pts ==> (sel_lt x pts' `suffix_of` sel_lt x pts))

let ord_reflexive #e (pts:parallel_traces e) : Lemma (ord pts pts) = ()
let ord_transitive #e (pts pts' pts'':parallel_traces e) :
  Lemma (ord pts pts' /\ ord pts' pts'' ==> ord pts pts'') = ()

val insert (r:'a) (lt:atrace 'e) (pts:parallel_traces 'e) :
  pr:(promise 'e 'a){~(pr `mem` pts)}
  &
  pts':(parallel_traces 'e){pts `ord` pts'} // /\ pr `mem` pts' /\ sel pr pts' == lt}

val await_pr (pr:promise 'e 'a) (pts:(parallel_traces 'e){pr `mem` pts}) :
  pts':(parallel_traces 'e){pts `ord` pts'}

// val size : atrace 'e -> nat

val closed_atrace (pts:parallel_traces 'e) (tr:atrace 'e) : GTot Type0 //(decreases (size tr))
  // match tr with
  // | [] -> True
  // | Ev _ :: tl ->
  //   assume (size tl < size tr);
  //   closed_atrace m tl
  // | EAwait #_ #b pr :: tl ->
  //   assume (size tl < size tr);
  //   pr `mem` m /\ closed_atrace m tl
  // | EAsync pr lt :: tl ->
  //   assume (size lt < size tr);
  //   assume (size (lt@tl) < size tr);
  //   closed_atrace m lt /\ (** the new thread can await on existing promises *)
  //   closed_atrace (dsnd (insert pr lt m)) (lt@tl) (** the parent thread can await on the promise of the kid
  //                                              and promises returned/created by the kid *)

val closed_atrace_insert #e #a h (pts:parallel_traces e) (r:a) lt :
  Lemma
    (requires (closed_atrace pts (h@lt)))
    (ensures (
      let (| pr, pts' |) = insert r lt pts in
      closed_atrace pts' (h @ [EAsync pr r lt])))

val closed_atrace_await_pr #e #a (pr:promise e a) h pts :
  Lemma
    (requires (closed_atrace pts h))
    (ensures (closed_atrace (await_pr pr pts) (h @ [EAwait pr])))

val closed_atrace_produce #e (ev:e) h pts :
  Lemma
    (requires (closed_atrace pts h))
    (ensures (closed_atrace pts (h @ [Ev ev])))

// val interleave_map
//   (pts: parallel_traces 'e)
//   (#_: squash (forall a (pr:promise 'e a). pr `mem` pts ==> closed_atrace pts (sel pr pts)))
//   : list (trace 'e)

let w_pre e = h:atrace e -> pts:parallel_traces e{
  closed_atrace pts h
  // /\ (forall pr. pr `mem` pts ==> (sel pr pts) `suffix_of` pr.lt)
  // we cannot have this refinement since we don't store the trace on the promise anymore
} -> Type0

let w_post e a h pts =
  a -> lt:atrace e -> pts':parallel_traces e{
      pts `ord` pts' /\
      closed_atrace pts' (h @ lt)
  } -> Type0

let w e a = h:atrace e -> pts:parallel_traces e{closed_atrace pts h} -> w_post e a h pts -> Type0

let w_ord #e #a (w1 w2:w e a) =
  forall h pts post. w2 h pts post ==> w1 h pts post

let encode_pre_post_in_w #e #a
  (pre:w_pre e)
  (post:(h:atrace e -> pts:parallel_traces e -> w_post e a h pts))
  : w e a
  = (fun h pts p -> pre h pts /\ (forall r' lt' pts'. post h pts r' lt' pts' ==> p r' lt' pts'))

let w_return e #a (x:a) : w e a =
  fun h pts p -> p x [] pts

let w_bind #e #a #b (m:w e a) (f: a -> w e b) : w e b =
  fun h pts post ->
    m h pts (fun r' lt' pts' ->
        f r' (h@lt') pts' (fun r'' lt'' pts'' ->
        append_assoc h lt' lt'';
        post r'' (lt'@lt'') pts''))

let w_async #e #a (wf:w e a) : w e (promise e a) =
  fun h pts post ->
    wf h pts (fun r' lt' pts' ->
      let prpts'' = insert r' lt' pts' in
      closed_atrace_insert h pts' r' lt';
      post (dfst prpts'') [EAsync (dfst prpts'') r' lt'] (dsnd prpts''))

let w_await #e #a (pr:promise e a) : w e a =
  fun h pts post ->
    pr `mem` pts /\
    (closed_atrace_await_pr pr h pts;
    post (sel_r pr pts) [EAwait pr] (await_pr pr pts))

let w_produce #e (ev:e) : w e unit =
  fun h pts post ->
    closed_atrace_produce ev h pts;
    post () [Ev ev] pts

let (let!) = w_bind

let f (pr:promise int unit) : w int unit =
  w_await pr ;!
  w_produce 0

let g () : w int unit =
  let! pr'  = w_async (let! pr = w_async (w_produce (-2)) in f pr) in
  let! pr'' = w_async (w_produce (-1)) in
  w_await pr' ;!
  w_await pr''

let _ =
  assert (
    g ()
    `w_ord`
    encode_pre_post_in_w (fun _ _ -> True) (fun _ _ _ lt _ -> exists pr' lt' pr''. lt == [EAsync pr' () lt'; EAsync pr'' () [Ev (-1)]; EAwait pr'; EAwait pr''])
  ) by (
    norm [delta_only [`%encode_pre_post_in_w; `%w_ord;`%g];iota];
    let h = forall_intro () in
    let pts = forall_intro () in
    let post = forall_intro () in
    let hyp = implies_intro () in
    let (_, hyp') = destruct_and hyp in
    clear hyp;
    norm [delta_only [`%w_async;`%w_produce;`%w_await;`%w_bind];iota];
    simpl ();
    dump "H")
