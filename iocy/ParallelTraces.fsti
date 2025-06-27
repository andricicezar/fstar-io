module ParallelTraces

open FStar.Tactics
open FStar.List.Tot

val promise (e:Type u#0) (a:Type u#0) : Type u#0

noeq
type event (e: Type0) : Type u#1 =
| Ev : e -> event e
| EAsync : b:Type0 -> pr:promise e b -> event e
| EAwait : #b:Type0 -> pr:promise e b -> event e
and atrace e : Type u#1 = list (event e)

type trace e = list e

let suffix_of #e (l1:atrace e) (l2:atrace e) : Type0 = admit ()
let lemma_suffix_of_reflexive #e (l:atrace e) : Lemma (suffix_of l l) [SMTPat (suffix_of l l)] = admit ()
let lemma_suffix_of_transitive #e (l1:atrace e) (l2:atrace e) (l3:atrace e) :
  Lemma (suffix_of l1 l2 /\ suffix_of l2 l3 ==> suffix_of l1 l3)
  [SMTPat (suffix_of l1 l2); SMTPat (suffix_of l2 l3); SMTPat (suffix_of l1 l3)] = ()

val parallel_traces (e:Type0) : Type u#1 (* promise_id -> atrace e *)

val mem (pr:promise 'e 'a) (pts:parallel_traces 'e) : Type0
val sel_lt (pr:promise 'e 'a) (pts:(parallel_traces 'e){pr `mem` pts}) : atrace 'e
val sel_r (pr:promise 'e 'a) (pts:(parallel_traces 'e){pr `mem` pts}) : 'a

let ord #e (pts pts':parallel_traces e) =
  (forall a (x:promise e a). x `mem` pts ==> x `mem` pts') /\
  (forall a (x:promise e a). x `mem` pts ==> (sel_lt x pts' `suffix_of` sel_lt x pts)) /\
  (forall a (x:promise e a). x `mem` pts ==> (sel_r x pts' == sel_r x pts))

let ord_reflexive #e (pts:parallel_traces e) : Lemma (ord pts pts) = ()
let ord_transitive #e (pts pts' pts'':parallel_traces e) :
  Lemma (ord pts pts' /\ ord pts' pts'' ==> ord pts pts'') = ()

val async (r:'a) (lt:atrace 'e) (pts:parallel_traces 'e) :
  prpts':((promise 'e 'a) & (parallel_traces 'e)){
    ~(fst prpts' `mem` pts) /\ pts `ord` (snd prpts') /\
    fst prpts' `mem` snd prpts' /\
    sel_r (fst prpts') (snd prpts') == r /\
    sel_lt (fst prpts') (snd prpts') == lt}

val await (pr:promise 'e 'a) (pts:(parallel_traces 'e){pr `mem` pts}) :
  pts':(parallel_traces 'e){pts `ord` pts' /\ sel_lt pr pts' == []}

let sel_r_async (r:'a) (lt:atrace 'e) (pts:parallel_traces 'e) :
  Lemma (
    let prpts = async r lt pts in
    sel_r (fst prpts) (snd prpts) == r
  )
  [SMTPat (sel_r (fst (async r lt pts)) (snd (async r lt pts)))]
  = ()

let sel_lt_async (r:'a) (lt:atrace 'e) (pts:parallel_traces 'e) :
  Lemma (
    let prpts = async r lt pts in
    sel_lt (fst prpts) (snd prpts) == lt
  )
  [SMTPat (sel_lt (fst (async r lt pts)) (snd (async r lt pts)))]
  = ()

let sel_lt_await_async (r:'a) (lt:atrace 'e) (pts:parallel_traces 'e) :
  Lemma (
    let prpts = async r lt pts in
    sel_lt (fst prpts) (await (fst prpts) (snd prpts)) == []
  )
  [SMTPat (sel_lt (fst (async r lt pts)) (await (fst (async r lt pts)) (snd (async r lt pts))))]
  = ()

// val size : atrace 'e -> nat

val closed_atrace (pts:parallel_traces 'e) (tr:atrace 'e) : Type0 //(decreases (size tr))
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
val closed_atrace_async #e #a h (pts:parallel_traces e) (r:a) lt :
  Lemma
    (requires (closed_atrace pts ((rev lt) @ h)))
    (ensures (
      let (pr, pts') = async r lt pts in
      closed_atrace pts' ((EAsync a pr) :: h)))
    [SMTPat (closed_atrace (snd (async r lt pts)) ((EAsync a (fst (async r lt pts))) :: h))]
//     SMTPat (closed_atrace (snd (async r lt pts)) ([EAsync (fst (async r lt pts)) r lt] @ h));
//     SMTPat (closed_atrace (snd (async r lt pts)) ([EAsync (fst (async r lt pts)) r lt] @ h)) ]

val closed_atrace_await_pr #e #a (pr:promise e a) h pts :
  Lemma
    (requires (closed_atrace pts h))
    (ensures (closed_atrace (await pr pts) ((EAwait pr) :: h)))
    [SMTPat (closed_atrace (await pr pts) ((EAwait pr) :: h))]

val closed_atrace_produce #e (ev:e) h pts :
  Lemma
    (requires (closed_atrace pts h))
    (ensures (closed_atrace pts ((Ev ev) :: h)))
    [SMTPat (closed_atrace pts ((Ev ev) :: h))]

let closed_atrace_append_assoc #e h lt1 lt2 (pts:parallel_traces e) :
  Lemma
    (closed_atrace pts (lt1@(lt2@h)) <==>  closed_atrace pts ((lt1@lt2)@h))
    [SMTPat (closed_atrace pts (lt1@(lt2@h)));
     SMTPat (closed_atrace pts ((lt1@lt2)@h))]
  = append_assoc lt1 lt2 h

let closed_atrace_rev_append #e h lt1 lt2 (pts:parallel_traces e) :
  Lemma
    (closed_atrace pts ((rev (lt1@lt2))@h) <==>  closed_atrace pts ((rev lt2) @ (rev lt1) @ h))
    [SMTPat (closed_atrace pts ((rev (lt1@lt2))@h));
     SMTPat (closed_atrace pts ((rev lt2) @ (rev lt1)@h))]
  = rev_append lt1 lt2

val size_pts : parallel_traces 'e -> nat
val can_progress : pr:promise 'e 'a -> pts:parallel_traces 'e{pr `mem` pts} -> bool
val get_next : #e:_ -> pts:parallel_traces e -> list (a:Type0 & pr:(promise e a){pr `mem` pts /\ can_progress pr pts})
val progress : pr:promise 'e 'a -> pts:(parallel_traces 'e){pr `mem` pts /\ can_progress pr pts} -> 'e * pts':parallel_traces 'e{size_pts pts' < size_pts pts}

let rec interleave_map
  (h:trace 'e)
  (pts: parallel_traces 'e)
  : Tot (list (trace 'e)) (decreases (size_pts pts)) =
  let next : list _ = get_next pts in
  if length next = 0 then [h]
  else begin
    fold_left (@) [] (
      map (fun (apr:(a:Type0 & pr:(promise 'e a){pr `mem` pts /\ can_progress pr pts})) ->
        let (| _, pr |) = apr in
        let (ev, pts') = progress pr pts in
        interleave_map (ev::h) pts') next)
  end
