module FancyTraces2

open FStar.Tactics

open FStar.List.Tot

(**
val rev_append: l1:list 'a -> l2:list 'a ->
  Lemma (requires True)
        (ensures ((rev (l1@l2)) == ((rev l2)@(rev l1))))
  [SMTPat (rev (l1@l2))]**)

val promise (e:Type u#0) (a:Type u#0) : Type u#0

noeq
type event (e: Type0) : Type u#1 =
| Ev : e -> event e
| EAsync : b:Type0 -> pr:promise e b -> event e
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
  (forall a (x:promise e a). x `mem` pts ==> (sel_lt x pts' `suffix_of` sel_lt x pts)) /\
  (forall a (x:promise e a). x `mem` pts ==> (sel_r x pts' == sel_r x pts))

let ord_reflexive #e (pts:parallel_traces e) : Lemma (ord pts pts) = ()
let ord_transitive #e (pts pts' pts'':parallel_traces e) :
  Lemma (ord pts pts' /\ ord pts' pts'' ==> ord pts pts'') = ()

val async (r:'a) (lt:atrace 'e) (pts:parallel_traces 'e) :
  prpts':((promise 'e 'a) & (parallel_traces 'e)){
    ~(fst prpts' `mem` pts) /\ pts `ord` (snd prpts') /\
    fst prpts' `mem` snd prpts' /\ sel_r (fst prpts') (snd prpts') == r /\ sel_lt (fst prpts') (snd prpts') == lt}

(**
val lemma_async (r:'a) (lt:atrace 'e) (pts:parallel_traces 'e) :
  Lemma (
    let prpts' = async r lt pts in
    ~(fst prpts' `mem` pts) /\ pts `ord` (snd prpts') /\
    fst prpts' `mem` snd prpts' /\ sel_r (fst prpts') (snd prpts') == r /\ sel_lt (fst prpts') (snd prpts') == lt)
  [SMTPat (fst (async r lt pts) `mem` pts);
   SMTPat (pts `ord` (snd (async r lt pts)));
   SMTPat (fst (async r lt pts) `mem` snd (async r lt pts));
   SMTPat (sel_r (fst (async r lt pts)) (snd (async r lt pts)));
   SMTPat (sel_lt (fst (async r lt pts)) (snd (async r lt pts)))]
**)

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
      closed_atrace pts' ((rev lt) @ h)
  } -> Type0

let w e a = h:atrace e -> pts:parallel_traces e{closed_atrace pts h} -> w_post e a h pts -> Type0

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
let w_return e #a (x:a) : w e a =
  fun h pts p -> p x [] pts

unfold
let w_bind #e #a #b (m:w e a) (f: a -> w e b) : w e b =
  fun h pts post ->
    m h pts (fun r' lt' pts' ->
        f r' ((rev lt')@h) pts' (fun r'' lt'' pts'' ->
        post r'' (lt'@lt'') pts''))

unfold
let w_async #e #a (wf:w e a) : w e (promise e a) =
  fun h pts post ->
    (** CA: should wf get any pts' that extends pts? *)
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

#push-options "--fuel 100 --z3rlimit 100"
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

let stupid_lemma (e1 e2:'a) : Lemma ([e1]@[e2] == [e1;e2]) = ()

let _ =
  assert (
    (let! pr = w_async (w_async (w_return int ())) in w_await pr ;! w_return int pr)
    `w_ord`
    encode_pre_post_in_w (fun _ _ -> True) (fun _ _ pr lt _ ->
      lt == [EAsync (promise int unit) pr; EAwait pr])
  )
  by (
    norm [delta_only [`%encode_pre_post_in_w; `%w_ord];iota];
    norm [delta_only [`%w_async;`%w_produce;`%w_await;`%w_bind;`%op_let_Bang;`%w_return];iota];
    let h = forall_intro () in
    let pts = forall_intro () in
    let post = forall_intro () in
    let hyp = implies_intro () in
    (**
    let (_, hyp') = destruct_and hyp in
    clear hyp;
    FStar.Tactics.V1.Logic.split ();
    bump_nth 2;
    simpl ();
    let hyp = instantiate hyp' (fresh_uvar None) in clear hyp';
    let hyp' = instantiate hyp (fresh_uvar None) in clear hyp;
    let hyp = instantiate hyp' (fresh_uvar None) in clear hyp';
    mapply hyp;
    clear hyp;
    l_to_r [`sel_r_async];
    l_to_r [`stupid_lemma];
    tadmit ();
    tadmit ();**)
    // witness (`(fst (async (fst (async () [] (`#pts)))
    //               [EAsync unit (fst (async () [] (`#pts)))]
    //               (snd (async () [] (`#pts))))));
    dump "H")

let _ =
  assert (
    (w_async (let! pr = w_async (w_return int ()) in w_await pr) ;! w_return int ())
    `w_ord`
    encode_pre_post_in_w (fun _ _ -> True) (fun _ _ () lt _ ->
      exists pr pr'. lt == [EAsync pr' () [EAsync pr () []; EAwait pr]])
  )
  by (
    norm [delta_only [`%encode_pre_post_in_w; `%w_ord];iota];
    norm [delta_only [`%w_async;`%w_produce;`%w_await;`%w_bind;`%op_let_Bang;`%w_return];iota];
    let h = forall_intro () in
    let pts = forall_intro () in
    let post = forall_intro () in
    let hyp = implies_intro () in
    let (_, hyp') = destruct_and hyp in
    clear hyp;
    FStar.Tactics.V1.Logic.split ();
    bump_nth 2;
    simpl ();
    dump "H")

let _ =
  assert (
    g ()
    `w_ord`
    encode_pre_post_in_w (fun _ _ -> True) (fun _ _ _ lt _ ->
      exists pr' pr pr''. lt == [EAsync pr' () [EAsync pr () [Ev (-2)]; EAwait pr; Ev 0]; EAsync pr'' () [Ev (-1)]; EAwait pr'; EAwait pr''])
  )
  by (
    norm [delta_only [`%encode_pre_post_in_w; `%w_ord;`%g];iota];
    norm [delta_only [`%w_async;`%w_produce;`%w_await;`%w_bind;`%op_let_Bang];iota];
    let h = forall_intro () in
    let pts = forall_intro () in
    let post = forall_intro () in
    let hyp = implies_intro () in
    let (_, hyp') = destruct_and hyp in
    clear hyp;
    simpl ();
    let hyp = instantiate hyp' (`()) in
    clear hyp';
    dump "H")
#pop-options
