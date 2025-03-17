module FancyTraces_Async_Await

open FStar.Tactics
open FStar.List.Tot.Base
open FStar.Classical.Sugar

type w_post #e (a:Type) = e -> a -> Type0
type w_pre #e = e -> Type0
type w0 #e (a:Type) = w_post #e a -> w_pre #e
unfold
let w_post_ord (#e:Type) (#a:Type) (p1 p2:w_post #e a) = forall lt (r:a). p1 lt r ==> p2 lt r

let w_monotonic (#e:Type) (#a:Type) (wp:w0 #e a) =
  forall (p1 p2:w_post a). (p1 `w_post_ord` p2) ==> (forall h. wp p1 h ==> wp p2 h)

type w (#e:Type) (a:Type) = wp:(w0 #e a){w_monotonic wp}

#push-options "--__no_positivity"
noeq
type event (e: Type0) =
| Ev : e -> event e
| EAsync : nat -> b:Type0 -> w #(list (event e)) b -> event e
| EAwait : nat -> event e
#pop-options

(** Waiting twice for the same await
let ex1 =
  let p1 = async (fun () -> print 0) in {{ [0] }}
  await p1;
  print 1;
  await p1;
  {{ [0;1] }}
**)

(** Transitive await
let ex2 =
  let p1 = async (fun () -> print 0) in
  let p2 = async (fun () -> await p1) in {{ Await p1 }}
  await p2;
  print 1;
  await p1;
  {{ [0;1] }}
**)

(** Higher-order promise -- TODO: check if universes allow us to have higher-order promises
let ex3 =
  let p1 = async (fun () -> async (fun () -> print 0)) in
  let p2 = await p1 in
  print 1;
  await p2;
  {{ [0;1];[1;0] }}
**)

(** Unawaited events
let ex3 =
  let p1 = async (fun () ->
      let _ = async (fun () -> print 0) in
      print 1) in
  await p1;
  print 2;
  {{ [1;2];[0;1;2];[1;0;2];[1;2;0] }}
**)
