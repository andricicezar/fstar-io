module Soundness

open FStar.Tactics

assume val state_t:Type0
assume val state_rel : FStar.Preorder.preorder state_t

type stable_pred =
  pred:(state_t -> Type0){forall h0 h1. pred h0 /\ h0 `state_rel` h1 ==> pred h1}

let state_wp a = (a -> state_t -> Type0) -> (state_t -> Type0)

let state_wp_return (x:'a) : state_wp 'a = fun p s0 -> p x s0
let state_wp_bind (m:state_wp 'a) (k:'a -> state_wp 'b) : state_wp 'b =
  fun p s0 -> m (fun r s1 -> k r p s1) s0
  
let state_wp_stronger (wp1 wp2:state_wp 'a) : Type0 =
  forall p s0. wp2 p s0 ==> wp1 p s0

noeq
type mst_repr (a:Type) =
| Return : a -> mst_repr a 
| Get : (state_t -> mst_repr a) -> mst_repr a
| Put : state_t -> (unit -> mst_repr a) -> mst_repr a
| Witness : pred:stable_pred -> (unit -> mst_repr a) -> mst_repr a
| Recall : pred:stable_pred -> (unit -> mst_repr a) -> mst_repr a
  
let rec theta (witnessed:(state_t -> Type0) -> Type0) (m:mst_repr 'a) : state_wp 'a =
  match m with
  | Return x -> state_wp_return x
  | Get k -> state_wp_bind (fun p s0 -> p s0 s0) (fun r -> theta witnessed (k r))
  | Put s1 k -> state_wp_bind (fun p s0 -> s0 `state_rel` s1 /\ p () s1) (fun r -> theta witnessed (k r))
  | Witness pred k -> state_wp_bind (fun p s0 -> pred s0 /\ (witnessed pred ==> p () s0)) (fun r -> theta witnessed (k r))
  | Recall pred k -> state_wp_bind (fun p s0 -> witnessed pred /\ (pred s0 ==> p () s0)) (fun r -> theta witnessed (k r))

module S = FStar.TSet

let rec witnessed_before #a (over:S.set stable_pred) (m:mst_repr a) : Tot Type0 (decreases m) =
  match m with
  | Return _ -> True
  | Get k -> forall s . over `witnessed_before` (k s)
  | Put s1 k -> over `witnessed_before` (k ())
  | Witness pred k -> (S.union over (S.singleton pred)) `witnessed_before` (k ())
  | Recall pred k -> pred `S.mem` over /\ over `witnessed_before` (k ())

type state_w_preds =
  sp:(state_t * S.set stable_pred){forall (pred:stable_pred). pred `S.mem` (snd sp) ==> pred (fst sp)}
  
val witnessed_trivial : (state_t -> Type0) -> Type0
let witnessed_trivial pred = True // trivial instance of witnessed tokens

let rec run_mst_with_preds #a 
  (m:mst_repr a) 
  (wp:(state_wp a){theta witnessed_trivial m `state_wp_stronger` wp}) 
  (post:(a -> state_t -> Type0)) 
  (s0:state_w_preds{wp post (fst s0) /\ (snd s0) `witnessed_before` m}) 
: Tot (r:(a * state_w_preds){post (fst r) (fst (snd r))}) 
=
  match m with
  | Return x -> (x, s0)
  | Get k -> run_mst_with_preds (k (fst s0)) (theta witnessed_trivial (k (fst s0))) post s0
  | Put s1 k -> run_mst_with_preds (k ()) (theta witnessed_trivial (k ())) post (s1, snd s0)
  | Witness pred k -> 
    let lp = S.union (snd s0) (S.singleton pred) in
    run_mst_with_preds (k ()) (theta witnessed_trivial (k ())) post (fst s0, lp)
  | Recall pred k -> 
    run_mst_with_preds (k ()) (theta witnessed_trivial (k ())) post s0

let run_mst #a 
  (m:mst_repr a{S.empty `witnessed_before` m}) 
  (wp:(state_wp a){theta witnessed_trivial m `state_wp_stronger` wp}) 
  (post:(a -> state_t -> Type0)) 
  (s0:state_t{wp post s0}) 
: Tot (r:(a * state_t){post (fst r) (snd r)}) 
=
  let (r, s1p) = run_mst_with_preds m wp post (s0, S.empty) in
  (r, fst s1p)

let soundness_with_preds #a (m:mst_repr a) (wp:state_wp a) (preds:S.set stable_pred) 
: Lemma
    (requires ((forall witnessed. theta witnessed m `state_wp_stronger` wp) /\ preds `witnessed_before` m))
    (ensures  (forall post s0. wp post s0 /\ (forall (pred:stable_pred). pred `S.mem` preds ==> pred s0) ==> 
                            (let (r,s1p) = run_mst_with_preds m wp post (s0, preds) in post r (fst s1p)))) 
=
  () 

let soundness_whole_program #a (m:mst_repr a) (wp:state_wp a) 
: Lemma 
    (requires ((forall witnessed. theta witnessed m `state_wp_stronger` wp) /\ S.empty `witnessed_before` m)) 
    (ensures  (forall post s0. wp post s0 ==> (let (r,s1) = run_mst m wp post s0 in post r s1))) 
=
  ()

let _ = soundness_whole_program (Return 5) (state_wp_return 5) 
let _ = soundness_whole_program (Witness (fun _ -> 6 == 6) Return) (state_wp_return ())
let _ = soundness_whole_program (Witness (fun _ -> 6 == 6) (fun () -> Recall (fun _ -> 6 == 6) Return)) (state_wp_return ())

[@expect_failure]
let _ = soundness_whole_program (Recall (fun _ -> 6 == 6) Return) (state_wp_return ())

let test x y = soundness_whole_program (Witness (fun _ -> x < y) (fun () -> Recall (fun _ -> x < y) Return)) (fun p s0 -> x < y /\ p () s0)

[@expect_failure]
let test2 x y = soundness_whole_program (Witness (fun _ -> x < y) (fun () -> Recall (fun _ -> x > 5) Return)) (fun p s0 -> x < y /\ p () s0)

[@expect_failure]
let test2' x y = assert (S.empty `witnessed_before` (Witness (fun _ -> x < y) (fun () -> Recall (fun _ -> x > 5) Return)))

let test2'' x y = assert ((S.singleton #stable_pred (fun _ -> x > 5)) `witnessed_before` (Witness (fun _ -> x < y) (fun () -> Recall (fun _ -> x > 5) Return)))
