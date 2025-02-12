module ComputationalView

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

let state a = state_t -> a * state_t

noeq
type freeMST (a:Type) =
| ReturnMST : a -> freeMST a 
| GetMST : (state_t -> freeMST a) -> freeMST a
| PutMST : state_t -> (unit -> freeMST a) -> freeMST a
| WitnessMST : pred:stable_pred -> (unit -> freeMST a) -> freeMST a
| RecallMST : pred:stable_pred -> (unit -> freeMST a) -> freeMST a
  
let rec freeMST_theta (witnessed:(state_t -> Type0) -> Type0) (m:freeMST 'a) : state_wp 'a =
  match m with
  | ReturnMST x -> state_wp_return x
  | GetMST k -> state_wp_bind (fun p s0 -> p s0 s0) (fun r -> freeMST_theta witnessed (k r))
  | PutMST s1 k -> state_wp_bind (fun p s0 -> s0 `state_rel` s1 /\ p () s1) (fun r -> freeMST_theta witnessed (k r))
  | WitnessMST pred k -> state_wp_bind (fun p s0 -> pred s0 /\ (witnessed pred ==> p () s0)) (fun r -> freeMST_theta witnessed (k r))
  | RecallMST pred k -> state_wp_bind (fun p s0 -> witnessed pred /\ (pred s0 ==> p () s0)) (fun r -> freeMST_theta witnessed (k r))
 
assume val witnessed : (state_t -> Type0) -> Type0
//let witnessed = fun pred -> exists s0. pred s0

(** Theorem 5.4 in recalling a witness **)
let rec general_idea_freeMST_to_state #a (m:freeMST a) (wp:(state_wp a){freeMST_theta witnessed m `state_wp_stronger` wp}) (post:(a -> state_t -> Type0)) (s0:state_t{wp post s0}) :
  Tot (r:(a * state_t){post (fst r) (snd r)}) =
  match m with
  | ReturnMST x -> (x, s0)
  | GetMST k ->  general_idea_freeMST_to_state (k s0) (freeMST_theta witnessed (k s0)) post s0
  | PutMST s1 k -> general_idea_freeMST_to_state (k ()) (freeMST_theta witnessed (k ())) post s1
  | WitnessMST pred k -> 
    assert (pred s0);
    assert (witnessed pred ==> freeMST_theta witnessed (k ()) post s0);
    assume (witnessed pred); (** CA: how to fold witnessed here? **)
    general_idea_freeMST_to_state (k ()) (freeMST_theta witnessed (k ())) post s0
  | RecallMST pred k -> 
    assert (witnessed pred);
    assume (pred s0); (** CA: how to unfold witnessed here? **)
    general_idea_freeMST_to_state (k ()) (freeMST_theta witnessed (k ())) post s0


(** ** Attempt at collecting predicates **)

module S = FStar.TSet

type statepreds =
  sp:(state_t * S.set stable_pred){forall (pred:stable_pred). pred `S.mem` (snd sp) ==> pred (fst sp)}
  
val witnessed' : (state_t -> Type0) -> Type0
let witnessed' pred = True // i don't have access to the heap // DA: this looks very fishy
                                                           //     with this definition witnessed plays no real role below
                                                           //     the proof below just relies on recursively calculating which predicates have to hold for recalls to be "typeable" 

let rec closed_preds #a (m:freeMST a) (over:S.set stable_pred) : Type0 =
  match m with
  | ReturnMST _ -> True
  | GetMST k -> forall s. closed_preds (k s) over
  | PutMST s1 k -> closed_preds (k ()) over
  | WitnessMST pred k -> closed_preds (k ()) (S.union over (S.singleton pred))
  | RecallMST pred k -> pred `S.mem` over /\ closed_preds (k ()) over

let rec collect_preds_freeMST_to_state #a (m:freeMST a) (wp:(state_wp a){freeMST_theta witnessed' m `state_wp_stronger` wp}) (post:(a -> state_t -> Type0)) (s0:statepreds{wp post (fst s0) /\ closed_preds m (snd s0)}) :
  Tot (r:(a * statepreds){post (fst r) (fst (snd r))}) =
  match m with
  | ReturnMST x -> (x, s0)
  | GetMST k ->  collect_preds_freeMST_to_state (k (fst s0)) (freeMST_theta witnessed' (k (fst s0))) post s0
  | PutMST s1 k -> collect_preds_freeMST_to_state (k ()) (freeMST_theta witnessed' (k ())) post (s1, snd s0)
  | WitnessMST pred k -> 
    assert (pred (fst s0));
    assert (witnessed' pred ==> freeMST_theta witnessed' (k ()) post (fst s0));
    assert (witnessed' pred);
    let lp = S.union (snd s0) (S.singleton pred) in
    assert (forall (pred:stable_pred). pred `S.mem` lp ==> pred (fst s0));
    collect_preds_freeMST_to_state (k ()) (freeMST_theta witnessed' (k ())) post (fst s0, lp)
  | RecallMST pred k -> 
    assert (witnessed' pred);
    assert (pred (fst s0));
    collect_preds_freeMST_to_state (k ()) (freeMST_theta witnessed' (k ())) post s0

let freeMST_to_state #a (m:freeMST a{closed_preds m S.empty}) (wp:(state_wp a){freeMST_theta witnessed' m `state_wp_stronger` wp}) (post:(a -> state_t -> Type0)) (s0:state_t{wp post s0}) :
  Tot (r:(a * state_t){post (fst r) (snd r)}) =
  let (r, s1p) = collect_preds_freeMST_to_state m wp post (s0, S.empty) in
  (r, fst s1p)

let soundness_pprog #a (m:freeMST a) (wp:state_wp a) (preds:S.set stable_pred) :
  Lemma
    (requires ((forall wit. freeMST_theta wit m `state_wp_stronger` wp) /\ closed_preds m preds))
    (ensures (forall post s0. wp post s0 /\ (forall (pred:stable_pred). pred `S.mem` preds ==> pred s0) ==> (let (r,s1p) = collect_preds_freeMST_to_state m wp post (s0, preds) in post r (fst s1p)))) =
    () 

let soundness_whole #a (m:freeMST a) (wp:state_wp a) :
  Lemma
    (requires ((forall wit. freeMST_theta wit m `state_wp_stronger` wp) /\ closed_preds m S.empty)) // the second conjuct requires that witnessed is not used in the pre-condition
    (ensures (forall post s0. wp post s0 ==> (let (r,s1) = freeMST_to_state m wp post s0 in post r s1))) =
  () // soundness_pprogram #a m wp S.empty

(** CA: my interpretation of this result is the following:
    Given a M, a WP, and a proof that M satisfies WP for abstract Witnessed,
    Then, starting from the pre-condition, one can prove the post-condition,
    by forgetting about Witnessed and only collect the predicates when they get witnessed.
    
    This works because I know that a predicate holds when it is witnessed,
    given by the fact that M satisfies WP.
**)

let _ = soundness_whole (ReturnMST 5) (state_wp_return 5) 
let _ = soundness_whole (WitnessMST (fun _ -> 6 == 6) ReturnMST) (state_wp_return ())
let _ = soundness_whole (WitnessMST (fun _ -> 6 == 6) (fun () -> RecallMST (fun _ -> 6 == 6) ReturnMST)) (state_wp_return ())
[@expect_failure]
let _ = soundness_whole (RecallMST (fun _ -> 6 == 6) ReturnMST) (state_wp_return ())

let test x y = soundness_whole (WitnessMST (fun _ -> x < y) (fun () -> RecallMST (fun _ -> x < y) ReturnMST)) (fun p s0 -> x < y /\ p () s0)

[@expect_failure]
let test2 x y = soundness_whole (WitnessMST (fun _ -> x < y) (fun () -> RecallMST (fun _ -> x > 5) ReturnMST)) (fun p s0 -> x < y /\ p () s0)
[@expect_failure]
let test2' x y = assert (closed_preds (WitnessMST (fun _ -> x < y) (fun () -> RecallMST (fun _ -> x > 5) ReturnMST)) S.empty)
let test2'' x y = assert (closed_preds (WitnessMST (fun _ -> x < y) (fun () -> RecallMST (fun _ -> x > 5) ReturnMST)) (S.singleton #stable_pred (fun _ -> x > 5)))
