module ComputationalView

open FStar.Tactics

noeq
type freePure (a:Type) =
| Return : a -> freePure a 
| Require : (pre:Type0) -> (k:unit -> freePure a) -> freePure a

let pure_wp a = (a -> Type0) -> Type0
let pure_wp_return (x:'a) : pure_wp 'a = fun p -> p x
let pure_wp_bind (m:pure_wp 'a) (k:'a -> pure_wp 'b) : pure_wp 'b =
 fun p -> m (fun r -> (k r) p) 
let pure_wp_stronger (wp1 wp2:pure_wp 'a) : Type0 =
  forall p. wp2 p ==> wp1 p

let rec freePure_theta (m:freePure 'a) : pure_wp 'a = 
  match m with
  | Return x -> pure_wp_return x 
  | Require pre k -> pure_wp_bind (fun p -> pre /\ p ()) (fun r -> freePure_theta (k r))

let pureId (a:Type) = a

(** This is possible because Pure has the effect implemented by the Require **)
let rec freePure_to_pureId #a (m:freePure a) (wp:pure_wp a) (post:a -> Type0) :
  Pure (pureId a)
    (requires (freePure_theta m `pure_wp_stronger` wp /\ wp post))
    (ensures post) =
  match m with
  | Return x -> x
  | Require pre k ->
    assert (freePure_theta m post);
    assert (pre);
    assert (freePure_theta (k ()) `pure_wp_stronger` (freePure_theta (k ())));
    assert ((freePure_theta (k())) post);
    freePure_to_pureId (k ()) (freePure_theta (k())) post

assume val state_t:Type0
assume val state_rel : FStar.Preorder.preorder state_t

noeq
type freeState (a:Type) =
| ReturnST : a -> freeState a 
| GetST : (state_t -> freeState a) -> freeState a
| PutST : state_t -> (unit -> freeState a) -> freeState a

let state_wp a = (a -> state_t -> Type0) -> (state_t -> Type0)
let state_wp_return (x:'a) : state_wp 'a = fun p s0 -> p x s0
let state_wp_bind (m:state_wp 'a) (k:'a -> state_wp 'b) : state_wp 'b =
  fun p s0 -> m (fun r s1 -> k r p s1) s0
let state_wp_stronger (wp1 wp2:state_wp 'a) : Type0 =
  forall p s0. wp2 p s0 ==> wp1 p s0

let rec freeState_theta (m:freeState 'a) : state_wp 'a =
  match m with
  | ReturnST x -> state_wp_return x
  | GetST k -> state_wp_bind (fun p s0 -> p s0 s0) (fun r -> freeState_theta (k r))
  | PutST s1 k -> state_wp_bind (fun p s0 -> s0 `state_rel` s1 /\ p () s1) (fun r -> freeState_theta (k r)) (** This enforces monotonicity **)

let state a = state_t -> a * state_t

let rec freeState_to_state #a (m:freeState a) (wp:(state_wp a){freeState_theta m `state_wp_stronger` wp}) (post:(a -> state_t -> Type0)) (s0:state_t{wp post s0}) :
  Tot (r:(a * state_t){post (fst r) (snd r) /\ s0 `state_rel` (snd r)}) =
  match m with
  | ReturnST x -> (x, s0)
  | GetST k ->  freeState_to_state (k s0) (freeState_theta (k s0)) post s0
  | PutST s1 k -> freeState_to_state (k ()) (freeState_theta (k ())) post s1

noeq
type freeMST (a:Type) =
| ReturnMST : a -> freeMST a 
| GetMST : (state_t -> freeMST a) -> freeMST a
| PutMST : state_t -> (unit -> freeMST a) -> freeMST a
| WitnessMST : pred:(state_t -> Type0) -> (unit -> freeMST a) -> freeMST a
| RecallMST : pred:(state_t -> Type0) -> (unit -> freeMST a) -> freeMST a
  
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
let rec freeMST_to_state #a (m:freeMST a) (wp:(state_wp a){freeMST_theta witnessed m `state_wp_stronger` wp}) (post:(a -> state_t -> Type0)) (s0:state_t{wp post s0}) :
  Tot (r:(a * state_t){post (fst r) (snd r)}) =
  match m with
  | ReturnMST x -> (x, s0)
  | GetMST k ->  freeMST_to_state (k s0) (freeMST_theta witnessed (k s0)) post s0
  | PutMST s1 k -> freeMST_to_state (k ()) (freeMST_theta witnessed (k ())) post s1
  | WitnessMST pred k -> 
    assert (pred s0);
    assert (witnessed pred ==> freeMST_theta witnessed (k ()) post s0);
    assume (witnessed pred); (** CA: how to fold witnessed here? **)
    freeMST_to_state (k ()) (freeMST_theta witnessed (k ())) post s0
  | RecallMST pred k -> 
    assert (witnessed pred);
    assume (pred s0); (** CA: how to unfold witnessed here? **)
    freeMST_to_state (k ()) (freeMST_theta witnessed (k ())) post s0


(** ** Attempt at collecting predicates **)

type stable_pred =
  pred:(state_t -> Type0){forall h0 h1. pred h0 /\ h0 `state_rel` h1 ==> pred h1}

module S = FStar.TSet

type statepreds =
  sp:(state_t * S.set stable_pred){forall (pred:stable_pred). pred `S.mem` (snd sp) ==> pred (fst sp)}
  
val witnessed' : (state_t -> Type0) -> Type0
let witnessed' pred = True // i don't have access to the heap

let rec freeMST_to_state' #a (m:freeMST a) (wp:(state_wp a){freeMST_theta witnessed' m `state_wp_stronger` wp}) (post:(a -> state_t -> Type0)) (s0:statepreds{wp post (fst s0)}) :
  Tot (r:(a * statepreds){post (fst r) (fst (snd r))}) =
  match m with
  | ReturnMST x -> (x, s0)
  | GetMST k ->  freeMST_to_state' (k (fst s0)) (freeMST_theta witnessed' (k (fst s0))) post s0
  | PutMST s1 k -> freeMST_to_state' (k ()) (freeMST_theta witnessed' (k ())) post (s1, snd s0)
  | WitnessMST pred k -> 
    assert (pred (fst s0));
    assert (witnessed' pred ==> freeMST_theta witnessed' (k ()) post (fst s0));
    assume (forall h0 h1. pred h0 /\ h0 `state_rel` h1 ==> pred h1); // one has to strengthen the type of witness/recall
    assert (witnessed' pred);
    let lp = S.union (snd s0) (S.singleton pred) in
    assume (forall (pred:stable_pred). pred `S.mem` lp ==> pred (fst s0)); // probably easy to prove by induction;
    freeMST_to_state' (k ()) (freeMST_theta witnessed' (k ())) post (fst s0, lp)
  | RecallMST pred k -> 
    assert (witnessed' pred);
    assume (forall h0 h1. pred h0 /\ h0 `state_rel` h1 ==> pred h1); // one has to strengthen the type of witness/recall
    assume (pred `S.mem` (snd s0));
    assert (pred (fst s0)); (** 
      CA: i need to know here that pred is in the list of predicates.
      In pulse, they have an index that tells them that the predicate is contained **)
    freeMST_to_state' (k ()) (freeMST_theta witnessed' (k ())) post s0







