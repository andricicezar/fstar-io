module ComputationalView

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
assume val state_rel : state_t -> state_t -> Type0

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
  | PutST s1 k -> state_wp_bind (fun p s0 -> s0 `state_rel` s1 /\ p () s1) (fun r -> freeState_theta (k r))

let state a = state_t -> a * state_t

let rec freeState_to_state #a (m:freeState a) (wp:(state_wp a){freeState_theta m `state_wp_stronger` wp}) (post:(a -> state_t -> Type0)) (s0:state_t{wp post s0}) :
  Tot (r:(a * state_t){post (fst r) (snd r)}) =
  match m with
  | ReturnST x -> (x, s0)
  | GetST k ->  freeState_to_state (k s0) (freeState_theta (k s0)) post s0
  | PutST s1 k -> freeState_to_state (k ()) (freeState_theta (k ())) post s1
