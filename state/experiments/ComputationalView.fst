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
