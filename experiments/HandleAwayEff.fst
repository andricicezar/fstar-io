module HandleAwayEff

open FStar.Monotonic.Pure

open FStar.Tactics
open FStar.Tactics.Typeclasses

assume type beta : Type u#0

let pure_wp (a: Type) = wp:pure_wp' a{pure_wp_monotonic0 a wp}

let pure_return (x:'a) : pure_wp 'a =
  pure_return 'a x

let pure_bind (m:pure_wp 'a) (k:'a -> pure_wp 'b) : pure_wp 'b =
  FStar.Monotonic.Pure.elim_pure_wp_monotonicity_forall ();
  pure_bind_wp _ _ (as_pure_wp m) (fun x -> as_pure_wp (k x))
  
(** *** Source monad : a Dijkstra Monad **)
noeq
type free_req (a:Type u#a) : Type u#(a+1) = 
| Return : a -> free_req a
| Op : (beta -> free_req a) -> free_req a
| Require : (pre:pure_pre) -> cont:((squash pre) -> free_req a) -> free_req a

let rec theta (m:free_req 'a) : pure_wp 'a =
  match m with
  | Return x -> pure_return x
  | Op k ->
    pure_bind (fun p -> forall x. p x) (fun x -> theta (k x))
  | Require pre k -> pure_bind (fun p -> pre /\ p (() <: squash pre)) (fun r -> theta (k r))

let dm (a:Type) (wp:pure_wp a) =
  m:(free_req a){forall p. wp p ==> theta m p}

let dm_return (x:'a) : dm 'a (pure_return x) = Return x

let dm_bind (#a:Type u#a) (#b:Type u#b) (#wp1:pure_wp a) (#wp2:a -> pure_wp b)
  (m:dm a wp1)
  (k:(x:a -> dm b (wp2 x))) :
  dm b (pure_bind wp1 wp2) =
  admit ()

let dm_subcomp (#a:Type u#a) (#wp1:pure_wp a) (#wp2:pure_wp a) (m:dm a wp1) : Pure (dm a wp2) (requires (forall p. wp2 p ==> wp1 p)) (ensures fun _ -> True) = m

class source (t:Type) = { [@@@no_method] _empty : unit }

instance source_int : source int = { _empty = () }

instance source_pair (t1:Type) {| source t1 |} (t2:Type) {| source t2 |} : source (t1 * t2) = { _empty = () }

instance source_arrow
  (t1:Type) {| source t1 |}
  (t2:t1 -> Type) {| (x:t1) -> source (t2 x) |}
  (wp:(x:t1) -> pure_wp (t2 x)) : 
  source (x:t1 -> dm (t2 x) (wp x)) = { _empty = () }

let test0 : source (x:int -> dm int (as_pure_wp (fun p -> x > 5 /\ (forall r. p r)))) =
  source_arrow int (fun _ -> int) (fun x -> (as_pure_wp (fun p -> x > 5 /\ (forall r. p r))))

let test1 : source (x:int -> dm (y:int -> dm int (fun p -> x == y /\ (forall r. p r))) (fun p -> x > 5 /\ (forall r. p r))) =
  source_arrow
    int _ #(fun x -> source_arrow int (fun _ -> int)
    (fun y -> as_pure_wp (fun p -> x == y /\ (forall r. p r))))
    (fun x -> as_pure_wp (fun p -> x > 5 /\ (forall r. p r)))

let test2 : source ((y:int -> dm int (fun p -> y > 2 /\ (forall r. p r))) -> dm int (fun p -> (forall r. p r))) =
  source_arrow
    _ #(source_arrow int (fun _ -> int) (fun y p -> y > 2 /\ (forall r. p r)))
    (fun _ -> int)
    (fun _ p -> (forall r. p r))

(** *** Target monad : a Free Monad with less constructors **)
noeq
type free (a:Type u#a) : Type u#a =
| Call : (beta -> free a) -> free a
| Ret : a -> free a

let free_return (x:'a) : free 'a = Ret x

let rec free_bind (m:free 'a) (k:'a -> free 'b) : free 'b =
  match m with
  | Ret x -> k x
  | Call cont -> Call (fun b -> free_bind (cont b) k)

class target (t:Type) = { [@@@no_method] _empty : unit }

instance target_int : target int = { _empty = () }

instance target_pair (t1:Type) {| target t1 |} (t2:Type) {| target t2 |} : target (t1 * t2) = { _empty = () }

instance target_arrow (t1:Type) {| target t1 |} (t2:Type) {| target t2 |} : target (x:t1 -> free t2) = { _empty = () }

(** *** Semantics **)
let behS (m:dm 'a 'wp) = theta m
let rec behT (m:free 'a) : pure_wp 'a = 
  match m with
  | Ret x -> pure_return x
  | Call k ->
    pure_bind (fun p -> forall x. p x) (fun x -> behT (k x))

let eq_beh (rel:'a -> 'b -> Type0) (w1:pure_wp 'a) (w2:pure_wp 'b): Type0 =
  forall p1 p2. (forall r1 r2. r1 `rel` r2 ==> (p1 r1 <==> p2 r2)) ==> (w1 p1 <==> w2 p2)
// TODO: figure out how to define this equivalence


let rec lift_m (m:free 'a) : dm 'a (fun p -> forall r. p r) =
  match m with
  | Ret x -> Return x
  | Call k -> Op (fun x -> lift_m (k x))

let rec handle_m (m:dm 'a (fun p -> forall r. p r)) : free 'a =
  match m with
  | Return x -> Ret x
  | Require pre k -> begin
    assert (theta m (fun r -> True));
    assert (pre);
    handle_m (k ())
  end
  | Op k -> Call (fun x -> handle_m (k x))

(** *** Type class: Lift **)
class liftable (t:Type u#a) = {
  [@@@no_method]
  t_tc : target t;
  [@@@no_method]
  s : Type u#b;
  [@@@no_method]
  s_tc : source s;

  lift : t -> s;

  lem1 : w:free t -> rel:(t -> s -> Type0) -> Lemma ((behT w) `eq_beh rel` (behS (dm_bind (lift_m w) (fun r -> dm_return (lift r)))))
}

class handleable (t:Type u#a) = {
  [@@@no_method]
  t_tc : target t;

  [@@@no_method]
  s : Type u#b;
  [@@@no_method]
  s_tc : source s;

  handle : s -> t;
}

instance liftable_int : liftable int = {
  t_tc = solve;
  s = int;
  s_tc = solve;

  lift = (fun x -> x);
  lem1 = (fun x rel -> admit ())
}

instance liftable_pair (t1 t2:Type) {| c1:liftable t1 |} {| c2:liftable t2 |} : liftable (t1 * t2) = {
  t_tc = target_pair t1 #c1.t_tc t2 #c2.t_tc; 
  s = c1.s * c2.s;
  s_tc = source_pair c1.s #c1.s_tc c2.s #c2.s_tc;

  lift = (fun (x, y) -> (lift x, lift y));
  lem1 = (fun x rel -> admit ())
}

instance liftable_arrow (t1 t2:Type) {| c1:handleable t1 |} {| c2:liftable t2 |} : liftable (t1 -> free t2) = {
  t_tc = target_arrow t1 #c1.t_tc t2 #c2.t_tc;
  s = c1.s -> dm c2.s (fun p -> forall r. p r);
  s_tc = source_arrow c1.s #c1.s_tc (fun _ -> c2.s) #(fun _ -> c2.s_tc) (fun x p -> forall r. p r);

  lift = (fun (f:t1 -> free t2) (x:c1.s) -> 
    dm_bind (lift_m #t2 (f (handle x))) (fun (r:t2) -> dm_return (c2.lift r))
  );
  lem1 = (fun x rel -> admit ())
}

instance handleable_int : handleable int = {
  t_tc = solve;
  s = int;
  s_tc = solve;

  handle = (fun x -> x);
}

instance handleable_arrow (t1 t2:Type) {| c1:liftable t1 |} {| c2:handleable t2 |} : handleable (t1 -> free t2) = {
  t_tc = target_arrow t1 #c1.t_tc t2 #c2.t_tc;
  s = c1.s -> dm c2.s (fun p -> forall r. p r);
  s_tc = source_arrow c1.s #c1.s_tc (fun _ -> c2.s) #(fun _ -> c2.s_tc) (fun x p -> forall r. p r);

  handle = (fun f (x:t1) ->
    free_bind (handle_m (f (lift x))) (fun r -> free_return (c2.handle r))
  )
}

let sc (ps:(int -> dm int (fun p -> forall r. p r)) -> dm int (fun p -> forall r. p r)) (ct:int -> free int) : Type0 =
  behS (ps (lift ct)) `eq_beh (==)` behT ((fun cb -> free_bind (handle_m (ps (lift cb))) (fun r -> free_return (handle r))) ct)

open FStar.Tactics

let sc_proof ps ct : Lemma (sc ps ct) 
  by (
    explode ();
    let x = nth_binder (-2) in
    let x = instantiate x (fresh_uvar None) in
    mapply x;
    norm [delta_only [`%sc]];
    explode ();
    dump "H";
    tadmit ();
    tadmit ()
  )
  = ()

let sc' (ct:(int -> free int) -> free int) (ps:int -> dm int (fun p -> forall r. p r)) : Type0 =
  behT (ct (handle ps)) `eq_beh (==)`
  behS (dm_bind (lift_m (ct ((handleable_arrow int int).handle ps))) (fun r -> dm_return (lift r))) 

let sc_proof' ps ct : Lemma (sc' ct ps)
  by (
    explode ();
    let x = nth_binder (-3) in
    let x = instantiate x (fresh_uvar None) in
    mapply x;
    norm [delta_only [`%sc']];
    assumption ()
  )
  = lem1 (ct (handle ps)) (==)
