module Assert

open FStar.Tactics.V2
open FStar.Monotonic.Pure

val dm_wp (a:Type u#a) (w:pure_wp a) : Type u#(max 1 a)

val return #a (x:a) : dm_wp a (pure_return a x)

val (let!) #a #b #w1 #w2 (m:dm_wp a w1) (k:(x:a -> dm_wp b (w2 x))) : dm_wp b (pure_bind_wp _ _ w1 w2)

val do #a (#wp1:pure_wp a) (#wp2:(pure_wp a){pure_stronger _ wp2 wp1}) (f:dm_wp a wp1) : dm_wp a wp2

val dm_assert (pre:Type0) : dm_wp unit (as_pure_wp (fun p -> pre /\ p ()))

val dm_assume (post:Type0) : dm_wp unit (as_pure_wp (fun p -> post ==> p ()))

val dm_admit #a () : dm_wp a (as_pure_wp (fun p -> forall r. p r))

let dm_contradiction #a () : dm_wp a (as_pure_wp (fun p -> False /\ forall (r:a). p r)) =
  dm_assert False ;!
  dm_admit () (** i guess one can use the previous false to prove that a witness exists? **)

type dm a (pre:Type0) (post:(_:a{pre} -> Type0)) =
  dm_wp a (as_pure_wp (fun p -> pre /\ (forall r. post r ==> p r)))

val dm_refine (#a:Type) (x:a) (ref:a -> Type0) : dm_wp (x:a{ref x}) (as_pure_wp #(x:a{ref x}) (fun p -> ref x /\ p (x <: (x:a{ref x}))))

let dm_erase_refinement (#a:Type) (ref:a -> Type0) (x:a{ref x}) : dm_wp a (as_pure_wp #a (fun p -> ref x ==> p (x <: a))) = do begin
  return x
end
