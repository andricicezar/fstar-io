module Assert

open FStar.Tactics.V2
open FStar.Monotonic.Pure

noeq
type free (a:Type u#a) : Type u#(max 1 a) =
| Return : a -> free a
| Assert : pre:Type0 -> (squash pre -> free a) -> free a

let rec free_bind
  #a #b
  (m:free a)
  (f:a -> free b) :
  free b =
  match m with
  | Return x -> f x
  | Assert pre k -> Assert pre (fun x -> free_bind (k x) f)

let rec theta #a (m:free a) : pure_wp a =
  match m with
  | Return x -> pure_return _ x
  | Assert pre k -> pure_bind_wp _ _ (as_pure_wp #(squash pre) (fun p -> pre /\ p ())) (fun x -> theta (k x))

type dm_wp a (w:pure_wp a) =
  m:(free a){pure_stronger _ w (theta m)}

let return #a (x:a) : dm_wp a (pure_return a x) = Return x

let (let!)
  #a #b
  #w1 #w2
  (m:dm_wp a w1)
  (k:(x:a -> dm_wp b (w2 x))) :
  dm_wp b (pure_bind_wp _ _ w1 w2) =
  admit (); (** easy to prove **)
  free_bind m k

let do #a (#wp1:pure_wp a) (#wp2:(pure_wp a){pure_stronger _ wp2 wp1}) (f:dm_wp a wp1) : dm_wp a wp2 =
  f

let dm_assert (pre:Type0) : dm_wp unit (as_pure_wp (fun p -> pre /\ p ())) =
  Assert pre Return

assume val dm_assume (post:Type0) : dm_wp unit (as_pure_wp (fun p -> post ==> p ()))
assume val dm_admit #a () : dm_wp a (as_pure_wp (fun p -> forall r. p r))

let dm_contradiction #a () : dm_wp a (as_pure_wp (fun p -> False /\ forall (r:a). p r)) =
  dm_assert False ;!
  dm_admit () (** i guess one can use the previous false to prove that a witness exists? **)


type dm a (pre:Type0) (post:(_:a{pre} -> Type0)) =
  dm_wp a (as_pure_wp (fun p -> pre /\ (forall r. post r ==> p r)))

(**** Test Refinements **)

let dm_refine (#a:Type) (x:a) (ref:a -> Type0) : dm_wp (x:a{ref x}) (as_pure_wp #(x:a{ref x}) (fun p -> ref x /\ p (x <: (x:a{ref x})))) =
  Assert (ref x) (fun _ -> Return (x <: (x:a{ref x}))) // what is the intuition behind this?

let dm_erase_refinement (#a:Type) (ref:a -> Type0) (x:a{ref x}) : dm_wp a (as_pure_wp #a (fun p -> ref x ==> p (x <: a))) =
  return x

val incr5 (x:int{x > 5}) : r:int{r-x == 5}
let incr5 x = x + 5

val dm_incr5 (x:int{x > 5}) : dm (r:int{r-x == 5}) (requires True) (ensures fun _ -> True)
let dm_incr5 x = return (incr5 x)

 val dm_incr5' (x:int) : dm (r:int{r-x == 5}) (requires x > 5) (ensures fun _ -> True)
let dm_incr5' x =
  let! x' = dm_refine x (fun x -> x > 5) in (** this creates a new x with a different type **)
  let! r = dm_erase_refinement (fun r -> r-x'==5) (incr5 x') in
  // let r : int = incr5 x in (** the refinement is erased without being saved at all! **)
  dm_refine r (fun r -> r-x == 5)

val dm_incr5'' (x:int{x > 5}) : dm int (requires True) (ensures fun r -> r-x == 5)
let dm_incr5'' x = return (incr5 x)

val dm_incr5''' (x:int) : dm int (requires x > 5) (ensures fun r -> r-x == 5)
let dm_incr5''' x =
  let! y = dm_refine x (fun x -> x > 5) in
  return (incr5 y)

val dm_incr5_dm (x:int{x > 5}) : dm (r:int{r-x == 5}) (requires True) (ensures fun _ -> True)
let dm_incr5_dm  x = dm_incr5 x

val dm_incr5_dm' (x:int) : dm (r:int{r-x == 5}) (requires x > 5) (ensures fun _ -> True)
let dm_incr5_dm' x =
  let! x' = dm_refine x (fun x -> x > 5) in
  let! r = dm_erase_refinement (fun r -> r-x'==5) (incr5 x') in
  dm_refine r (fun r -> r-x == 5)

val dm_incr5_dm'' (x:int{x > 5}) : dm int (requires True) (ensures fun r -> r-x == 5)
let dm_incr5_dm'' x =
  let! y = dm_incr5 x in
  dm_erase_refinement (fun r -> r-x == 5) y

val dm_incr5_dm''' (x:int) : dm int (requires x > 5) (ensures fun r -> r-x == 5)
let dm_incr5_dm''' x =
  let! x' = dm_refine x (fun x -> x > 5) in
  return (incr5 x') (** refinement is erased forever **)


(** *** Test Squash **)
assume val p : prop
assume val p' : prop
assume val pure_lemma (_ : unit) : dm p (requires True) (ensures fun _ -> True)
assume val some_f (_ : squash p) : dm unit (requires True) (ensures fun _ -> True)
assume val some_f' : unit -> dm unit (requires p) (ensures fun _ -> p')

let pure_lemma_test () : dm unit (requires True) (ensures fun _ -> True) =
  pure_lemma () ;!
  some_f ()

let pure_lemma_test2 () : dm unit (requires True) (ensures fun _ -> True) =
  pure_lemma () ;!
  some_f () ;!
  some_f' () ;!
  dm_assert p'

(** *** Test partiality **)
// A test to make sure exfalso isn't used
let test_assume #a #pre (f : unit -> dm a (requires pre) (ensures fun _ -> True)) : dm a True (fun _ -> True) =
  assume pre ;
  f ()

let test_assume' #a #pre (f : unit -> dm a (requires pre) (ensures fun _ -> True)) : dm a True (fun _ -> True) =
  dm_assume pre ;!
  f ()

let test_assert p : dm unit (requires p) (ensures fun _ -> True) =
  dm_assert p

[@expect_failure]
let partial_match (l : list int) : dm unit (requires True) (ensures fun _ -> True) =
  match l with
  | Cons _ _ -> return ()
  | _ -> dm_contradiction ()

let partial_match (l : list int) : dm unit (requires Cons? l) (ensures fun _ -> True) =
  match l with
  | Cons _ _ -> return ()
  | _ -> dm_contradiction ()

[@expect_failure](** how to make this work? *)
let partial_match (l : list int) : dm unit (requires Cons? l) (ensures fun _ -> True) =
  match l with
  | Cons _ _ -> return ()

let partial_match_pre (l : list int) : dm int (requires Cons? l) (ensures fun r -> r == List.Tot.hd l) =
  match l with
  | x :: r -> return x
  | _ -> dm_contradiction ()

// let partial_match_io (l : list string) : dm file_descr (requires l <> []) (ensures fun _ -> True) =
//   match l with
//   | s :: _ -> open_file s
