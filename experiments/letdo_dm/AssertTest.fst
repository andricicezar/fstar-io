module AssertTest

open FStar.Tactics.V2
open FStar.Monotonic.Pure

open Assert

(**** Test Refinements **)

val incr5 (x:int{x > 5}) : r:int{r-x == 5}
let incr5 x = x + 5

val dm_incr5 (x:int{x > 5}) : dm (r:int{r-x == 5}) (requires True) (ensures fun _ -> True)
let dm_incr5 x = do begin
  return (incr5 x)
end

val dm_incr5' (x:int) : dm (r:int{r-x == 5}) (requires x > 5) (ensures fun _ -> True)
let dm_incr5' x = do begin
  let! x' = dm_refine x (fun x -> x > 5) in
  let! r = dm_erase_refinement (fun r -> r-x'==5) (incr5 x') in
  dm_refine r (fun r -> r-x == 5)
end

val dm_incr5'' (x:int{x > 5}) : dm int (requires True) (ensures fun r -> r-x == 5)
let dm_incr5'' x = do begin
  return (incr5 x)
end

val dm_incr5''' (x:int) : dm int (requires x > 5) (ensures fun r -> r-x == 5)
let dm_incr5''' x = do begin
  let! y = dm_refine x (fun x -> x > 5) in
  return #int (incr5 y) // <-- needs help here
end

val dm_incr5_dm (x:int{x > 5}) : dm (r:int{r-x == 5}) (requires True) (ensures fun _ -> True)
let dm_incr5_dm  x = do begin
  dm_incr5 x
end

val dm_incr5_dm' (x:int) : dm (r:int{r-x == 5}) (requires x > 5) (ensures fun _ -> True)
let dm_incr5_dm' x = do begin
  let! x' = dm_refine x (fun x -> x > 5) in
  let! r = dm_erase_refinement (fun r -> r-x'==5) (incr5 x') in
  dm_refine r (fun r -> r-x == 5)
end

val dm_incr5_dm'' (x:int{x > 5}) : dm int (requires True) (ensures fun r -> r-x == 5)
let dm_incr5_dm'' x = do begin
  let! y = dm_incr5 x in
  dm_erase_refinement (fun r -> r-x == 5) y
end

val dm_incr5_dm''' (x:int) : dm int (requires x > 5) (ensures fun r -> r-x == 5)
let dm_incr5_dm''' x = do begin
  let! x' = dm_refine x (fun x -> x > 5) in
  return #int (incr5 x') // <-- needs help to erase the refinement
end

(** *** Test Squash **)
assume val p : prop
assume val p' : prop
assume val pure_lemma (_ : unit) : dm p (requires True) (ensures fun _ -> True)
assume val some_f (_ : squash p) : dm unit (requires True) (ensures fun _ -> True)
assume val some_f' : unit -> dm unit (requires p) (ensures fun _ -> p')

let pure_lemma_test () : dm unit (requires True) (ensures fun _ -> True) = do begin
  pure_lemma () ;!
  some_f ()
end

let pure_lemma_test2 () : dm unit (requires True) (ensures fun _ -> True) = do begin
  pure_lemma () ;!
  some_f () ;!
  some_f' () ;!
  dm_assert p'
end

(** *** Test partiality **)
// A test to make sure exfalso isn't used
let test_assume' #a #pre (f : unit -> dm a (requires pre) (ensures fun _ -> True)) : dm a True (fun _ -> True) = do begin
  dm_assume pre ;!
  f ()
end

let test_assert p : dm unit (requires p) (ensures fun _ -> True) = do begin
  dm_assert p
end

[@expect_failure]
let partial_match (l : list int) : dm unit (requires True) (ensures fun _ -> True) = do begin
  match l with
  | Cons _ _ -> return ()
  | _ -> dm_contradiction ()
end

let partial_match (l : list int) : dm unit (requires Cons? l) (ensures fun _ -> True) =
  match l with
  | Cons _ _ -> do begin return () end
  | _ -> do begin dm_contradiction #unit () end

[@expect_failure](** how to make this work? *)
let partial_match (l : list int) : dm unit (requires Cons? l) (ensures fun _ -> True) =
  match l with
  | Cons _ _ -> do begin return () end

let partial_match_pre (l : list int) : dm int (requires Cons? l) (ensures fun r -> r == List.Tot.hd l) =
  match l with
  | x :: r -> do begin return x end
  | _ -> do begin dm_contradiction () end
