module Examples.Guess

open FStar.FiniteSet.Base
open FStar.Ghost
open FStar.Monotonic.Heap
open FStar.Preorder
open FStar.Tactics.Typeclasses

open SharedRefs
open Witnessable

type r = 
  | LT 
  | GT 
  | EQ

(*TODO: check second postcond & update the name here/ in the paper to match *)
let post_cond = fun h0 _ h1 -> modifies_only_shared_and_encapsulated h0 h1 
              /\ (forall (a:Type) (rel:FStar.Preorder.preorder a) (r:mref a rel) . 
                  h0 `contains` r ==> kind_not_modified r h0 h1)

type player_type =
  l: int -> r: int -> (guess: int -> SST int (requires fun _ -> True) (ensures post_cond)) ->
  SST int (requires (fun _ -> l < r)) (ensures post_cond)

let play_guess (l pick r: int) (player: player_type) : 
  SST (bool * int)
  (requires fun _ -> l < pick /\ pick < r) 
  (ensures post_cond) =
  (* let counter = alloc 0 (fun v' v'' -> v' <= v'') in
  encapsulate counter;
  let final_guess = 
    player (fun x -> counter := counter + 1;
            if pick = x then EQ
            else if pick < x then GT else LT) in
  if pick = final_guess then (true, !counter)
  else (false, !counter) *)
  admit()