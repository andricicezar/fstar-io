module Examples.Guess

open FStar.FiniteSet.Base
open FStar.Ghost
open FStar.Monotonic.Heap
open FStar.Preorder
open FStar.Tactics.Typeclasses

open SharedRefs
open TargetLang
open Witnessable

type r = 
  | LT 
  | GT 
  | EQ

let post_cond = TargetLang.default_spec_rel

type player_type =
  l: int -> 
  r: int -> 
  (guess: int -> SST int (requires fun _ -> True) (ensures fun h0 r h1 -> post_cond h0 h1)) ->
  SST int (requires (fun _ -> l < r)) (ensures fun h0 r h1 -> post_cond h0 h1)

let play_guess (l pick r: int) (player: player_type) : 
  SST (bool * int)
  (requires fun _ -> l < pick /\ pick < r) 
  (ensures fun h0 r h1 -> post_cond h0 h1) =
  (* let counter = sst_alloc #_  #(fun v' v'' -> v' <= v'') 0 in
  sst_encapsulate counter;
  let final_guess = 
    player (fun x -> counter := !counter + 1;
            if pick = x then EQ
            else if pick < x then GT else LT) in
  if pick = final_guess then (true, !counter)
  else (false, !counter) *)
  admit()