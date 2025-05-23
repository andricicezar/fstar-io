module CooperativeMultiThreading

open FStar.List.Tot
open SharedRefs 

noeq
type atree (a:Type0) =
| Return : a -> atree a 
| Yield : continuation a -> atree a
| Fork : continuation a -> continuation a -> atree a
and continuation a =
  unit -> SST (atree a) (fun _ -> True) (fun _ _ _ -> True)

let rec scheduler
  (fuel:nat)
  (f:continuation unit)
  (queue:list (continuation unit))
  : SST (unit * (list (continuation unit)))
    (requires (fun _ -> True))
    (ensures (fun _ _ _ -> True)) = 
  if fuel = 0 then ((), [])
  else
  match f () with
  | Return x -> run_next (fuel-1) queue ()
  | Yield k -> run_next (fuel-1) (queue @ [k]) ()
  | Fork k1 k2 -> scheduler (fuel-1) k1 (queue @ [k2])
and run_next (fuel:nat) (queue:list (continuation unit)) (v:unit)
  : SST (unit * (list (continuation unit)))
    (requires (fun _ -> True))
    (ensures (fun _ _ _ -> True)) =
  match queue with
  | [] -> (v, [])
  | hd::tl -> scheduler fuel hd tl

let round_robin 
  #ta (v:to_Type ta) (** shared value/memory **)
  (main:(to_Type ta -> SST (atree unit) (fun _ -> True) (fun _ _ _ -> True)))
  : SST unit
    (requires (fun _ -> True))
    (ensures (fun _ _ _ -> True)) = 
  fst (scheduler 1000 (fun () -> main v) [])

(**
    TODO: no private reference
    TODO: what is the meaning of shared references here
let blackjack
  seed
  #ta (v:to_Type ta) (** shared value/memory **)
  (house:(to_Type ta -> see_cards:(unit -> SST (list card)) -> draw_card:(unit -> SST (option card)) -> SST (atree unit) (fun _ -> True) (fun _ _ _ -> True)))
  (pl1:(to_Type ta -> see_cards:_ -> draw_card:_ -> SST (atree unit) (fun _ -> True) (fun _ _ _ -> True)))
  : SST game_state
    (requires (fun _ -> True))
    (ensures (fun _ r _ -> valid_game_state r)) =
    
  let gdeck : list card = generate_deck seed in
  let deck : mref (list card) (prefix gdeck) = alloc gdeck in
  encapsulate deck;
  let game_state : mref _ _ = _ in // has a preorder on it guaranteeing correctness, depend on gdeck
  encapsulate game_state;

  let draw_card ply = 
    if next_valid_game_state !game_state ply then
      let card = pop deck in
      game_state := game_state @ [Draw ply card];
      Some card
    else None
  in

  let pl1_cards : ref (list card) = [draw_card 1; draw_card 1] in
  let house_sec_card : ref card = draw_card 0 in
  let house_cards : ref (list card) = [draw_card 0] in

  let _ =
    scheduler 1000
      (fun () -> pl1 v (fun () -> (!pl1_cards, !house_cards)) (fun () -> draw_card 1))
      [(fun () -> house v (fun () -> (!house_sec_card, !house_cards, !pl1_cards)) (fun () -> draw_card 0))] in

  !game_state
**)
