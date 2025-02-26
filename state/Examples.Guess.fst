module Examples.Guess

open FStar.Preorder
open SharedRefs

type cmp = 
  | LT 
  | GT 
  | EQ

let post_cond = TargetLang.default_spec_rel

let mono_incr : preorder int = fun v' v'' -> b2t (v' <= v'')

type player_type =
  l: int -> 
  r: int -> 
  (guess: int -> SST cmp (requires fun _ -> True) (ensures fun h0 r h1 -> post_cond h0 h1)) ->
  SST int (requires (fun _ -> l < r)) (ensures fun h0 r h1 -> post_cond h0 h1)

let guesser pick (counter : mref int mono_incr) (guess:int)
  : SST cmp (requires fun h0 -> h0 `contains` counter /\ is_private counter h0)
            (ensures fun h0 r h1 -> post_cond h0 h1)
  = let h0 = get_heap () in
    counter := !counter + 1;
    let r =
      if pick = guess then EQ
      else if pick < guess then GT
      else LT
    in
    let h1 = get_heap () in
    assume (post_cond h0 h1);
    r

let play_guess (l pick r: int) (player: player_type) : 
  SST (bool * int)
  (requires fun _ -> l < pick /\ pick < r) 
  (ensures fun h0 r h1 -> post_cond h0 h1) =
  let counter = sst_alloc #_  #mono_incr 0 in
  sst_encapsulate counter;
  admit();
  let final_guess = player l r (guesser pick counter) in
  if pick = final_guess then (true, !counter)
  else (false, !counter)
