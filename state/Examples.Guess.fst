module Examples.Guess

open SharedRefs
open Witnessable
open Compiler
open HigherOrderContracts
open PolyIface
open SpecTree

type cmp = | LT | GT | EQ

instance witnessable_cmp : witnessable cmp = { satisfy = (fun _ _ -> True) }
instance poly_iface_cmp a3p : poly_iface a3p cmp = { wt = witnessable_cmp }

let post_cond = PolyIface.c3p_hrel

type player_type =
  args:((int & int) & (guess: int -> SST cmp (fun _ -> True) (fun h0 r h1 -> post_cond h0 h1))) ->
  SST int (requires (fun _ -> fst (fst args) < snd (fst args))) (ensures fun h0 r h1 -> post_cond h0 h1)

let play_guess (args:player_type & (int & (int & int))) : 
  SST (bool & int)
  (requires fun _ -> fst (snd (snd args)) < fst (snd args) /\ fst (snd args) < snd (snd (snd args))) 
  (ensures fun h0 r h1 -> post_cond h0 h1) =
  let player, (pick, (l, r)) = args in
  let counter : mref int (fun v' v'' -> b2t (v' <= v'')) = sst_alloc 0 in
  sst_encapsulate counter;
  witness (contains_pred counter);witness (is_encapsulated counter);
  let cb (g:int) : SST cmp (fun _ -> True) (fun h0 r h1 -> post_cond h0 h1) = (
    recall (contains_pred counter);recall (is_encapsulated counter);
    sst_write counter ((sst_read counter) + 1);
    if g = pick then EQ else if pick < g then LT else GT) in
  let final_guess = player ((l,r),cb) in
  if pick = final_guess then (true, !counter)
  else (false, !counter)

instance importable_player a3p : safe_importable_to a3p (mk_poly_arrow a3p ((int & int) & (mk_poly_arrow a3p int cmp)) int) Leaf =
  poly_iface_is_safely_importable a3p _ #(poly_iface_arrow a3p ((int & int) & (mk_poly_arrow a3p int cmp)) int #(
    poly_iface_pair a3p (int & int) (mk_poly_arrow a3p int cmp) #_ #(poly_iface_arrow a3p int cmp)
  ) #_)

// instance exportable_guess a3p : exportable_from a3p (mk_poly_arrow a3p (player_type & (int & (int & int))) (resexn (bool & int)) #(witnessable_resexn (bool & int) #(witnessable_pair bool int))) _ =
//   exportable_arrow a3p _ _ Leaf Leaf _ _