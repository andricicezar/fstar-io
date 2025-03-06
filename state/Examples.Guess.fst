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

type player_type a3p =
  args:((int & int) & (guess: (mk_poly_arrow a3p int cmp))) ->
  ST int (requires (fun h0 -> inv a3p h0 /\ fst (fst args) < snd (fst args))) (ensures fun h0 r h1 -> inv a3p h1 /\ h0 `hrel a3p` h1)

type play_guess_type a3p =
  args:(player_type a3p & (int & (int & int))) ->
  ST (resexn (bool & int)) (requires fun h0 -> inv a3p h0 /\ fst (snd (snd args)) < fst (snd args) /\ fst (snd args) < snd (snd (snd args))) (ensures fun h0 r h1 -> inv a3p h1 /\ h0 `hrel a3p` h1)

val play_guess : play_guess_type c3p
let play_guess args =
  let player, (pick, (l, r)) = args in
  let counter : mref int (fun v' v'' -> b2t (v' <= v'')) = sst_alloc 0 in
  sst_encapsulate counter;
  witness (contains_pred counter);witness (is_encapsulated counter);
  let cb (g:int) : SST cmp (fun _ -> True) (fun h0 r h1 -> h0 `hrel_c` h1) = (
    recall (contains_pred counter);recall (is_encapsulated counter);
    sst_write counter ((sst_read counter) + 1);
    if g = pick then EQ else if pick < g then LT else GT) in
  let final_guess = player ((l,r),cb) in
  if pick = final_guess then (Inl (true, !counter))
  else (Inl (false, !counter))

open FStar.Tactics
open FStar.Tactics.Typeclasses

instance player_args a3p : poly_iface a3p ((int & int) & (mk_poly_arrow a3p int cmp)) =
  poly_iface_pair a3p (int & int) (mk_poly_arrow a3p int cmp) #_ #(poly_iface_arrow a3p int cmp)

let cb_spec (a3p:threep) : pck_spec =
  Spec00 true
    int
    (witnessable_int)
    (pre_poly_arrow a3p)
    cmp
    (witnessable_cmp)
    (fun _ -> post_poly_arrow a3p)

let player_spec (a3p:threep) : pck_spec =
  Spec10 false
    ((int & int) & (guess: (mk_poly_arrow a3p int cmp)))
    (witnessable_pair _ _ #(witnessable_pair _ _ #witnessable_int #witnessable_int) #(witnessable_arrow int cmp _ _))
    (fun x h0 -> inv a3p h0 /\ fst (fst x) < snd (fst x))
    int
    witnessable_int
    (fun _ h0 _ h1 -> inv a3p h1 /\ hrel a3p h0 h1)

(** Stuck here: **)
instance importable_player (a3p:threep) : safe_importable_to a3p (player_type a3p) (Node (player_spec a3p) Leaf Leaf) =
  safe_importable_arrow_safe10 
    a3p _ _
    #(poly_iface_is_exportable a3p _ #(poly_iface_pair a3p _ _ #(poly_iface_pair a3p int int) #(poly_iface_arrow a3p _ _ #(poly_iface_int a3p) #(poly_iface_cmp a3p))))
    // #(exportable_pair a3p 
    //   (int & int) 
    //   (mk_poly_arrow a3p int cmp) 
    //   _ _ 
    //   #(exportable_pair a3p int int Leaf Leaf #(exportable_int a3p) #(exportable_int a3p))
    //   #(exportable_arrow_no_err00 a3p int _ #(poly_iface_is_safely_importable a3p int) cmp _ #(poly_iface_is_exportable a3p cmp #(poly_iface_cmp a3p)) _ _))
    _ _ #(poly_iface_is_safely_importable a3p int #(poly_iface_int a3p))
    (fun x h0 -> inv a3p h0 /\ fst (fst x) < snd (fst x))
    (fun _ h0 _ h1 -> inv a3p h1 /\ hrel a3p h0 h1)

instance args_importable a3p : importable_to a3p (player_type a3p & (int & (int & int))) _ =
  importable_pair a3p (player_type a3p) (int & (int & int)) _ Leaf #(safe_importable_is_importable a3p _ _ #(importable_player a3p))

instance exportable_play_guess a3p : exportable_from a3p (play_guess_type a3p) _ =
  exportable_arrow10 a3p 
    _ _ _ _ 
    #(args_importable a3p)
    #(exportable_resexn a3p (bool & int) (EmptyNode Leaf Leaf) #(exportable_pair a3p bool int Leaf Leaf))
    _ _

