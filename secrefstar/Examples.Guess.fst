module Examples.Guess

open LabeledRefs
open Witnessable
open Compiler
open HigherOrderContracts
open PolyIface
open SpecTree

type cmp = | LT | GT | EQ

instance witnessable_cmp : witnessable cmp = { satisfy = (fun _ _ -> True) }
instance poly_iface_cmp a3p : poly_iface a3p cmp = { wt = witnessable_cmp }

(* F* warns below that the names are meaningless (and they are),
   but we keep them for documentation purposes. *)
#push-options "--warn_error -331"
type player_type a3p =
  args:((int & int) & (guess: (mk_poly_arrow a3p int cmp))) ->
  ST int (requires (fun h0 -> inv a3p h0 /\ fst (fst args) < snd (fst args))) (ensures fun h0 r h1 -> inv a3p h1 /\ h0 `hrel a3p` h1)
#pop-options

type play_guess_type a3p =
  args:(player_type a3p & (int & (int & int))) ->
  ST (resexn (bool & int)) 
    (requires fun h0 -> inv a3p h0 /\ fst (snd (snd args)) < fst (snd args) /\ fst (snd args) < snd (snd (snd args))) 
    (ensures fun h0 _ h1 -> inv a3p h1 /\ h0 `hrel a3p` h1)

val play_guess : play_guess_type c3p
let play_guess args =
  let player, (pick, (l, r)) = args in
  let counter : mref int (fun v' v'' -> b2t (v' <= v'')) = lr_alloc 0 in
  label_encapsulated counter;
  witness (contains_pred counter);witness (is_encapsulated counter);
  let cb (g:int) : LR cmp (fun _ -> True) (fun h0 r h1 -> h0 `hrel_c` h1) = (
    recall (contains_pred counter);recall (is_encapsulated counter);
    lr_write counter ((lr_read counter) + 1);
    if g = pick then EQ else if pick < g then LT else GT) in
  let final_guess = player ((l,r),cb) in
  if pick = final_guess then (Inl (true, !counter))
  else (Inl (false, !counter))

open FStar.Tactics
open FStar.Tactics.Typeclasses

instance player_args a3p : poly_iface a3p ((int & int) & (mk_poly_arrow a3p int cmp)) =
  poly_iface_pair a3p (int & int) (mk_poly_arrow a3p int cmp) #(poly_iface_arrow a3p int cmp)

let cb_spec (a3p:threep) : spec =
  Spec true false
    int
    (witnessable_int)
    (pre_poly_arrow a3p)
    cmp
    (witnessable_cmp)
    (fun _ -> post_poly_arrow a3p)

let player_spec (a3p:threep) : spec =
  (Spec false false
    ((int & int) & mk_poly_arrow a3p int cmp)
    (poly_iface_is_exportable a3p ((int & int) & mk_poly_arrow a3p int cmp)).c_styp (** TODO: simplify here: (witnessable_pair _ _ #(witnessable_pair _ _ #witnessable_int #witnessable_int) #(witnessable_arrow int cmp _ _)) *)
    (fun x h0 -> inv a3p h0 /\ fst (fst x) < snd (fst x))
    int
    witnessable_int
    (fun _ h0 _ h1 -> inv a3p h1 /\ hrel a3p h0 h1))

let player_hoc : hoc c3p (player_spec c3p) =
  TrivialPost (fun _ -> ()) (fun _ _ -> ())

instance importable_player (a3p:threep) : safe_importable_to a3p (player_type a3p) (Node (U10 (player_spec a3p)) Leaf Leaf) =
  safe_importable_arrow10 
    a3p _ _
    #(poly_iface_is_exportable a3p _ #(poly_iface_pair a3p _ #(poly_iface_pair a3p int int) _ #(poly_iface_arrow a3p _ #(poly_iface_int a3p) _ #(poly_iface_cmp a3p))))
    _ _ #(poly_iface_is_safely_importable a3p int #(poly_iface_int a3p))
    (fun x h0 -> inv a3p h0 /\ fst (fst x) < snd (fst x))
    (fun _ h0 _ h1 -> inv a3p h1 /\ hrel a3p h0 h1)

instance args_importable a3p : importable_to a3p (player_type a3p & (int & (int & int))) _ =
  importable_pair a3p (player_type a3p) _ #(safe_importable_is_importable a3p _ _ #(importable_player a3p)) (int & (int & int)) Leaf

let play_guess_spec (a3p:threep) : spec =
  Spec true true
    (player_type a3p & (int & (int & int)))
    (args_importable a3p).c_styp (** TODO: simplify here with witnessable *)
    (fun x h0 -> inv a3p h0 /\ fst (snd (snd x)) < fst (snd x) /\ fst (snd x) < snd (snd (snd x)))
    (bool & int)
    (exportable_pair a3p bool Leaf int Leaf).c_styp (** TODO: simplify here with witnessable *)
    (fun _ h0 _ h1 -> inv a3p h1 /\ hrel a3p h0 h1)

(* The check is given the type that `pre_check` (i.e. `select_check`)
   abbreviates, spelled out: newer F* versions no longer elaborate the lambda
   against the abbreviation when it appears as an argument of `EnforcePre`. *)
let play_guess_check (args:(play_guess_spec c3p).argt)
  : ST (eh0:FStar.Ghost.erased heap{pre_poly_arrow c3p #((play_guess_spec c3p).argt) #(play_guess_spec c3p).wt_argt args eh0} &
        cb_check c3p (play_guess_spec c3p).argt unit
          (pre_poly_arrow c3p #((play_guess_spec c3p).argt) #(play_guess_spec c3p).wt_argt)
          (fun x _ _ h1 -> (play_guess_spec c3p).pre x h1) args eh0)
       (pre_poly_arrow c3p #((play_guess_spec c3p).argt) #(play_guess_spec c3p).wt_argt args)
       (fun h0 r h1 -> FStar.Ghost.reveal (dfst r) == h0 /\ h0 == h1) =
  let args : (player_type c3p & (int & (int & int))) = args in
  let eh0 = get_heap () in
  let check : cb_check c3p (play_guess_spec c3p).argt unit (pre_poly_arrow c3p #((play_guess_spec c3p).argt) #(play_guess_spec c3p).wt_argt) (fun x _ _ h1 -> (play_guess_spec c3p).pre x h1) args eh0 =
    (fun () -> if fst (snd (snd args)) < fst (snd args) && fst (snd args) < snd (snd (snd args)) then Inl () else Inr (Contract_failure "Invalid range")) in
  (| eh0, check |)

let play_guess_hoc : hoc c3p (play_guess_spec c3p) =
  EnforcePre
    play_guess_check
    (fun x r ->
      (* `satisfy` on the return type is `True` (the return type is ground),
         but reducing it needs the case analysis on the resexn. *)
      (match r with
       | Inl v -> assert ((play_guess_spec c3p).wt_rett.satisfy v (prref c3p))
                    by (norm [delta; iota; zeta; primops; simplify]; smt ())
       | Inr _ -> ());
      assert (forall h0 h1. inv c3p h1 /\ hrel c3p h0 h1 ==> post_poly_arrow c3p #(resexn (play_guess_spec c3p).rett) #(witnessable_resexn _ #(play_guess_spec c3p).wt_rett) h0 r h1))

instance exportable_play_guess a3p : exportable_from a3p (play_guess_type a3p) (Node (U10 (play_guess_spec a3p)) _ _) =
  exportable_arrow_err10 a3p 
    _ _
    #(args_importable a3p)
    _ _
    #(exportable_pair a3p bool Leaf int Leaf)
    _ _

let play_guess_st (a3p:threep) : spec_tree =
  Node (U10 (play_guess_spec a3p))
    (EmptyNode
        (Node (U10 (player_spec a3p)) Leaf Leaf) Leaf)
    (EmptyNode Leaf Leaf)

let player_pck_hoc : pck_uhoc c3p =
  (| U10 (player_spec c3p), U10hoc player_hoc |)

let play_guess_pck_hoc : pck_uhoc c3p =
  (| U10 (play_guess_spec c3p), U10hoc play_guess_hoc |)

let play_guess_hoc_tree : hoc_tree c3p (play_guess_st c3p) =
  Node play_guess_pck_hoc
    (EmptyNode
      (Node player_pck_hoc Leaf Leaf) Leaf)
    (EmptyNode Leaf Leaf)

let sit2 : src_interface2 = {
  specs = play_guess_st;
  hocs = play_guess_hoc_tree;
  pt = play_guess_type;
  c_pt = exportable_play_guess;
}

val prog2 : prog_src2 sit2
let prog2 = play_guess

let compiled_prog2 =
  compile_pprog2 #sit2 prog2

val some_ctx2 : ctx_tgt2 (comp_int_src_tgt2 sit2)
let some_ctx2 #a3p _ _ alloc prog =
  let cb : (safe_importable_is_importable a3p (player_type a3p) (Node (U10 (player_spec a3p)) Leaf Leaf) #(importable_player a3p)).ityp =
    (fun ((l, r), cb) -> let _ = cb l in let _ = cb (l+1) in r) in
  match prog (cb, (0, (0, 10))) with
  | Inl (b, guesses_count) -> if b then -2 else 0
  | Inr _ -> -1

let whole_prog2 : whole_tgt2 =
  link_tgt2 compiled_prog2 some_ctx2

let r2 = whole_prog2 ()
let _ =
  match r2 with
  | 0 -> FStar.IO.print_string "Success!\n"
  | -2 -> FStar.IO.print_string "Error! How did it guess?\n"
  | -1 -> FStar.IO.print_string "Error! The contract was supposed to succeed!\n"
  | _ -> FStar.IO.print_string "Impossible!\n"
