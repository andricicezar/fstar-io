module Examples.Guess

open FStar.Preorder
open SharedRefs

type cmp = 
  | LT 
  | GT 
  | EQ

let post_cond = TargetLang.concrete_spec_rel

let mono_incr : preorder int = fun v' v'' -> b2t (v' <= v'')

type player_type =
  l: int -> 
  r: int -> 
  (guess: int -> SST cmp (requires fun _ -> True) (ensures fun h0 r h1 -> post_cond h0 h1)) ->
  SST int (requires (fun _ -> l < r)) (ensures fun h0 r h1 -> post_cond h0 h1)

let ctrans_ref_update1nat (h0 h1 : heap) (r: mref (to_Type SNat) mono_incr) (pred : mref_heap_stable_pred)
  : Lemma (requires modifies !{r} h0 h1 /\ ctrans_ref_pred h0 pred)
          (ensures  ctrans_ref_pred h1 pred)
          [SMTPat (modifies !{r} h0 h1); SMTPat (ctrans_ref_pred h0 pred)]
  = assume (forall (t : shareable_typ) (r' : ref (to_Type t)).
              r' === r \/ contains h0 r' <==> contains h1 r');
    assume (forall_refs_heap pred h0 (sel h0 r) ==> 
            forall_refs_heap pred h1 (sel h1 r));
    admit()

let guess_f
      (pick : int)
      (counter : mref (to_Type SNat) mono_incr{witnessed (contains_pred counter) /\ witnessed (is_encapsulated counter)})
      (guess : int)
  : SST cmp (requires fun h0 -> True)
            (ensures fun h0 r h1 -> post_cond h0 h1)
  = let h0 = get_heap () in
    recall (is_encapsulated counter);
    recall (contains_pred counter);
    let v = !counter in
    counter := v + 1;
    let r =
      if pick = guess then EQ
      else if pick < guess then GT
      else LT
    in
    assert (~(is_private counter h0));
    assert (~(is_shared counter h0));
    let h1 = get_heap () in
    assert (ctrans_ref_pred h0 contains_pred);
    assert (ctrans_ref_pred h0 is_shared);
    ctrans_ref_update1nat h0 h1 counter is_shared;
    ctrans_ref_update1nat h0 h1 counter contains_pred;
    FStar.Monotonic.Heap.lemma_next_addr_upd h0 counter (v+1);
    assert (next_addr h1 >= next_addr h0);
    r

let play_guess (l pick r: int) (player: player_type) : 
  SST (bool * int)
  (requires fun _ -> l < pick /\ pick < r) 
  (ensures fun h0 r h1 -> post_cond h0 h1) =
  let counter = sst_alloc #_  #mono_incr 0 in
  sst_encapsulate counter;
  witness (contains_pred counter);
  witness (is_encapsulated counter);
  let final_guess = player l r (fun g -> guess_f pick counter g) in
  if pick = final_guess then (true, !counter)
  else (false, !counter)
