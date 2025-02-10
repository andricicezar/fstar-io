module SharedRefsCounter

open SharedRefs

open FStar.Preorder

let counter_rel : preorder nat = fun i j -> b2t (i <= j)

let counter = mref nat counter_rel

let counter_pred (c:counter) (i:nat) : heap_predicate_stable = 
  fun h -> h `contains` c /\ sel h c >= i

let witnessed_counter (c:counter) (i:nat) = witnessed (counter_pred c i)

let initialise_counter (init:nat) 
: SST counter 
    (requires (fun h0 -> True)) 
    (ensures (fun h0 c h1 -> alloc_post #nat init h0 c h1)) = 
  sst_alloc' init

let increment_counter (c:counter)
: SST unit 
    (requires (fun h0 -> h0 `contains` c)) 
    (ensures (fun h0 _ h1 -> 
      h0 `contains` c /\
      h1 == upd h0 c (sel h0 c + 1) /\
      modifies (Set.singleton (addr_of c)) h0 h1 /\ 
      equal_dom h0 h1)) =
  let i = sst_read' c in
  sst_write'' c (i + 1)

let witness_counter (c:counter) (i:nat)
: SST unit
    (requires (fun h0 -> h0 `contains` c /\ counter_pred c i h0))
    (ensures  (fun h0 _ h1 -> h0 == h1 /\ witnessed_counter c i)) =
  witness (counter_pred c i)

let recall_counter (c:counter) (i:nat)
: SST unit
    (requires (fun h0 -> h0 `contains` c /\ witnessed_counter c i))
    (ensures  (fun h0 _ h1 -> h0 == h1 /\ counter_pred c i h1)) =
  recall (counter_pred c i)

let test1 (init:nat) (f:counter -> SST unit (requires (fun h0 -> True)) (fun h0 x h1 -> True))
: SST counter 
    (requires (fun h0 -> True)) 
    (ensures (fun h0 c h1 -> h1 `contains` c /\ sel h1 c >= init)) = 
  let c = initialise_counter init in
  increment_counter c;
  witness_counter c (init + 1);
  f c;
  let h = get_heap () in
  assert (sel h c >= init);            // DA: the memory model is so transparent that recalling isn't needed
  //recall_counter c (init + 1);    
  c

let test2 (init:nat) (f:(c:counter) -> SST unit (requires (fun h0 -> True)) (fun h0 x h1 -> witnessed_counter c (init + 42)))
: SST counter 
    (requires (fun h0 -> True)) 
    (ensures (fun h0 c h1 -> h1 `contains` c /\ sel h1 c >= (init + 43))) = 
  let c = initialise_counter init in
  increment_counter c;
  witness_counter c (init + 1);
  f c;
  recall_counter c (init + 42);
  increment_counter c;
  c
