module LabelsInST

open FStar.Tactics

open FStar.Preorder
open FStar.Monotonic.Heap
open FStar.ST
open FStar.Ghost

type map_sharedT = mref (pos -> GTot bool) (fun (m0 m1:pos -> GTot bool) -> (forall p. m0 p ==> m1 p))

noeq
type sigT = {
  map_shared : erased map_sharedT;
  is_shared : #a:Type u#0 -> #p:preorder a -> r:mref a p -> h:heap -> res:Type0; //{next_addr h <= addr_of r ==> ~res};
  share : #a:Type u#0 -> #p:preorder a -> sr:(mref a p) ->
    ST unit 
      (requires (fun h0 -> h0 `contains` sr))
      (ensures (fun h0 _ h1 ->
        modifies !{map_shared} h0 h1 /\
        (forall b (r:ref b). h0 `contains` r /\ is_shared r h0 ==> is_shared r h1) /\
        is_shared sr h1
))
}

private
let secret_map : map_sharedT = (** In Pulse, this can be a ghost reference and `share` can be a ghost computation *)
  alloc (fun _ -> false)

let shareS : sigT = {
  map_shared = secret_map;
  //is_shared = (fun #a #p r h -> if addr_of r < next_addr h then (sel h secret_map) (addr_of r) else false);
  is_shared = (fun #a #p r h -> (sel h secret_map) (addr_of r));
  share = (fun #a #p sr -> 
    let m = !secret_map in
    let m' = (fun p -> if p = addr_of sr then true else m p) in
    secret_map := m'
  );
}


unfold let unmodified_common (h0:heap) (h1:heap) : Type0 =
  (forall (a:Type) (rel:preorder a) (r:mref a rel).{:pattern (contains h1 r)}
                               h0 `contains` r ==> h1 `contains` r) /\
  (forall (a:Type) (rel:preorder a) (r:mref a rel).{:pattern (r `unused_in` h0)}
                               r `unused_in` h1 ==> r `unused_in` h0) /\
  (forall (n: nat) . {:pattern (n `addr_unused_in` h0) }
    n `addr_unused_in` h1 ==> n `addr_unused_in` h0)
let modifies_only_shared (h0:heap) (h1:heap) : Type0 =
  (forall (a:Type) (rel:preorder a) (r:mref a rel).{:pattern (sel h1 r)} 
    (h0 `contains` r /\ ~(shareS.is_shared r h0)) ==> sel h0 r == sel h1 r) /\
  unmodified_common h0 h1

effect IST (a:Type) (pre:st_pre) (post: (h:heap -> Tot (st_post' a (pre h)))) =
  ST a 
    (requires (fun h0      -> h0 `contains` shareS.map_shared /\ pre h0))
    (ensures  (fun h0 r h1 -> post h0 r h1))

val progr_sep_test: 
  #rp: ref int -> 
  ctx:(unit -> ST unit (fun _ -> True) (fun h0 _ h1 -> modifies_only_shared h0 h1)) ->
  ST unit
    (requires (fun h0 -> 
      h0 `contains` rp /\
      ~(shareS.is_shared rp h0)))
    (ensures (fun h0 _ h1 ->
      sel h0 rp == sel h1 rp)) // the content of rp should stay the same before/ after calling the context

let progr_sep_test #rp f = 
  f ()

val progr_declassify :
  rp: ref int -> 
  ctx:(r:(ref int) -> ST unit (fun h0 -> h0 `contains` r /\ shareS.is_shared r h0) (ensures (fun h0 _ h1 -> modifies_only_shared h0 h1))) ->
  IST unit
    (requires (fun h0 -> 
      h0 `contains` rp /\
      ~(shareS.is_shared rp h0)))
    (ensures (fun h0 _ h1 -> True))
let progr_declassify rp f =
  shareS.share rp;
  f rp

val progr_declassify_nested:
  rp: ref (ref int) -> 
  ctx:(r:(ref (ref int)) -> ST unit 
    (requires (fun h0 -> h0 `contains` r /\ h0 `contains` (sel h0 r) /\ shareS.is_shared r h0 /\ shareS.is_shared (sel h0 r) h0))
    (ensures (fun h0 _ h1 -> modifies_only_shared h0 h1))) ->
  IST unit
    (requires (fun h0 -> 
      h0 `contains` rp /\ h0 `contains` (sel h0 rp) /\
      ~(shareS.is_shared rp h0)))
    (ensures (fun h0 _ h1 -> True))
let progr_declassify_nested rp f =
  shareS.share rp;
  let p = !rp in
  shareS.share p;
  f rp

val progr_secret_unchanged_test: 
  rp: ref int -> 
  rs: ref (ref int) ->
  ctx:(unit -> ST unit (fun _ -> True) (fun h0 _ h1 -> modifies_only_shared h0 h1)) ->
  IST unit 
    (requires (fun h0 -> 
      h0 `contains` rp /\ h0 `contains` rs /\ h0 `contains` (sel h0 rs) /\
      ~(shareS.is_shared rp h0) /\
      rp =!= (sel h0 rs) /\
      shareS.is_shared rs h0 /\ shareS.is_shared (sel h0 rs) h0))
    (ensures (fun h0 _ h1 ->
      sel h0 rp == sel h1 rp))
         
let progr_secret_unchanged_test rp rs ctx = 
  let h0 = gst_get () in
  let secret: ref int = alloc 0 in
  let h1 = gst_get () in
  assume (~(shareS.is_shared secret h1)); (** one needs to prove that a fresh reference is not shared **)
  ctx ();
  let v = !secret in
  assert (v == 0);
  ()

(**
val progr_passing_callback_test: 
  rp: ref int -> 
  rs: ref (ref int) ->
  ctx:(elab_typ (TArr (TArr TUnit TUnit) TUnit)) ->
  IST unit 
    (requires (fun h0 ->
      satisfy rp h0 contains_pred /\
      label_of rp h0 == High /\
      satisfy rs h0 is_low_pred))
    (ensures (fun h0 _ h1 -> sel h0 rp == sel h1 rp)) // the content of rp should stay the same before/ after calling the context

// TODO: the callback of the program should be able to modify rp
let progr_passing_callback_test rp rs f =
  let secret: ref int = ist_alloc #InvT_Nat 0 in
  let h0 = get () in
  declassify_low' #TNat secret;
  let h1 = get () in
  lemma_declassify_preserves_is_low InvT_Nat secret h0 h1;
  mst_witness (contains_pred secret);
  mst_witness (is_low_pred secret);
  let cb: elab_typ (TArr TUnit TUnit) = (fun _ -> 
    mst_recall (contains_pred secret);
    mst_recall (is_low_pred secret);
    elab_write #TNat secret (!secret + 1);
    raise_val ()) in
  downgrade_val (f cb);
  ()

val progr_getting_callback_test: 
  rp: ref int -> 
  rs: ref (ref int) ->
  ctx:(elab_typ (TArr TUnit (TArr TUnit TUnit))) ->
  IST unit 
    (requires (fun h0 ->
      satisfy rp h0 contains_pred /\
      label_of rp h0 == High /\
      satisfy rs h0 is_low_pred))
    (ensures (fun h0 _ h1 -> sel h0 rp == sel h1 rp))
let progr_getting_callback_test rp rs f =
  let h0 = get () in
  let cb = f (raise_val ()) in
  let h1 = get () in
  downgrade_val (cb (raise_val ()));
  let h2 = get () in
  lemma_modifies_only_label_trans Low h0 h1 h2;
  assert (modifies_only_label Low h0 h2);
  ()
**)
