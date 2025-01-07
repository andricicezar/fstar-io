module SharedRefs

open FStar.Tactics

open FStar.Preorder
open FStar.Monotonic.Heap
open FStar.Ghost
open MST.Tot

private
let secret_map : map_sharedT = (** In Pulse, this can be a ghost reference and `share` can be a ghost computation *)
  alloc (fun _ -> false)

(** In practice, one hides secret_map from the verified program and only exposes `shareS`. **)

let shareS : sigT = {
  map_shared = secret_map;
  // is_shared = (fun #a #p r h -> addr_of r < next_addr h /\ (sel h secret_map) (addr_of r));
  is_shared = (fun #a #p r h -> h `contains` secret_map /\ (** this contains is necessary to show that is_shared is a stable predicate **)
                             (sel h secret_map) (addr_of r));
  is_shared_stable = (fun #a r -> ());
  share = (fun #a #p sr -> 
    let h0 = get () in
    assume (addr_of sr < next_addr h0);(** should come from contains **)
    let m = !secret_map in
    let m' = (fun p -> if p = addr_of sr then true else m p) in
    secret_map := m';
    let h1 = get () in
    assume (next_addr h0 <= next_addr h1)(** Should come from write **)
  );
}

  (**
val is_shared_stable : #a:Type0 -> r:ref a -> Lemma (stable (shareS.is_shared r)) [SMTPat (shareS.is_shared r)]
let is_shared_stable #a r : Lemma (stable (shareS.is_shared r)) [SMTPat (shareS.is_shared r)] = ()
  (**assert (stable (shareS.is_shared r)) by (
    norm[delta_only [`%stable;`%heap_rel];iota];
    let h1 = forall_intro () in let h2 = forall_intro () in
    let i = implies_intro () in 
    let (x, y) = destruct_and i in
    clear i;
    let y = instantiate y (fresh_uvar None) in
    let y' = instantiate y (fresh_uvar None) in
    let y'' = instantiate y' (`secret_map) in
    clear y; clear y';
    compute ();
    binder_retype (nth_binder 6); compute (); trefl ();
    dump "H"
  )**)**)

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
    (requires (fun h0      -> 
      h0 `contains` shareS.map_shared /\ 
      ~(shareS.is_shared (shareS.map_shared) h0) /\ (* the map stays unshared *)
      (forall p. p >= next_addr h0 ==> ~(sel h0 shareS.map_shared p)) /\
      pre h0))
    (ensures  (fun h0 r h1 -> 
      ~(shareS.is_shared (shareS.map_shared) h1) /\
      (forall p. p >= next_addr h1 ==> ~(sel h1 shareS.map_shared p)) /\
      post h0 r h1))

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
  ctx:(r:(ref int) -> IST unit (fun h0 -> h0 `contains` r /\ shareS.is_shared r h0) (ensures (fun h0 _ h1 -> modifies_only_shared h0 h1))) ->
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
  ctx:(r:(ref (ref int)) -> IST unit 
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
  ctx:(unit -> IST unit (fun _ -> True) (fun h0 _ h1 -> modifies_only_shared h0 h1)) ->
  IST unit 
    (requires (fun h0 -> 
      h0 `contains` rp /\ h0 `contains` rs /\ h0 `contains` (sel h0 rs) /\
      ~(shareS.is_shared rp h0) /\
      rp =!= (sel h0 rs) /\
      shareS.is_shared rs h0 /\ shareS.is_shared (sel h0 rs) h0))
    (ensures (fun h0 _ h1 ->
      sel h0 rp == sel h1 rp))
         
let progr_secret_unchanged_test rp rs ctx = 
  let h0 = get () in
  let secret: ref int = alloc 0 in
  assume (addr_of secret == next_addr h0);(** has to come from alloc, necessary to show that secret is not shared **)
  let h1 = get () in
  assume (next_addr h0 < next_addr h1); (** comes from alloc **)
  ctx ();
  let v = !secret in
  assert (v == 0);
  ()

val progr_passing_callback_test: 
  rp: ref int -> 
  rs: ref (ref int) ->
  //ctx:(elab_typ (TArr (TArr TUnit TUnit) TUnit)) ->
  ctx:( (unit -> IST unit (fun _ -> True) (fun h0 _ h1 -> modifies_only_shared h0 h1)) -> 
              IST unit (fun _ -> True) (fun h0 _ h1 -> modifies_only_shared h0 h1)) ->
  IST unit 
    (requires (fun h0 ->
      h0 `contains` rp /\ h0 `contains` rs /\ h0 `contains` (sel h0 rs) /\
      ~(shareS.is_shared rp h0) /\
      shareS.is_shared rs h0 /\ shareS.is_shared (sel h0 rs) h0))
    (ensures (fun h0 _ h1 -> sel h0 rp == sel h1 rp)) // the content of rp should stay the same before/ after calling the context

// TODO: the callback of the program should be able to modify rp
let progr_passing_callback_test rp rs f =
  let h0 = get () in
  let secret: ref int = alloc 0 in
  let h1 = get () in
  assume (next_addr h0 < next_addr h1); (** comes from alloc *)
  shareS.share secret;
  witness (contains_pred secret);
  witness (shareS.is_shared secret);
  let cb : (unit -> IST unit (fun _ -> True) (fun h0 _ h1 -> modifies_only_shared h0 h1)) = (fun _ -> 
    let h0 = get () in
    recall (contains_pred secret);
    recall (shareS.is_shared secret);
    secret := !secret + 1;
    let h1 = get () in
    assume (next_addr h0 <= next_addr h1);
    ()) in
  f cb

val progr_getting_callback_test: 
  rp: ref int -> 
  rs: ref (ref int) ->
  ctx:( unit -> 
    IST ((unit -> IST unit (fun _ -> True) (fun h0 _ h1 -> modifies_only_shared h0 h1)))
      (fun _ -> True)
      (fun h0 _ h1 -> modifies_only_shared h0 h1)) ->
 // ctx:(elab_typ (TArr TUnit (TArr TUnit TUnit))) ->
  IST unit 
    (requires (fun h0 ->
      h0 `contains` rp /\ h0 `contains` rs /\ h0 `contains` (sel h0 rs) /\
      ~(shareS.is_shared rp h0) /\
      shareS.is_shared rs h0 /\ shareS.is_shared (sel h0 rs) h0))
    (ensures (fun h0 _ h1 -> sel h0 rp == sel h1 rp))

let progr_getting_callback_test rp rs f =
  let cb = f () in
  cb ();
  ()
