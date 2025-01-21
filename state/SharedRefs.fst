module SharedRefs

(**
private (** TODO: is this necessary? **)
let secret_map : map_sharedT = (** In Pulse, this can be a ghost reference and `share` can be a ghost computation *)
  alloc (fun _ -> false)
**)
(** Popular vote for this, instead of the top-level effectful call **)
assume val secret_map : map_sharedT

private
let is_shared : ref_heap_stable_pred = (fun #a #p (r:mref a p) h ->
    h `contains` secret_map /\ (** this contains is necessary to show that is_shared is a stable predicate **)
    (sel h secret_map) (addr_of r)) 

private
let unmodified_map_implies_same_shared_status (ms:Set.set nat) (h0 h1:heap) : 
    Lemma (h0 `contains` secret_map /\ h0 `heap_rel` h1 /\ ~(addr_of secret_map `Set.mem` ms) /\ modifies ms h0 h1 ==> 
      (forall #a #rel (r:mref a rel). is_shared r h0 <==> is_shared r h1)) = 
    introduce h0 `contains` secret_map /\ h0 `heap_rel` h1 /\ ~(addr_of secret_map `Set.mem` ms) /\ modifies ms h0 h1 ==> (forall #a #rel (r:mref a rel). is_shared r h0 <==> is_shared r h1) with _. begin
      introduce forall a rel (r:mref a rel). is_shared r h0 <==> is_shared r h1 with begin
        introduce is_shared r h0 ==> is_shared r h1 with _. ();
        introduce is_shared r h1 ==> is_shared r h0 with _. ()
      end
    end  

let shareS : sigT = {
  map_shared = secret_map;
  is_shared = is_shared;
  fresh_ref_not_shared = (fun #a #rel r h -> ());
  unmodified_map_implies_same_shared_status = unmodified_map_implies_same_shared_status;
  same_addr_same_sharing_status = (fun ra rb h -> ());
  share = (fun #a #p sr -> 
    let h0 = get () in
    lemma_next_addr_contained_refs_addr h0 sr;
    let m = !secret_map in
    let m' = (fun p -> if p = addr_of sr then true else m p) in
    secret_map := m';
    let h1 = get () in
    lemma_next_addr_upd_tot h0 secret_map m'
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
  )**)

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
**)
