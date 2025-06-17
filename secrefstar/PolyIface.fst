module PolyIface

open FStar.Tactics
open FStar.Tactics.Typeclasses
open FStar.Ghost
open FStar.Preorder
open FStar.Universe

open LabeledRefs
open Witnessable

(** *** Type to carry the three predicates around *)

(* F* warns below that the names are meaningless (and they are),
   but we keep them for documentation purposes. *)
#push-options "--warn_error -331"
type threep =
  inv:(heap -> Type0) * prref:mref_pred * hrel:(preorder heap)
  (**                   ^ if this predicate would be also over heaps, then the contexts needs witness&recall in HO settings **)
#pop-options

unfold
let mk_threep
  (inv  : heap -> Type0)
  (prref: mref_pred)
  (hrel : preorder heap)
  : threep =
  (inv, (prref <: (#a:Type0 -> #rel:preorder a -> mref a rel -> Type0)), hrel)

let inv = Mktuple3?._1
let prref = Mktuple3?._2
let hrel = Mktuple3?._3

(** *** Helper function to make an arrow polymorphic in the three predicates *)

unfold let pre_poly_arrow
  (a3p:threep)
  (#t1:Type) {| c1 : witnessable t1 |}
  (x:t1) (h0:heap) =
  inv a3p h0 /\ c1.satisfy x (prref a3p)

unfold let post_poly_arrow
  (a3p:threep)
  (#t2:Type) {| c2 : witnessable t2 |}
  (h0:heap) (r:t2) (h1:heap) =
  inv a3p h1 /\ h0 `hrel a3p` h1 /\ c2.satisfy r (prref a3p)

let mk_poly_arrow
  (a3p:threep)
  (t1:Type u#a) {| c1 : witnessable t1 |}
  (t2:Type u#b) {| c2 : witnessable t2 |}
= x:t1 -> ST t2
    (pre_poly_arrow a3p x)
    (post_poly_arrow a3p)

(** *** Type class that defines polymorphic interfaces *)

class poly_iface (a3p:threep) (t:Type u#a) =
  { wt : witnessable t }

instance poly_iface_full_ground_type a3p (t:Type) {| c:tc_full_ground_type t |} : poly_iface a3p t = {
  wt = witnessable_full_ground_type t #c;
}

instance poly_iface_unit a3p : poly_iface a3p unit = { wt = witnessable_unit }
instance poly_iface_int  a3p : poly_iface a3p int = { wt = witnessable_int }
instance poly_iface_bool  a3p : poly_iface a3p bool = { wt = witnessable_bool }
instance poly_iface_pair a3p t1 {| c1:poly_iface a3p t1 |}  t2 {| c2:poly_iface a3p t2 |}
  : poly_iface a3p (t1 * t2)
  = { wt = witnessable_pair t1 #c1.wt t2 #c2.wt }
instance poly_iface_univ_raise a3p (t1:Type u#a) {| c1:poly_iface a3p t1 |}
  : poly_iface a3p (FStar.Universe.raise_t u#a u#b t1)
  = { wt = witnessable_univ_raise t1 #c1.wt }
instance poly_iface_sum a3p t1 {| c1:poly_iface a3p t1 |} t2 {| c2:poly_iface a3p t2 |}
  : poly_iface a3p (either t1 t2)
  = { wt = witnessable_sum t1 #c1.wt t2 #c2.wt }
instance poly_iface_option a3p t1 {| c1:poly_iface a3p t1 |}
  : poly_iface a3p (option t1)
  = { wt = witnessable_option t1 #c1.wt }
instance poly_iface_ref a3p t1 {| c1:tc_full_ground_type t1 |}
  : poly_iface a3p (ref t1)
  = { wt = witnessable_mref t1 (FStar.Heap.trivial_preorder t1) #solve }
instance poly_iface_list a3p t1 {| c1:poly_iface a3p t1 |}
  : poly_iface a3p (list t1)
  = { wt = witnessable_list t1 #c1.wt }
instance poly_iface_llist a3p t1 {| c1:tc_full_ground_type t1 |}
  : poly_iface a3p (linkedList t1)
  = { wt = witnessable_llist t1 #solve }

instance poly_iface_arrow a3p t1 {| c1:poly_iface a3p t1 |} t2 {| c2:poly_iface a3p t2 |}
  : poly_iface a3p (mk_poly_arrow a3p t1 #c1.wt t2 #c2.wt)
  = { wt = witnessable_arrow t1 t2 _ _ }

type ttl_read (a3p:threep) =
  (#t:full_ground_typ) -> r:ref (to_Type t) ->
    ST (to_Type t)
      (requires (fun h0 -> inv a3p h0 /\ prref a3p r))
      (ensures  (fun h0 v h1 -> h0 `hrel a3p` h1 /\ inv a3p h1 /\ forall_refs (prref a3p) v))

type ttl_write (a3p:threep) =
  (#t:full_ground_typ) -> r:ref (to_Type t) -> v:(to_Type t) ->
    ST unit
      (requires (fun h0 -> inv a3p h0 /\ prref a3p r /\ forall_refs (prref a3p) v))
      (ensures  (fun h0 _ h1 -> h0 `hrel a3p` h1 /\ inv a3p h1))

type ttl_alloc (a3p:threep) =
  (#t:full_ground_typ) -> init:(to_Type t) ->
    ST (ref (to_Type t))
      (requires (fun h0 -> inv a3p h0 /\ forall_refs (prref a3p) init))
      (ensures  (fun h0 r h1 -> h0 `hrel a3p` h1 /\ inv a3p h1 /\ prref a3p r))

(** ** The concrete predicates **)

unfold
let c3p_hrel (h0:heap) (h1:heap) =
  modifies_only_shared_and_encapsulated h0 h1 /\ gets_shared Set.empty h0 h1

let c3p_hrel_trans (h0:heap) (h1:heap) (h2:heap)
: Lemma (requires (c3p_hrel h0 h1 /\ c3p_hrel h1 h2))
        (ensures  (c3p_hrel h0 h2))
        [SMTPat (c3p_hrel h0 h1); SMTPat (c3p_hrel h1 h2)]
=
  assert (modifies_only_shared_and_encapsulated h0 h2);
  introduce forall (a:Type) (rel:preorder a) (r:mref a rel).
    ((~ (Set.mem (addr_of r) Set.empty)) /\ h0 `contains` r) ==> kind_not_modified r h0 h2 with
  begin
    introduce ((~ (Set.mem (addr_of r) Set.empty)) /\ h0 `contains` r) ==> kind_not_modified r h0 h2 with _.
    begin
      assert ((sel h0 label_map) (addr_of r) = (sel h1 label_map) (addr_of r) /\
                h0 `contains` label_map <==> h1 `contains` label_map);
      assert ((sel h1 label_map) (addr_of r) = (sel h2 label_map) (addr_of r) /\
                h1 `contains` label_map <==> h2 `contains` label_map)
    end
  end

let c3p : threep = (
    (fun h ->
        trans_shared_contains h /\
        h `contains` label_map /\
        is_private (label_map) h /\
        (forall p. p >= next_addr h ==> is_private_addr p h)),
    (fun #a #rel (r:mref a rel) -> witnessed (contains_pred r) /\ witnessed (is_shareable r)),
    (fun h0 h1 -> c3p_hrel h0 h1)
)

unfold
let inv_c : heap -> Type0 = Mktuple3?._1 c3p
unfold
let prref_c : mref_pred = Mktuple3?._2 c3p
unfold
let hrel_c : preorder heap = Mktuple3?._3 c3p

let interm (l:Type) = poly_iface c3p l
unfold let pre_interm_arrow
  (#t1:Type) {| c1 : witnessable t1 |}
  (x:t1) (h0:heap) =
  inv_c h0 /\ c1.satisfy x prref_c

unfold let post_interm_arrow
  (#t2:Type) {| c2 : witnessable t2 |}
  (h0:heap) (r:t2) (h1:heap) =
  inv_c h1 /\ h0 `hrel_c` h1 /\ c2.satisfy r prref_c

#set-options "--print_universes"
let mk_interm_arrow
  (t1:Type u#a) {| c1 : witnessable t1 |}
  (t2:Type u#b) {| c2 : witnessable t2 |}
 : Type u#(max 1 a b)
= x:t1 -> ST t2
    (pre_interm_arrow x)
    (post_interm_arrow)


val tl_read : ttl_read c3p
let tl_read #t r =
  let h0 = get_heap () in
  recall (contains_pred r);
  recall (is_shareable r);
  let v = lr_read r in
  assert (forall_refs_heap contains_pred h0 v);
  assert (forall_refs_heap is_shareable h0 v);
  lemma_forall_refs_heap_forall_refs_witnessed v contains_pred;
  lemma_forall_refs_heap_forall_refs_witnessed v is_shareable;
  lemma_forall_refs_join v (fun r -> witnessed (contains_pred r)) (fun r -> witnessed (is_shareable r));
  v

val tl_write : ttl_write c3p
let tl_write #t r v =
  recall (contains_pred r);
  recall (is_shareable r);
  let h0 = get_heap () in
  lemma_forall_refs_split v (fun r -> witnessed (contains_pred r)) (fun r -> witnessed (is_shareable r));
  lemma_forall_refs_witnessed_forall_refs_heap v contains_pred;
  lemma_forall_refs_witnessed_forall_refs_heap v is_shareable;
  lr_write_shareable r v;
  let h1 = get_heap () in
  assert (modifies_only_shared h0 h1 /\ gets_shared Set.empty h0 h1);
  assert (trans_shared_contains h1);
  assert (h1 `contains` label_map);
  assert (is_private (label_map) h1);
  assert ((forall p. p >= next_addr h1 ==> is_private_addr p h1))

#push-options "--split_queries always"
val tl_alloc : ttl_alloc c3p
let tl_alloc #t init =
  assert (forall_refs (fun r' -> witnessed (contains_pred r') /\ witnessed (is_shareable r')) init);
  lemma_forall_refs_split init (fun r -> witnessed (contains_pred r)) (fun r -> witnessed (is_shareable r));
  lemma_forall_refs_witnessed_forall_refs_heap init contains_pred;
  lemma_forall_refs_witnessed_forall_refs_heap init is_shareable;
  let r = lr_alloc_shared init in
  witness (contains_pred r); witness (is_shareable r);
  r
#pop-options
