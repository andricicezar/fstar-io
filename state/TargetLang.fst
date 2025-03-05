module TargetLang

open FStar.Tactics
open FStar.Tactics.Typeclasses
open FStar.Ghost
open FStar.Preorder
open FStar.Universe

open SharedRefs
open Witnessable

instance witnessable_shareable_type (t:Type) {| c:tc_shareable_type t |} : witnessable t = {
  satisfy = (fun x pred -> forall_refs pred #c.__t x);
}

type targetlang_pspec =
  (inv:heap -> Type0) * (prref:mref_pred) * (hrel:preorder heap)

unfold
let mk_targetlang_pspec
  (inv  : heap -> Type0)
  (prref: mref_pred)
  (hrel : preorder heap)
  : targetlang_pspec =
  (inv, (prref <: (#a:Type0 -> #rel:preorder a -> mref a rel -> Type0)), hrel)

class targetlang (spec:targetlang_pspec) (t:Type u#a) =
  { wt : witnessable t }

instance targetlang_shareable_type pspec (t:Type) {| c:tc_shareable_type t |} : targetlang pspec t = {
  wt = witnessable_shareable_type t #c;
}

instance targetlang_unit pspec : targetlang pspec unit = { wt = witnessable_unit }
instance targetlang_int  pspec : targetlang pspec int = { wt = witnessable_int }
instance targetlang_pair pspec t1 t2 {| c1:targetlang pspec t1 |} {| c2:targetlang pspec t2 |}
  : targetlang pspec (t1 * t2)
  = { wt = witnessable_pair t1 t2 #c1.wt #c2.wt }
instance targetlang_univ_raise pspec (t1:Type u#a) {| c1:targetlang pspec t1 |}
  : targetlang pspec (FStar.Universe.raise_t u#a u#b t1)
  = { wt = witnessable_univ_raise t1 #c1.wt }
instance targetlang_sum pspec t1 t2 {| c1:targetlang pspec t1 |} {| c2:targetlang pspec t2 |}
  : targetlang pspec (either t1 t2)
  = { wt = witnessable_sum t1 t2 #c1.wt #c2.wt }
instance targetlang_option pspec t1 {| c1:targetlang pspec t1 |}
  : targetlang pspec (option t1)
  = { wt = witnessable_option t1 #c1.wt }
instance targetlang_ref pspec t1 {| c1:tc_shareable_type t1 |}
  : targetlang pspec (ref t1)
  = { wt = witnessable_mref t1 (FStar.Heap.trivial_preorder t1) #solve }
instance targetlang_list pspec t1 {| c1:targetlang pspec t1 |}
  : targetlang pspec (list t1)
  = { wt = witnessable_list t1 #c1.wt }
instance targetlang_llist pspec t1 {| c1:tc_shareable_type t1 |}
  : targetlang pspec (linkedList t1)
  = { wt = witnessable_llist t1 #solve }

unfold let pre_targetlang_arrow
  (pspec:targetlang_pspec)
  (#t1:Type) {| c1 : witnessable t1 |}
  (x:t1) (h0:heap) =
  (Mktuple3?._1 pspec) h0 /\ c1.satisfy x (Mktuple3?._2 pspec)

unfold let post_targetlang_arrow
  (pspec:targetlang_pspec)
  (#t2:Type) {| c2 : witnessable t2 |}
  (h0:heap) (r:t2) (h1:heap) =
  (Mktuple3?._1 pspec) h1 /\ h0 `(Mktuple3?._3 pspec)` h1 /\ c2.satisfy r (Mktuple3?._2 pspec)

let mk_targetlang_arrow
  (pspec:targetlang_pspec)
  (t1:Type u#a) {| c1 : witnessable t1 |}
  (t2:Type u#b) {| c2 : witnessable t2 |}
= x:t1 -> ST t2
    (pre_targetlang_arrow pspec x)
    (post_targetlang_arrow pspec)

instance targetlang_arrow pspec t1 t2 {| c1:targetlang pspec t1 |} {| c2:targetlang pspec t2 |}
  : targetlang pspec (mk_targetlang_arrow pspec t1 #c1.wt t2 #c2.wt)
  = { wt = witnessable_arrow t1 t2 _ _ }

type ttl_read (inv:heap -> Type0) (prref:mref_pred) (hrel:preorder heap) =
  (#t:shareable_typ) -> r:ref (to_Type t) ->
    ST (to_Type t)
      (requires (fun h0 -> inv h0 /\ prref r))
      (ensures  (fun h0 v h1 -> h0 `hrel` h1 /\ inv h1 /\ forall_refs prref v))

type ttl_write (inv:heap -> Type0) (prref:mref_pred) (hrel:preorder heap) =
  (#t:shareable_typ) -> r:ref (to_Type t) -> v:(to_Type t) ->
    ST unit
      (requires (fun h0 -> inv h0 /\ prref r /\ forall_refs prref v))
      (ensures  (fun h0 _ h1 -> h0 `hrel` h1 /\ inv h1))

type ttl_alloc (inv:heap -> Type0) (prref:mref_pred) (hrel:preorder heap) =
  (#t:shareable_typ) -> init:(to_Type t) ->
    ST (ref (to_Type t))
      (requires (fun h0 -> inv h0 /\ forall_refs prref init))
      (ensures  (fun h0 r h1 -> h0 `hrel` h1 /\ inv h1 /\ prref r))

(** ** interm language **)

unfold
let concrete_spec_rel (h0:heap) (h1:heap) =
  modifies_only_shared_and_encapsulated h0 h1 /\ gets_shared Set.empty h0 h1

let concrete_spec_rel_trans (h0:heap) (h1:heap) (h2:heap)
: Lemma (requires (concrete_spec_rel h0 h1 /\ concrete_spec_rel h1 h2))
        (ensures  (concrete_spec_rel h0 h2))
        [SMTPat (concrete_spec_rel h0 h1); SMTPat (concrete_spec_rel h1 h2)]
=
  assert (modifies_only_shared_and_encapsulated h0 h2);
  introduce forall (a:Type) (rel:preorder a) (r:mref a rel).
    ((~ (Set.mem (addr_of r) Set.empty)) /\ h0 `contains` r) ==> kind_not_modified r h0 h2 with
  begin
    introduce ((~ (Set.mem (addr_of r) Set.empty)) /\ h0 `contains` r) ==> kind_not_modified r h0 h2 with _.
    begin
      assert ((sel h0 map_shared) (addr_of r) = (sel h1 map_shared) (addr_of r) /\
                h0 `contains` map_shared <==> h1 `contains` map_shared);
      assert ((sel h1 map_shared) (addr_of r) = (sel h2 map_shared) (addr_of r) /\
                h1 `contains` map_shared <==> h2 `contains` map_shared)
    end
  end

let concrete_spec : targetlang_pspec = (
    (fun h ->
        trans_shared_contains h /\
        h `contains` map_shared /\
        is_private (map_shared) h /\
        (forall p. p >= next_addr h ==> is_private_addr p h)),
    (fun #a #rel (r:mref a rel) -> witnessed (contains_pred r) /\ witnessed (is_shared r)),
    (fun h0 h1 -> concrete_spec_rel h0 h1)
)

unfold
let inv_c : heap -> Type0 = Mktuple3?._1 concrete_spec
unfold
let prref_c : mref_pred = Mktuple3?._2 concrete_spec
unfold
let hrel_c : preorder heap = Mktuple3?._3 concrete_spec

let interm (l:Type) = targetlang concrete_spec l
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


val tl_read : ttl_read (inv_c) (prref_c) (hrel_c)
let tl_read #t r =
  let h0 = get_heap () in
  recall (contains_pred r);
  recall (is_shared r);
  let v = sst_read r in
  assert (forall_refs_heap contains_pred h0 v);
  assert (forall_refs_heap is_shared h0 v);
  lemma_forall_refs_heap_forall_refs_witnessed v contains_pred;
  lemma_forall_refs_heap_forall_refs_witnessed v is_shared;
  lemma_forall_refs_join v (fun r -> witnessed (contains_pred r)) (fun r -> witnessed (is_shared r));
  v

val tl_write : ttl_write (inv_c) (prref_c) (hrel_c)
let tl_write #t r v =
  recall (contains_pred r);
  recall (is_shared r);
  let h0 = get_heap () in
  lemma_forall_refs_split v (fun r -> witnessed (contains_pred r)) (fun r -> witnessed (is_shared r));
  lemma_forall_refs_witnessed_forall_refs_heap v contains_pred;
  lemma_forall_refs_witnessed_forall_refs_heap v is_shared;
  sst_write_shareable r v;
  let h1 = get_heap () in
  assert (modifies_only_shared h0 h1 /\ gets_shared Set.empty h0 h1);
  assert (trans_shared_contains h1);
  assert (h1 `contains` map_shared);
  assert (is_private (map_shared) h1);
  assert ((forall p. p >= next_addr h1 ==> is_private_addr p h1))

#push-options "--split_queries always"
val tl_alloc : ttl_alloc (inv_c) (prref_c) (hrel_c)
let tl_alloc #t init =
  assert (forall_refs (fun r' -> witnessed (contains_pred r') /\ witnessed (is_shared r')) init);
  lemma_forall_refs_split init (fun r -> witnessed (contains_pred r)) (fun r -> witnessed (is_shared r));
  lemma_forall_refs_witnessed_forall_refs_heap init contains_pred;
  lemma_forall_refs_witnessed_forall_refs_heap init is_shared;
  let r = sst_alloc_shared init in
  witness (contains_pred r); witness (is_shared r);
  r
#pop-options
