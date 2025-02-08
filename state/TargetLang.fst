module TargetLang

open FStar.Tactics
open FStar.Tactics.Typeclasses

open SharedRefs
open Witnessable

type targetlang_pspec = 
  (inv:heap -> Type0) * (prref:mref_pred) * (hrel:FStar.Preorder.preorder heap)

class targetlang (spec:targetlang_pspec) (t:Type) = 
  { wt : witnessable t }

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
instance targetlang_ref pspec t1 {| c1:targetlang pspec t1 |} 
  : targetlang pspec (ref t1)
  = { wt = witnessable_mref t1 (FStar.Heap.trivial_preorder t1) #c1.wt }
instance targetlang_llist pspec t1 {| c1:targetlang pspec t1 |} 
  : targetlang pspec (linkedList t1)
  = { wt = witnessable_llist t1 #c1.wt }

unfold let pre_targetlang_arrow
  (inv:heap -> Type0)
  (prref:mref_pred)
  (#t1:Type) {| c1 : witnessable t1 |}
  (x:t1) (h0:heap) =
  inv h0 /\ c1.satisfy x prref

unfold let post_targetlang_arrow
  (inv:heap -> Type0)
  (prref:mref_pred)
  (hrel:FStar.Preorder.preorder heap)
  (#t1:Type) {| c1 : witnessable t1 |}
  (#t2:Type) {| c2 : witnessable t2 |}
  (x:t1) (h0:heap) (r:t2) (h1:heap) =
  inv h1 /\ h0 `hrel` h1 /\ c2.satisfy r prref

let mk_targetlang_arrow
  (pspec:targetlang_pspec)
  (t1:Type) {| c1 : witnessable t1 |}
  (t2:Type) {| c2 : witnessable t2 |}
= x:t1 -> ST t2 
    (requires (fun h0 -> (Mktuple3?._1 pspec) h0 /\ c1.satisfy x (Mktuple3?._2 pspec))) (** CA: super stupid that one has to use projectors **)
    (ensures (fun h0 r h1 -> (Mktuple3?._1 pspec) h1 /\ h0 `(Mktuple3?._3 pspec)` h1 /\ c2.satisfy r (Mktuple3?._2 pspec)))

instance targetlang_arrow pspec t1 t2 {| c1:targetlang pspec t1 |} {| c2:targetlang pspec t2 |}
  : targetlang pspec (mk_targetlang_arrow pspec t1 #c1.wt t2 #c2.wt)
  = { wt = witnessable_arrow t1 t2 _ _ }

let default_spec : targetlang_pspec = (
    (fun h -> 
        trans_shared_contains h /\
        h `contains` map_shared /\ 
        ~(is_shared (map_shared) h) /\
        (forall p. p >= next_addr h ==> ~(sel h map_shared p))),
    (fun #a #rel (r:mref a rel) -> witnessed (contains_pred r) /\ witnessed (is_shared r)),
    (fun h0 h1 -> modifies_only_shared h0 h1 /\ gets_shared Set.empty h0 h1)
)
