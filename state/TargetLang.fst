module TargetLang

open FStar.Tactics
open FStar.Tactics.Typeclasses

open Labeled.Monotonic.Heap
open Labeled.MST
open Witnessable

unfold let shallowly_contained_low (#a:Type) {| c:witnessable a |} (v:a) (h:lheap) =
  c.satisfy v h contains_pred /\ c.satisfy v h is_low_pred

unfold let pre_tgt_arrow
  (#t1:Type) {| c1 : witnessable t1 |}
  (#inv:lheap -> Type0)
  (x:t1) (h0:lheap) =
  inv h0 /\
  shallowly_contained_low #t1 #c1 x h0

unfold let post_tgt_arrow
  (#t1:Type) {| c1 : witnessable t1 |}
  (#t2:Type) {| c2 : witnessable t2 |}
  (#inv:lheap -> Type0)
  (x:t1) (h0:lheap) (r:t2) (h1:lheap) =
  inv h1 /\
  modifies_only_label Low h0 h1 /\                       (* allows low references to be modified *)
  modifies_classification Set.empty h0 h1 /\             (* no modifications of the classification *)
  shallowly_contained_low #t2 #c2 r h1

let mk_tgt_arrow 
  (inv:lheap -> Type0)
  (t1:Type) {| c1 : witnessable t1 |}
  (t2:Type) {| c2 : witnessable t2 |}
= x:t1 -> ST t2 
    (requires (pre_tgt_arrow #t1 #c1 #inv x ))
    (ensures (post_tgt_arrow #t1 #c1 #t2 #c2 #inv x))

(** _elab_typ should be in translation file, but it is here because 
    we need it to write our invariants **)
open STLC

let rec _elab_typ (t:typ) (inv:lheap -> Type0): tt:Type0 & witnessable tt =
  match t with
  | TArr t1 t2 -> begin
    let tt1 = _elab_typ t1 inv in
    let tt2 = _elab_typ t2 inv in
    (| mk_tgt_arrow inv (dfst tt1) #(dsnd tt1) (dfst tt2) #(dsnd tt2),
       witnessable_arrow (dfst tt1) (dfst tt2) pre_tgt_arrow post_tgt_arrow
    |)
  end 
  | TUnit -> (| unit, witnessable_unit |)
  | TNat -> (| int, witnessable_int |)
  | TSum t1 t2 ->
    let (| tt1, c_tt1 |) = _elab_typ t1 inv in
    let (| tt2, c_tt2 |) = _elab_typ t2 inv in
    (| either tt1 tt2, witnessable_sum tt1 tt2 #c_tt1 #c_tt2 |)
  | TPair t1 t2 ->
    let (| tt1, c_tt1 |) = _elab_typ t1 inv in
    let (| tt2, c_tt2 |) = _elab_typ t2 inv in
    (| (tt1 * tt2), witnessable_pair tt1 tt2 #c_tt1 #c_tt2 |)
  | TRef t ->
    let (| tt, c_tt |) = _elab_typ t inv in
    (| ref tt, witnessable_ref tt #c_tt |)
  | TLList t ->
    let (| tt, c_tt |) = _elab_typ t inv in
    (| linkedList tt, witnessable_llist tt #c_tt |)

let elab_typ (t:typ) (hinv:lheap -> Type0) : Type =
  dfst (_elab_typ t hinv)

let elab_typ_tc (t:typ) (hinv:lheap -> Type0) : witnessable (elab_typ t hinv)=
  dsnd (_elab_typ t hinv)

let inv_points_to (h:lheap) pred =
  // forall (a:Type) (c:witnessable a) (r:ref a). 
  //   (witnessable_ref _ #c).satisfy r h pred ==>
  //     c.satisfy (sel h r) h pred
  // CA: previous version does not work because in proofs, one needs to prove a property like:
  // forall (a:Type) (c:witnessable a) (c':witnessable a) (r:ref a).
  //   c.satisfy r h pred ==> c'.satisfy r h pred

  // however, the following version needs an inversion lemma that cannot be proven in F* yet
  // because one cannot reason about the types of effectful arrows. e.g., `int =!= int -> ST int` cannot be proven
  (forall (a:typ) (inv:lheap -> Type0) (r:ref (elab_typ a inv)).
    (witnessable_ref _ #(elab_typ_tc a inv)).satisfy r h pred ==> 
      (elab_typ_tc a inv).satisfy (sel h r) h pred)

let inv_low_contains (h:lheap) = 
  inv_points_to h contains_pred /\ inv_points_to h is_low_pred


let eliminate_inv_points_to (h:lheap) (a:typ) (hinv:lheap -> Type0) (r:ref (elab_typ a hinv)) pred :
  Lemma
    (requires (inv_points_to h pred))
    (ensures (
      (witnessable_ref (elab_typ a hinv) #(elab_typ_tc a hinv)).satisfy r h pred ==> 
        (elab_typ_tc a hinv).satisfy (sel h r) h pred
    )) = ()

let eliminate_inv_low (h:lheap) (a:typ) (hinv:lheap -> Type0) (r:ref (elab_typ a hinv)) :
  Lemma
    (requires (inv_points_to h is_low_pred))
    (ensures (
      (witnessable_ref (elab_typ a hinv) #(elab_typ_tc a hinv)).satisfy r h is_low_pred ==> 
        (elab_typ_tc a hinv).satisfy (sel h r) h is_low_pred
    )) = ()

let eliminate_inv_contains (h:lheap) (a:typ) (hinv:lheap -> Type0) (r:ref (elab_typ a hinv)) :
  Lemma
    (requires (inv_points_to h contains_pred))
    (ensures (
      (witnessable_ref (elab_typ a hinv) #(elab_typ_tc a hinv)).satisfy r h contains_pred ==> 
        (elab_typ_tc a hinv).satisfy (sel h r) h contains_pred
    )) = ()

effect IST (a:Type) (pre:st_pre) (post: (h:lheap -> Tot (st_post' a (pre h)))) =
  ST a 
    (requires (fun h0      -> inv_low_contains h0 /\ pre h0))
    (ensures  (fun h0 r h1 -> inv_low_contains h1 /\ post h0 r h1))

