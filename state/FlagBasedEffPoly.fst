module FlagBasedEffPoly

open Labeled.Monotonic.Heap
open Labeled.MST
open Witnessable
open TargetLang
open STLC 

(** for the very general idea, look into experiments/FlagBasedEffPoly.fst **)

type fo_ctx =
  #inv:(lheap -> Type0) -> (** invariant on the heap **)
  #prref: (#a:Type -> #rel:_ -> mref a rel -> Type0) ->
  #hrel:FStar.Preorder.preorder lheap ->
 // #hrel:(rel:(lheap -> lheap -> Type0){FStar.Preorder.transitive rel}) -> (** because of the hrel, we may not need the flag because even if the context uses operations directly, it cannot prove that it preserves the hrel**)
  (** ^ if this predicate would be also over heaps, then the contexts needs witness&recall in HO settings **)
  read :  ((#t:typ0) -> r:ref (elab_typ0 t) -> 
            ST (elab_typ0 t) 
              (requires (fun h0 -> inv h0 /\ prref r))
              (ensures  (fun h0 v h1 -> h0 `hrel` h1 /\ inv h1 /\ (** prref r /\**) (elab_typ0_tc t).satisfy_refinement v prref))) -> // sel h1 r == v /\
  write : ((#t:typ0) -> r:ref (elab_typ0 t) -> v:(elab_typ0 t) -> 
            ST unit
              (requires (fun h0 -> inv h0 /\ prref r /\ (elab_typ0_tc t).satisfy_refinement v prref))
              (ensures  (fun h0 _ h1 -> h0 `hrel` h1 /\ inv h1 (**/\ prref r /\ (elab_typ0_tc t).satisfy_refinement v prref **)))) -> // /\ sel h1 r == v 
  alloc : ((#t:typ0) -> init:(elab_typ0 t) -> 
            ST (ref (elab_typ0 t)) 
              (requires (fun h0 -> inv h0 /\ (elab_typ0_tc t).satisfy_refinement init prref))
              (ensures  (fun h0 r h1 -> h0 `hrel` h1 /\ inv h1 /\ prref r (** /\ (elab_typ0_tc t).satisfy_refinement init prref **)))) -> // sel h1 r == init /\  
  (** type of the context: *)
  unit -> ST unit (inv) (fun h0 _ h1 -> inv h1 /\ h0 `hrel` h1)

(** Checking if there exists read, write, alloc so that we can instantiate the polymorphic context **)

unfold
let is_low_pred' r : pred:heap_predicate{stable pred} = (* F* being silly. There is an SMTPat on is_low_pred_stable **)
  let pred = is_low_pred r in
  is_low_pred_stable r;
  pred
 
let check_instantiating_the_context (ctx:fo_ctx) = 
  ctx
    #(fun h -> inv_low_contains h)
    #(fun r -> witnessed (contains_pred r) /\ witnessed (is_low_pred' r)) 
    #(fun h0 h1 -> modifies_only_label Low h0 h1 /\ modifies_classification Set.empty h0 h1)
    (fun #t r -> (* READ *)
      let h0 = get () in
      mst_recall (contains_pred r); 
      mst_recall (is_low_pred r);
      let v = read r in
      assert ((elab_typ0_tc t).satisfy v h0 contains_pred);
      assert ((elab_typ0_tc t).satisfy v h0 is_low_pred);
      assume ((elab_typ0_tc t).satisfy_refinement v (fun r' -> witnessed (contains_pred r') /\ witnessed (is_low_pred' r'))); (** one can create witnesses using the previous assertions **)
      v) 
    (fun #t r v -> (* WRITE *)
      mst_recall (contains_pred r); 
      mst_recall (is_low_pred r); 
      let h0 = get () in
      assert ((elab_typ0_tc t).satisfy_refinement v (fun r' -> witnessed (contains_pred r') /\ witnessed (is_low_pred' r')));
      assume (shallowly_contained_low v #(elab_typ0_tc t) h0); (** one has to recall on v. a method on witnessable, that given a `witnessed pred`, returns a `satisfy pred`. **)
      elab_write r v)
    (fun #t init -> (* ALLOC *)
      let h0 = get () in
      assert ((elab_typ0_tc t).satisfy_refinement init (fun r' -> witnessed (contains_pred r') /\ witnessed (is_low_pred' r')));
      assume (shallowly_contained_low init #(elab_typ0_tc t) h0); (** one has to recall on init **)
      let r = elab_alloc init in 
      mst_witness (contains_pred r); mst_witness (is_low_pred r);
      r)


(** TODO: Can the context easily/automatically work with the pre- and post-conditions? **)


open FStar.Tactics

(** CA: this test fails if the relation is not reflexive **)
val ctx_pure : fo_ctx
let ctx_pure #inv #_ #hrel my_read my_write my_alloc () : ST unit (inv) (fun h0 _ h1 -> inv h1 /\ h0 `hrel` h1) by (
  explode ();
     let bi = nth_binder (-2) in
     let (_, fl) = destruct_and bi in
     clear bi;
     let fl' = instantiate fl (nth_binder (-3)) in
     clear fl;
     let fl'' = instantiate fl' (nth_binder (-4)) in
     clear fl';
  dump "H"
)=
  ()
  
  
val ctx_update_ref_test : fo_ctx
let ctx_update_ref_test my_read my_write my_alloc () =
  let x = my_alloc 5 in
  let y = my_read x in
  my_write #TNat x (y+1);
  ()

type ho_ctx1 = (** only the type of the context is different **)
  #inv:(lheap -> Type0) -> (** invariant on the heap **)
  #prref: (#a:Type -> #rel:_ -> mref a rel -> Type0) ->
  #hrel:(FStar.Preorder.preorder lheap) ->
  (** ^ if this predicate would be also over heaps, then the contexts needs witness&recall in HO settings **)
  read :  ((#t:typ0) -> r:ref (elab_typ0 t) -> 
            ST (elab_typ0 t) 
              (requires (fun h0 -> inv h0 /\ prref r))
              (ensures  (fun h0 v h1 -> h0 `hrel` h1 /\ inv h1 /\ (** prref r /\**) (elab_typ0_tc t).satisfy_refinement v prref))) -> // sel h1 r == v /\
  write : ((#t:typ0) -> r:ref (elab_typ0 t) -> v:(elab_typ0 t) -> 
            ST unit
              (requires (fun h0 -> inv h0 /\ prref r /\ (elab_typ0_tc t).satisfy_refinement v prref))
              (ensures  (fun h0 _ h1 -> h0 `hrel` h1 /\ inv h1 (**/\ prref r /\ (elab_typ0_tc t).satisfy_refinement v prref **)))) -> // /\ sel h1 r == v 
  alloc : ((#t:typ0) -> init:(elab_typ0 t) -> 
            ST (ref (elab_typ0 t)) 
              (requires (fun h0 -> inv h0 /\ (elab_typ0_tc t).satisfy_refinement init prref))
              (ensures  (fun h0 r h1 -> h0 `hrel` h1 /\ inv h1 /\ prref r (** /\ (elab_typ0_tc t).satisfy_refinement init prref **)))) -> // sel h1 r == init /\  
  (** type of the context: *)
  rr:ref (ref int) -> ST (r:ref int -> ST unit (fun h0 -> inv h0 /\ prref r) (fun h0 _ h1 -> inv h1 /\ hrel h0 h1))
    (requires (fun h0 -> inv h0 /\ prref rr))
    (ensures  (fun h0 _ h1 -> inv h1 /\ hrel h0 h1))

val ctx_update_multiple_refs_test : ho_ctx1
let ctx_update_multiple_refs_test #inv #prref #hrel my_read my_write my_alloc x y =
  let ix = my_read #(TRef TNat) x in
  my_write #(TRef TNat) x y;
  my_write #TNat y ((my_read #TNat y) + 5);
  ()


type ho_ctx2 =
  #inv:(lheap -> Type0) -> (** invariant on the heap **)
  #prref: (#a:Type -> #rel:_ -> mref a rel -> Type0) ->
  #hrel:(rel:(lheap -> lheap -> Type0){FStar.Preorder.transitive rel}) -> (** because of the hrel, we may not need the flag because even if the context uses operations directly, it cannot prove that it preserves the hrel**)
  (** ^ if this predicate would be also over heaps, then the contexts needs witness&recall in HO settings **)
  read :  ((#t:typ0) -> r:ref (elab_typ0 t) -> 
            ST (elab_typ0 t) 
              (requires (fun h0 -> inv h0 /\ prref r))
              (ensures  (fun h0 v h1 -> inv h1 /\ prref r /\ (elab_typ0_tc t).satisfy_refinement v prref /\ h0 `hrel` h1))) -> // sel h1 r == v /\
  write : ((#t:typ0) -> r:ref (elab_typ0 t) -> v:(elab_typ0 t) -> 
            ST unit
              (requires (fun h0 -> inv h0 /\ prref r /\ (elab_typ0_tc t).satisfy_refinement v prref))
              (ensures  (fun h0 _ h1 -> inv h1 /\ prref r /\ h0 `hrel` h1 /\ (elab_typ0_tc t).satisfy_refinement v prref))) -> // /\ sel h1 r == v 
  alloc : ((#t:typ0) -> init:(elab_typ0 t) -> 
            ST (ref (elab_typ0 t)) 
              (requires (fun h0 -> inv h0 /\ (elab_typ0_tc t).satisfy_refinement init prref))
              (ensures  (fun h0 r h1 -> inv h1 /\ prref r /\ h0 `hrel` h1 /\ (elab_typ0_tc t).satisfy_refinement init prref))) -> // sel h1 r == init /\  
  (** type of the context: *)
  rr:ref ((ref int) * (ref int)) -> ST (unit -> ST unit (fun h0 -> inv h0) (fun h0 _ h1 -> inv h1 /\ h0 `hrel` h1))
    (requires (fun h0 -> inv h0 /\ prref rr))
    (ensures  (fun h0 _ h1 -> inv h1 /\ h0 `hrel` h1))

val ctx_HO_test1 : ho_ctx2
let ctx_HO_test1 #inv #prref my_read my_write my_alloc rr =
  let (x', x'') = my_read #(TPair (TRef TNat) (TRef TNat)) rr in
  my_write #(TPair (TRef TNat) (TRef TNat)) rr (x', x');
  (fun _ ->
    my_write #(TPair (TRef TNat) (TRef TNat)) rr (x', x''))
