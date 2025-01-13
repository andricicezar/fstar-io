module FlagBasedEffPoly

open Labeled.Monotonic.Heap
open Labeled.MST
open Witnessable
open TargetLang
open STLC 

(** for the very general idea, look into experiments/FlagBasedEffPoly.fst **)

type fo_ctx =
  // fl:erased tflag -> (** we don't have flag yets for ST **)
  #inv:(lheap -> Type0) -> (** invariant on the heap **)
  #prref: (#a:Type -> #rel:_ -> mref a rel -> Type0) ->
  (** ^ if this predicate would be also over heaps, then the contexts needs witness&recall in HO settings **)
  read :  ((#t:typ0) -> x:ref (elab_typ0 t) -> 
            ST (elab_typ0 t) 
              (requires (fun h0 -> inv h0 /\ (elab_typ0_tc (TRef t)).satisfy_refinement x prref))
              (ensures  (fun h0 r h1 -> h0 == h1 /\ sel h1 x == r /\ (elab_typ0_tc t).satisfy_refinement r prref))) ->
  write : ((#t:typ0) -> x:ref (elab_typ0 t) -> v:(elab_typ0 t) -> 
            ST unit
              (requires (fun h0 -> inv h0 /\ (elab_typ0_tc (TRef t)).satisfy_refinement x prref /\ (elab_typ0_tc t).satisfy_refinement v prref))
              (ensures  (fun h0 _ h1 -> inv h1 /\ sel h1 x == v /\ modifies_only_label Low h0 h1 /\ modifies_classification Set.empty h0 h1))) ->
  alloc : ((#t:typ0) -> init:(elab_typ0 t) -> 
            ST (ref (elab_typ0 t)) 
              (requires (fun h0 -> inv h0 /\ (elab_typ0_tc t).satisfy_refinement init prref))
              (ensures  (fun h0 r h1 -> inv h1 /\ sel h1 r == init /\ (elab_typ0_tc (TRef t)).satisfy_refinement r prref /\ modifies_only_label Low h0 h1 /\ modifies_classification Set.empty h0 h1))) ->
  (** type of the context: *)
  unit -> ST unit (inv) (fun h0 _ h1 -> inv h1 /\ modifies_only_label Low h0 h1 /\ modifies_classification Set.empty h0 h1)

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
      assume (shallowly_contained_low v #(elab_typ0_tc t) h0); (** one has to recall on v. a method on witnessable, that given a `witnessed pred`, returns a `satisfy pred`. **)
      elab_write r v)
    (fun #t init -> (* ALLOC *)
      let h0 = get () in
      assume (shallowly_contained_low init #(elab_typ0_tc t) h0); (** one has to recall on init **)
      let r = elab_alloc init in 
      mst_witness (contains_pred r); mst_witness (is_low_pred r);
      r)


(** TODO: Can the context easily/automatically work with the pre- and post-conditions? **)

val ctx_update_ref_test : fo_ctx
let ctx_update_ref_test my_read my_write my_alloc () =
  let x = my_alloc 5 in
  let y = my_read x in
  my_write #TNat x (y+1);
  ()

type ho_ctx1 = (** only the type of the context is different **)
  // fl:erased tflag ->
  #inv:(lheap -> Type0) -> (** invariant on the heap **)
  #prref: (#a:Type -> #rel:_ -> mref a rel -> Type0) ->
  read :  ((#t:typ0) -> x:ref (elab_typ0 t) -> 
            ST (elab_typ0 t) 
              (requires (fun h0 -> inv h0 /\ (elab_typ0_tc (TRef t)).satisfy_refinement x prref))
              (ensures  (fun h0 r h1 -> h0 == h1 /\ sel h1 x == r /\ (elab_typ0_tc t).satisfy_refinement r prref))) ->
  write : ((#t:typ0) -> x:ref (elab_typ0 t) -> v:(elab_typ0 t) -> 
            ST unit
              (requires (fun h0 -> inv h0 /\ (elab_typ0_tc (TRef t)).satisfy_refinement x prref /\ (elab_typ0_tc t).satisfy_refinement v prref))
              (ensures  (fun h0 _ h1 -> inv h1 /\ sel h1 x == v /\ modifies_only_label Low h0 h1 /\ modifies_classification Set.empty h0 h1))) ->
  alloc : ((#t:typ0) -> init:(elab_typ0 t) -> 
            ST (ref (elab_typ0 t)) 
              (requires (fun h0 -> inv h0 /\ (elab_typ0_tc t).satisfy_refinement init prref))
              (ensures  (fun h0 r h1 -> inv h1 /\ sel h1 r == init /\ (elab_typ0_tc (TRef t)).satisfy_refinement r prref /\ modifies_only_label Low h0 h1 /\ modifies_classification Set.empty h0 h1))) ->
  (** type of the context: *)
  rr:ref (ref int) -> ST (r:ref int -> ST unit (fun h0 -> inv h0 /\ satisfy_refinement r prref) (fun h0 _ h1 -> inv h1 /\ modifies_only_label Low h0 h1 /\ modifies_classification Set.empty h0 h1))
    (requires (fun h0 -> inv h0 /\ satisfy_refinement rr prref))
    (ensures  (fun h0 _ h1 -> inv h1 /\ modifies_only_label Low h0 h1 /\ modifies_classification Set.empty h0 h1))

val ctx_update_multiple_refs_test : ho_ctx1
let ctx_update_multiple_refs_test my_read my_write my_alloc x y =
  let ix = my_read #(TRef TNat) x in
  my_write #(TRef TNat) x y;
  my_write #TNat y ((my_read #TNat y) + 5);
  ()


type ho_ctx2 =
  // fl:erased tflag ->
  #inv:(lheap -> Type0) -> (** invariant on the heap **)
  #prref: (#a:Type -> #rel:_ -> mref a rel -> Type0) ->
  read :  ((#t:typ0) -> x:ref (elab_typ0 t) -> 
            ST (elab_typ0 t) 
              (requires (fun h0 -> inv h0 /\ (elab_typ0_tc (TRef t)).satisfy_refinement x prref))
              (ensures  (fun h0 r h1 -> h0 == h1 /\ sel h1 x == r /\ (elab_typ0_tc t).satisfy_refinement r prref))) ->
  write : ((#t:typ0) -> x:ref (elab_typ0 t) -> v:(elab_typ0 t) -> 
            ST unit
              (requires (fun h0 -> inv h0 /\ (elab_typ0_tc (TRef t)).satisfy_refinement x prref /\ (elab_typ0_tc t).satisfy_refinement v prref))
              (ensures  (fun h0 _ h1 -> inv h1 /\ sel h1 x == v /\ modifies_only_label Low h0 h1 /\ modifies_classification Set.empty h0 h1))) ->
  alloc : ((#t:typ0) -> init:(elab_typ0 t) -> 
            ST (ref (elab_typ0 t)) 
              (requires (fun h0 -> inv h0 /\ (elab_typ0_tc t).satisfy_refinement init prref))
              (ensures  (fun h0 r h1 -> inv h1 /\ sel h1 r == init /\ (elab_typ0_tc (TRef t)).satisfy_refinement r prref /\ modifies_only_label Low h0 h1 /\ modifies_classification Set.empty h0 h1))) ->
  (** type of the context: *)
  rr:ref ((ref int) * (ref int)) -> ST (unit -> ST unit (fun h0 -> inv h0) (fun h0 _ h1 -> inv h1 /\ modifies_only_label Low h0 h1 /\ modifies_classification Set.empty h0 h1))
    (requires (fun h0 -> inv h0 /\ satisfy_refinement rr prref))
    (ensures  (fun h0 _ h1 -> inv h1 /\ modifies_only_label Low h0 h1 /\ modifies_classification Set.empty h0 h1))

val ctx_HO_test1 : ho_ctx2
let ctx_HO_test1 #inv #prref my_read my_write my_alloc rr =
  let (x', x'') = my_read #(TPair (TRef TNat) (TRef TNat)) rr in
  my_write #(TPair (TRef TNat) (TRef TNat)) rr (x', x');
  (fun _ ->
    my_write #(TPair (TRef TNat) (TRef TNat)) rr (x', x''))