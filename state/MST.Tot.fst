module MST.Tot


open FStar.Tactics
open FStar.Preorder
open FStar.Monotonic.Heap
open FStar.Ghost
include MST.Repr (** just for witnessed **)

(** Flag-based effect polymorphsim **)

type tflag =
| All
| None

let rec satisfies #a (t : free a) (f : tflag) =
  match f with
  | All -> True
  | None ->
    begin match t with
    | Return x -> True
    | Read r cont -> False
    | Write r v cont -> False
    | Alloc init cont -> False
    | Witness pred cont -> cont () `satisfies` f
    | Recall pred cont -> cont () `satisfies` f
    | PartialCall pre fnc -> forall r. fnc r  `satisfies` f
    | GetHeap cont -> False
    end

let (⊕) (flag1:tflag) (flag2:tflag) : tflag =
  match flag1, flag2 with
  | None, None -> None
  | None, fl -> fl
  | fl, None -> fl
  | _, _ -> All

let (≼) (flag1:tflag) (flag2:tflag) : Type0 =
  match flag1, flag2 with
  | None, _ -> True
  | All, All -> True
  | All, _ -> False

let plus_compat_le (f1 f2 : tflag) : Lemma (f1 ≼ (f1⊕f2)) = ()
let plus_comm      (f1 f2 : tflag) : Lemma (f1⊕f2 == f2⊕f1) = ()

let rec sat_le (f1:tflag) (f2:tflag{f1 ≼ f2}) (m : free 'a) :
  Lemma (satisfies m f1 ==> satisfies m f2) =
  match m with
  | Return _ -> ()
  | Alloc _ o
  | Witness _ o
  | Recall _ o
  | Read _ o
  | PartialCall _ o ->
    Classical.forall_intro
     ((fun r -> sat_le f1 f2 (o r)) <: r:_ -> Lemma (satisfies (o r) f1 ==> satisfies (o r) f2))
  | Write r v o -> ()
  | GetHeap cont -> ()

let rec sat_bind (fl:tflag) (v : free 'a) (f : 'a -> free 'b) :
  Lemma (
    v `satisfies` fl /\ (forall x. f x `satisfies` fl) ==>
    free_bind v f `satisfies` fl
  )
= match v with
  | Return _ -> ()
  | PartialCall i o
  | Alloc i o
  | Witness i o
  | Recall i o
  | Read i o ->
    Classical.forall_intro
      ((fun r -> sat_bind fl (o r) f) <: r:_ -> Lemma ((o r) `satisfies` fl /\ (forall x. f x `satisfies` fl) ==> free_bind (o r) f `satisfies` fl))
  | Write r v o -> ()
  | GetHeap cont -> ()

let sat_bind_add (fl_v fl_f:tflag) (v : free 'a) (f : 'a -> free 'b) :
  Lemma (
    v `satisfies` fl_v /\ (forall x. f x `satisfies` fl_f) ==>
    free_bind v f `satisfies` (fl_v ⊕ fl_f)
  )
  =
  sat_le fl_v (fl_v ⊕ fl_f) v;
  let aux x : Lemma (f x `satisfies` fl_f ==> f x `satisfies` (fl_v ⊕ fl_f)) =
    sat_le fl_f (fl_v ⊕ fl_f) (f x)
  in
  Classical.forall_intro aux;
  sat_bind (fl_v ⊕ fl_f) v f

(* Total state effect --- the heap is first-order *)

let st_pre   = st_pre_h   heap
let st_post' = st_post_h' heap
let st_post  = st_post_h  heap
let st_wp    = st_mwp_h   heap

val mheap : (a:Type u#a) -> erased tflag -> st_wp a -> Type u#(max 1 a)
let mheap a f w = t: mst a w { t `satisfies` f }

val mheap_bind :
  (a : Type u#a) ->
  (b : Type u#b) ->
  (fv : erased tflag) ->
  (wp_v : st_wp a) ->
  (ff : erased tflag) ->
  wp_f: (a -> st_wp b) ->
  (v : mheap a fv wp_v) ->
  (f : (x:a -> mheap b ff (wp_f x))) ->
  Tot (mheap b (fv ⊕ ff) (st_bind_wp heap a b wp_v wp_f))
let mheap_bind a b ff wp_v fv wp_f v f =
  sat_bind_add fv ff v f ;
  mst_bind #a #b #wp_v #wp_f v f

let mheap_return (a : Type) (x : a) :
  mheap a None (st_return heap a x) by (compute ())
= mst_return x


val mheap_subcomp :
  (a : Type u#a) ->
  (flag1 : erased tflag) ->
  (wp1 : st_wp a) ->
  (flag2 : erased tflag) ->
  (wp2 : st_wp a) ->
  (v : mheap a flag1 wp1) ->
  Pure (mheap a flag2 wp2) (requires flag1 ≼ flag2 /\ wp1 ⊑ wp2) (ensures (fun _ -> True))
let mheap_subcomp a flag1 wp1 flag2 wp2 v =
  sat_le flag1 flag2 v ;
  mst_subcomp v

let mheap_if_then_else (a : Type u#a)
  (flag1 : erased tflag)
  (#wp1 : st_wp a)
  (flag2 : erased tflag)
  (#wp2 : st_wp a)
  (f : mheap a flag1 wp1) (g : mheap a flag2 wp2) (b : bool) : Type =
  mheap a (flag1 ⊕ flag2) (st_if_then_else heap a b wp1 wp2)

[@@ top_level_effect]
total
reifiable
reflectable
effect {
  STATEwp (a:Type) (flag:erased tflag) (wp : st_wp a)
  with {
    repr         = mheap ;
    return       = mheap_return ;
    bind         = mheap_bind ;
    subcomp      = mheap_subcomp ;
    if_then_else = mheap_if_then_else
  }
}

effect ST (a:Type) (fl:tflag) (pre:st_pre) (post: (h:heap -> Tot (st_post' a (pre h)))) =
  STATEwp a fl (fun (p:st_post a) (h0:heap) -> pre h0 /\ (forall a h1. h0 `heap_rel` h1 /\ post h0 a h1 ==> p a h1))
effect St (a:Type) = ST a None (fun h -> True) (fun h0 r h1 -> True)

unfold
let wp_lift_pure_st (w : pure_wp 'a) : st_wp 'a =
  FStar.Monotonic.Pure.elim_pure_wp_monotonicity_forall ();
  fun p h -> w (fun r -> p r h)

val lift_pure_mst :
  a: Type u#a ->
  w: pure_wp a ->
  f: (eqtype_as_type unit -> PURE a w) ->
  Tot (mheap a None (wp_lift_pure_st w))
let lift_pure_mst a w f =
  FStar.Monotonic.Pure.elim_pure_wp_monotonicity_forall ();
  let lhs = partial_return (as_requires w) in
  let rhs = (fun (pre:(squash (as_requires w))) -> mheap_return a (f pre)) in
  let m = mheap_bind _ _ None _ _ _ lhs rhs in
  mheap_subcomp _ _ _ _ _ m

sub_effect PURE ~> STATEwp = lift_pure_mst

let contains_pred (#a:Type) (#rel:preorder a) (r:mref a rel) : heap_predicate_stable =
  fun h -> h `contains` r

let witness (pred:heap_predicate_stable) : STATEwp unit All (fun p h -> pred h /\ (witnessed pred ==> p () h)) =
  STATEwp?.reflect (mst_witness pred)

let recall (pred:heap_predicate_stable) : STATEwp unit All (fun p h -> witnessed pred /\ (pred h ==> p () h)) =
  STATEwp?.reflect (mst_recall pred)

let alloc (#a:Type) (#rel:preorder a) (init:a) :
  ST (mref a rel) All (fun h -> True) (alloc_post init)
= STATEwp?.reflect (mst_alloc init)

let read (#a:Type) (#rel:preorder a) (r:mref a rel) :
  STATEwp a All (fun p h0 -> h0 `contains` r /\ p (sel h0 r) h0)
= STATEwp?.reflect (mst_read r)

let write (#a:Type) (#rel:preorder a) (r:mref a rel) (v:a) :
  ST unit All
    (fun h0 -> h0 `contains` r /\ rel (sel h0 r) v)
    (write_post #a #rel r v)
= STATEwp?.reflect (mst_write r v)

let op_Bang (#a:Type) (#rel:preorder a) (r:mref a rel)
  : STATEwp a All (fun p h0 -> h0 `contains` r /\ p (sel h0 r) h0)
= read #a #rel r

let op_Colon_Equals (#a:Type) (#rel:preorder a) (r:mref a rel) (v:a)
  : ST unit All
    (fun h0 -> h0 `contains` r /\ rel (sel h0 r) v)
    (write_post r v)
= write #a #rel r v

let get_heap () : ST (erased heap) All (fun h0 -> True) (fun h0 r h1 -> h0 == h1 /\ reveal r == h0) =
  STATEwp?.reflect (mst_get_heap)

type ref (a:Type0) = mref a (FStar.Heap.trivial_preorder a)

noeq type linkedList (a: Type0) : Type0 =
| LLNil : linkedList a
| LLCons : v:a -> next:ref (linkedList a) -> linkedList a

type mref_pred =
  #a:Type0 -> #rel:preorder a -> mref a rel -> Type0

type mref_heap_pred =
  #a:Type -> #rel:_ -> mref a rel -> pred:(heap -> Type0)

type mref_heap_stable_pred =
  #a:Type -> #rel:_ -> mref a rel -> pred:(heap -> Type0){stable pred}
