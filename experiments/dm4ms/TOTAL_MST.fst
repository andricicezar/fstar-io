module TOTAL_MST

open WMonad


open FStar.Tactics
module W = FStar.Monotonic.Witnessed

noeq type tstate = {
  t: Type u#a;
  rel: FStar.Preorder.preorder t;
}

let stable (#state) (pred:state.t -> Type0) =
  forall h1 h2. (pred h1 /\ h1 `state.rel` h2) ==> pred h2

noeq
type free (state:tstate u#s) (a:Type u#a) : Type u#(max 1 a s) =
| Get : cont:(state.t -> free state a) -> free state a
| Put : state.t -> cont:(unit -> free state a) -> free state a
| Witness : p:(state.t -> Type0) -> cont:(unit -> free state a) -> free state a
| Recall : p:(state.t -> Type0) -> cont:(unit -> free state a) -> free state a

| PartialCall : (pre:pure_pre) -> cont:((squash pre) -> free state a) -> free state a
| Return : a -> free state a

let free_return (state:tstate u#s) (a:Type u#b) (x:a) : free state a =
  Return x

let rec free_bind
  (state:tstate u#s)
  (a:Type u#a)
  (b:Type u#b)
  (l : free state a)
  (k : a -> free state b) :
  free state b =
  match l with
  | Return x -> k x
  | Get cont -> Get (fun x -> free_bind state a b (cont x) k)
  | Put h cont -> Put h (fun _ -> free_bind state a b (cont ()) k)
  | Witness pred cont -> Witness pred (fun _ -> free_bind state a b (cont ()) k)
  | Recall pred cont -> Recall pred (fun _ -> free_bind state a b (cont ()) k)
  | PartialCall pre fnc ->
      PartialCall pre (fun _ ->
        free_bind state a b (fnc ()) k)

let partial_call_wp (state:tstate) (pre:pure_pre) : st_wp_h state.t (squash pre) = 
  fun p h0 -> pre /\ p () h0

val theta : #a:Type u#a -> #state:tstate u#s -> free state a -> st_wp_h state.t a
let rec theta #a #state m =
  match m with
  | Return x -> st_return state.t _ x
  | PartialCall pre k ->
      st_bind_wp state.t _ _ (partial_call_wp state pre) (fun r -> theta (k r))
  | Get k ->
      st_bind_wp state.t _ _ (fun p h -> p h h) (fun r -> theta (k r))
  | Put h1 k ->
      st_bind_wp state.t _ _ (fun p h0 -> h0 `state.rel` h1 /\ p () h1) (fun r -> theta (k r))
  | Witness pred k ->
      st_bind_wp state.t _ _ (fun p h -> pred h /\ stable pred /\ (W.witnessed state.rel pred ==> p () h)) (fun r -> theta (k r))
  | Recall pred k ->
      st_bind_wp state.t _ _ (fun p h -> W.witnessed state.rel pred /\ (pred h ==> p () h)) (fun r -> theta (k r))

let mst (state:tstate) (a:Type) (wp:st_wp_h state.t a)=
  m:(free state a){theta m ⊑ wp}

let mst_return (#state:tstate) (#a:Type) (x:a) : mst state a (st_return state.t _ x) =
  free_return state a x


let mst_bind
  (#state:tstate u#s)
  (#a : Type u#a)
  (#b : Type u#b)
  (#wp_v : st_wp_h state.t a)
  (#wp_f: a -> st_wp_h state.t b)
  (v : mst state a wp_v)
  (f : (x:a -> mst state b (wp_f x))) :
  Tot (mst state b (st_bind_wp state.t a b wp_v wp_f)) =
  admit (); (* TODO: prove monad morphism *)
  free_bind state a b v f

let mst_subcomp
  (#state:tstate u#s)
  (#a : Type u#a)
  (#wp1 : st_wp_h state.t a)
  (#wp2 : st_wp_h state.t a)
  (v : mst state a wp1)
  :
  Pure (mst state a wp2) (requires (wp1 ⊑ wp2)) (ensures (fun _ -> True)) =
  v

let partial_return state (pre:pure_pre) : mst state (squash pre) (partial_call_wp state pre) =
  PartialCall pre (Return)

let get #state () : mst state state.t (fun p h0 -> p h0 h0) =
  Get Return

let put #state (h1:state.t) : mst state unit (fun p h0 -> (h0 `state.rel` h1) /\ p () h1) =
  Put h1 Return

let witness #state (pred:state.t -> Type0) : mst state unit (fun p h -> pred h /\ stable pred /\ (W.witnessed state.rel pred ==> p () h)) =
  Witness pred Return

let recall #state (pred:state.t -> Type0) : mst state unit (fun p h -> W.witnessed state.rel pred /\ (pred h ==> p () h)) =
  Recall pred Return

let nat_state = {
  t = nat;
  rel = (fun x y -> x <= y == true);
}

assume val div : #state:tstate -> x:int -> y:int -> mst state int (fun p h -> y <> 0 /\ p (x/y) h)


// put(get() + 1); witness (fun s -> s > 0); let f () = recall (fun s -> s > 0); 1 / get() in f () 0

let f () : mst nat_state int (fun p h0 -> W.witnessed nat_state.rel (fun s -> s > 0) /\ (forall r. p r h0)) =
  (get ())
  `mst_bind`
  (fun h -> 
    (recall (fun s -> s > 0))
    `mst_bind`
    (fun () ->
      (1 `div` h)))

[@@expect_failure]
let test () : mst nat_state int (fun p h0 -> forall r h1. p r h1) =
  (get ())
  `mst_bind`
  (fun h0 -> 
    (put (h0+ 1))
    `mst_bind`
    (fun () -> 
      witness (fun s -> s > 0)
      `mst_bind`
      (fun () -> 
        (Put 0 (fun _ -> f ())) <: mst nat_state int (fun p h -> //h `nat_state.rel` 0 /\ 
                                                                 W.witnessed nat_state.rel (fun s -> s > 0) /\
                                                                 (forall r h'. p r h')))))
        // (Put (h0+1) (fun _ -> f ())) <: mst nat_state int (fun p h -> h `nat_state.rel` (h0+1) /\ 
        //                                                               W.witnessed nat_state.rel (fun s -> s > 0) /\
        //                                                               (forall r h'. p r h')))))
        // put (h0+1) // TODO: can I revert the state to h0?
        // `mst_bind`
        // (fun () -> f ()))))




open FStar.Monotonic.Heap

let heap_state : tstate = { t = heap; rel = FStar.ST.heap_rel }

unfold let _stable (pred:heap_state.t -> Type0) = stable #heap_state pred

let _mst a wp = mst heap_state a wp
let _mst_bind a b wp_v wp_f v f = mst_bind #heap_state #a #b #wp_v #wp_f v f
let _mst_return a x = mst_return #heap_state #a x

let _mst_subcomp a wp1 wp2 v:
  Pure (_mst a wp2) (requires (wp1 ⊑ wp2)) (ensures (fun _ -> True)) = mst_subcomp #heap_state #a #wp1 #wp2 v

let mst_if_then_else (a : Type u#a)
  (#wp1 : st_wp_h heap_state.t a)
  (#wp2 : st_wp_h heap_state.t a)
  (f : _mst a wp1) (g : _mst a wp2) (b : bool) : Type =
  _mst a (st_if_then_else heap_state.t a b wp1 wp2)


// total
reifiable
reflectable
effect {
  STATEwp (a:Type) (wp : st_wp_h heap_state.t a)
  with {
       repr       = _mst
     ; return     = _mst_return
     ; bind       = _mst_bind
     ; subcomp    = _mst_subcomp
     ; if_then_else = mst_if_then_else
     }
}

unfold
let wp_lift_pure_st (w : pure_wp 'a) : st_wp_h heap_state.t 'a =
  fun p h -> w (fun r -> p r h)

val lift_pure_mst :
  a: Type u#a ->
  w: pure_wp a ->
  f: (eqtype_as_type unit -> PURE a w) ->
  Tot (_mst a (wp_lift_pure_st w))
let lift_pure_mst a w f =
  FStar.Monotonic.Pure.elim_pure_wp_monotonicity_forall ();
  let lhs = partial_return heap_state (as_requires w) in
  let rhs = (fun (pre:(squash (as_requires w))) -> _mst_return a (f pre)) in
  let m = _mst_bind _ _ _ _ lhs rhs in
  _mst_subcomp _ _ _ m

sub_effect PURE ~> STATEwp = lift_pure_mst

let _get () : STATEwp heap (fun p h -> p h h) = 
  STATEwp?.reflect (get ())

let _put (h1:heap) : STATEwp unit (fun p h0 -> (h0 `heap_state.rel` h1) /\ p () h1) = 
  STATEwp?.reflect (put h1)


(** *** START SECTION --- COPY PASTE FROM FStar.ST **)
type heap_predicate = heap -> Type0

[@@"opaque_to_smt"]
let witnessed (p:heap_predicate{_stable p}) : Type0 = W.witnessed heap_state.rel p

let _witness (pred:heap -> Type0) : STATEwp unit (fun p h -> pred h /\ _stable pred /\ (witnessed pred ==> p () h)) = 
  STATEwp?.reflect (witness pred)

let _recall (pred:heap_predicate{stable #heap_state pred}) : STATEwp unit (fun p h -> witnessed pred /\ (pred h ==> p () h)) = 
  STATEwp?.reflect (recall pred)

let st_pre           = st_pre_h heap
let st_post' (a:Type) (pre:Type) = st_post_h' heap a pre
let st_post  (a:Type) = st_post_h heap a
let st_wp (a:Type)   = st_wp_h heap a

effect ST (a:Type) (pre:st_pre) (post: (h:heap -> Tot (st_post' a (pre h)))) =
  STATEwp a (fun (p:st_post a) (h:heap) -> pre h /\ (forall a h1. post h a h1 ==> p a h1))
effect St (a:Type) = ST a (fun h -> True) (fun h0 r h1 -> True)


let contains_pred (#a:Type) (#rel:FStar.Preorder.preorder a) (r:mref a rel) = fun h -> h `contains` r

type mref (a:Type0) (rel:FStar.Preorder.preorder a) =
  r:Heap.mref a rel{is_mm r = false /\ witnessed (contains_pred r)}

let alloc (#a:Type) (#rel:FStar.Preorder.preorder a) (init:a)
  :ST (mref a rel)
      (fun h -> True)
      (fun h0 r h1 -> fresh r h0 h1 /\ modifies Set.empty h0 h1 /\ sel h1 r == init)
  = let h0 = _get () in
    let r, h1 = alloc rel h0 init false in
    _put h1;
    _witness (contains_pred r);
    r

let read (#a:Type) (#rel:FStar.Preorder.preorder a) (r:mref a rel) :STATEwp a (fun p h -> p (sel h r) h)
  = let h0 = _get () in
    _recall (contains_pred r);
    Heap.lemma_sel_equals_sel_tot_for_contained_refs h0 r;
    sel_tot h0 r

let write (#a:Type) (#rel:FStar.Preorder.preorder a) (r:mref a rel) (v:a)
  : ST unit
    (fun h -> rel (sel h r) v)
    (fun h0 x h1 -> rel (sel h0 r) v /\ h0 `contains` r /\
                 modifies (Set.singleton (addr_of r)) h0 h1 /\ equal_dom h0 h1 /\
                 sel h1 r == v)
  = let h0 = _get () in
    _recall (contains_pred r);
    let h1 = upd_tot h0 r v in
    Heap.lemma_distinct_addrs_distinct_preorders ();
    Heap.lemma_distinct_addrs_distinct_mm ();
    Heap.lemma_upd_equals_upd_tot_for_contained_refs h0 r v;
    _put h1

let op_Bang (#a:Type) (#rel:FStar.Preorder.preorder a) (r:mref a rel)
  : STATEwp a (fun p h -> p (sel h r) h)
= read #a #rel r

let op_Colon_Equals (#a:Type) (#rel:FStar.Preorder.preorder a) (r:mref a rel) (v:a)
  : ST unit
    (fun h -> rel (sel h r) v)
    (fun h0 x h1 -> rel (sel h0 r) v /\ h0 `contains` r /\
                 modifies (Set.singleton (addr_of r)) h0 h1 /\ equal_dom h0 h1 /\
                 sel h1 r == v)
= write #a #rel r v

type ref (a:Type0) = mref a (FStar.Heap.trivial_preorder a)
(** *** END SECTION --- COPY PASTE FROM FStar.ST **)

let landins_knot_fs () : St nat =
  let id : nat -> St nat = fun x -> x in
  let r : ref (nat -> St nat) = alloc id in (** if total, there are universe problems because of pre-conditionality and `put h`,
                                                e.g., arrows are the same universe as the heap 
                                                This is a known problem. Check DM4Free: Forbidding recursion through the store*)
  let f : nat -> St nat = (fun x -> !r x) in
  r := f;
  f 0
