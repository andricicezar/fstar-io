module MST


open FStar.Tactics
module W = FStar.Monotonic.Witnessed

(**
  File structured as follows:
  1. Spec monad
  2. Free monad
  3. Define theta and proofs that is a lax morphism
  4. Define Dijkstra Monad
**)

(** ** START Section 1: specification monad **)

(** Preconditions are predicates on the [heap] *)
let st_pre_h (heap: Type) = heap -> GTot Type0

(** Postconditions relate [a]-typed results to the final [heap], here
    refined by some pure proposition [pre], typically instantiated to
    the precondition applied to the initial [heap] *)
let st_post_h' (heap a pre: Type) = a -> _: heap{pre} -> GTot Type0

(** Postconditions without refinements *)
let st_post_h (heap a: Type) = st_post_h' heap a True

unfold
let st_post_ord (#heap:Type) (p1 p2:st_post_h heap 'a) =
  forall r h. p1 r h ==> p2 r h

(** The type of the main WP-transformer for stateful computations *)
let st_wp_h0 (heap a: Type) = st_post_h heap a -> Tot (st_pre_h heap)

unfold
let st_wp_monotonic (heap:Type) (wp:st_wp_h0 heap 'a) =
  forall p1 p2. (p1 `st_post_ord` p2) ==> (forall h. wp p1 h ==> wp p2 h)

(** !!! This is the only difference to the monad used by F* state, the fact that
  here st_wp_h has to be monotonic *)
let st_wp_h (heap a: Type) = wp:(st_wp_h0 heap a){st_wp_monotonic heap wp}

(** Returning a value does not transform the state *)
unfold
let st_return (heap:Type u#b) (a: Type u#a) (x: a) (p: st_post_h heap a) = p x

(** Sequential composition of stateful WPs *)
unfold
let st_bind_wp
      (heap: Type u#c)
      (a:Type u#a)
      (b: Type u#b)
      (wp1: st_wp_h heap a)
      (wp2: (a -> GTot (st_wp_h heap b)))
      (p: st_post_h heap b)
      (h0: heap)
     = wp1 (fun a h1 -> wp2 a p h1) h0

(** Branching for stateful WPs *)
unfold
let st_if_then_else
      (heap a p: Type)
      (wp_then wp_else: st_wp_h heap a)
      (post: st_post_h heap a)
      (h0: heap)
     = wp_then post h0 /\ (~p ==> wp_else post h0)

(** As with [PURE] the [wp] combinator names the postcondition as
    [k] to avoid duplicating it. *)
unfold
let st_ite_wp (heap a: Type) (wp: st_wp_h heap a) (post: st_post_h heap a) (h0: heap) =
  forall (k: st_post_h heap a).
    (forall (x: a) (h: heap). {:pattern (guard_free (k x h))} post x h ==> k x h) ==> wp k h0

(** Subsumption for stateful WPs *)
unfold
let st_stronger (heap a: Type) (wp1 wp2: st_wp_h heap a) =
  (forall (p: st_post_h heap a) (h: heap). wp1 p h ==> wp2 p h)

unfold
let (⊑) #heap #a wp1 wp2 = st_stronger heap a wp2 wp1

(** Closing the scope of a binder within a stateful WP *)
unfold
let st_close_wp (heap a b: Type) (wp: (b -> GTot (st_wp_h heap a))) (p: st_post_h heap a) (h: heap) =
  (forall (b: b). wp b p h)

(** Applying a stateful WP to a trivial postcondition *)
unfold
let st_trivial (heap a: Type) (wp: st_wp_h heap a) = (forall h0. wp (fun r h1 -> True) h0)
(** ** END Section 1: specification monad **)



(** ** START Section 2: free monad **)
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
  (#state:tstate u#s)
  (#a:Type u#a)
  (#b:Type u#b)
  (l : free state a)
  (k : a -> free state b) :
  free state b =
  match l with
  | Return x -> k x
  | Get cont -> Get (fun x -> free_bind (cont x) k)
  | Put h cont -> Put h (fun _ -> free_bind (cont ()) k)
  | Witness pred cont -> Witness pred (fun _ -> free_bind (cont ()) k)
  | Recall pred cont -> Recall pred (fun _ -> free_bind (cont ()) k)
  | PartialCall pre fnc ->
      PartialCall pre (fun _ ->
        free_bind (fnc ()) k)
(** ** END Section 2: free monad **)

(** ** START Section 3: theta **)
let partial_call_wp (state:tstate) (pre:pure_pre) : st_wp_h state.t (squash pre) = 
  let wp' : st_wp_h0 state.t (squash pre) = fun p h0 -> pre /\ p () h0 in
  assert (st_wp_monotonic state.t wp');
  wp'

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

let lemma_theta_is_monad_morphism_ret (#state:tstate) (v:'a) :
  Lemma (theta (free_return state 'a v) == st_return state.t 'a v) by (compute ()) = ()

open FStar.Calc

let rec lemma_theta_is_lax_morphism_bind
  (#a:Type u#a) (#b:Type u#b) (#state:tstate u#s) (m:free state a) (f:a -> free state b) :
  Lemma
    (theta (free_bind m f) ⊑ st_bind_wp state.t a b (theta m) (fun x -> theta (f x))) = 
  match m with
  | Return x -> ()
  | Get k -> begin
    calc (⊑) {
      theta (free_bind (Get k) f);
      ⊑ {}
      st_bind_wp state.t state.t b (fun p h -> p h h) (fun r -> theta (free_bind (k r) f));
      ⊑ { 
          let lhs = fun r -> theta (free_bind (k r) f) in
          let rhs = fun r -> st_bind_wp state.t a b (theta (k r)) (fun x -> theta (f x)) in
          introduce forall r. lhs r ⊑ rhs r with begin
            lemma_theta_is_lax_morphism_bind #a #b #state (k r) f
          end
          }
      st_bind_wp state.t state.t b (fun p h -> p h h) (fun r -> st_bind_wp state.t a b (theta (k r)) (fun x -> theta (f x)));
      ⊑ {}
      st_bind_wp state.t a b (theta (Get k)) (fun x -> theta (f x));
    }
  end
  | Put h1 k -> begin
    calc (⊑) {
      theta (free_bind (Put h1 k) f);
      ⊑ {}
      st_bind_wp state.t unit b (fun p h0 -> h0 `state.rel` h1 /\ p () h1) (fun r -> theta (free_bind (k r) f));
      ⊑ { 
          let lhs = fun r -> theta (free_bind (k r) f) in
          let rhs = fun r -> st_bind_wp state.t a b (theta (k r)) (fun x -> theta (f x)) in
          introduce forall r. lhs r ⊑ rhs r with begin
            lemma_theta_is_lax_morphism_bind #a #b #state (k r) f
          end
          }
      st_bind_wp state.t unit b (fun p h0 -> h0 `state.rel` h1 /\ p () h1) (fun r -> st_bind_wp state.t a b (theta (k r)) (fun x -> theta (f x)));
      ⊑ {}
      st_bind_wp state.t a b (theta (Put h1 k)) (fun x -> theta (f x));
    }
  end
  | Witness pred k -> begin
    calc (⊑) {
      theta (free_bind (Witness pred k) f);
      ⊑ {}
      st_bind_wp state.t unit b (fun p h -> pred h /\ stable pred /\ (W.witnessed state.rel pred ==> p () h)) (fun r -> theta (free_bind (k r) f));
      ⊑ { 
          let lhs = fun r -> theta (free_bind (k r) f) in
          let rhs = fun r -> st_bind_wp state.t a b (theta (k r)) (fun x -> theta (f x)) in
          introduce forall r. lhs r ⊑ rhs r with begin
            lemma_theta_is_lax_morphism_bind #a #b #state (k r) f
          end
          }
      st_bind_wp state.t unit b (fun p h -> pred h /\ stable pred /\ (W.witnessed state.rel pred ==> p () h)) (fun r -> st_bind_wp state.t a b (theta (k r)) (fun x -> theta (f x)));
      ⊑ {}
      st_bind_wp state.t a b (theta (Witness pred k)) (fun x -> theta (f x));
    }
  end  
  | Recall pred k -> begin
    calc (⊑) {
      theta (free_bind (Recall pred k) f);
      ⊑ {}
      st_bind_wp state.t unit b (fun p h -> W.witnessed state.rel pred /\ (pred h ==> p () h)) (fun r -> theta (free_bind (k r) f));
      ⊑ { 
          let lhs = fun r -> theta (free_bind (k r) f) in
          let rhs = fun r -> st_bind_wp state.t a b (theta (k r)) (fun x -> theta (f x)) in
          introduce forall r. lhs r ⊑ rhs r with begin
            lemma_theta_is_lax_morphism_bind #a #b #state (k r) f
          end
          }
      st_bind_wp state.t unit b (fun p h -> W.witnessed state.rel pred /\ (pred h ==> p () h)) (fun r -> st_bind_wp state.t a b (theta (k r)) (fun x -> theta (f x)));
      ⊑ {}
      st_bind_wp state.t a b (theta (Recall pred k)) (fun x -> theta (f x));
    }
  end  
  | PartialCall pre k -> begin
    calc (⊑) {
      theta (free_bind (PartialCall pre k) f);
      ⊑ {}
      theta (PartialCall pre (fun r -> free_bind (k r) f));
      ⊑ {}
      st_bind_wp state.t (squash pre) b (partial_call_wp state pre) (fun r -> theta (free_bind (k r) f));
      ⊑ { 
          let lhs = fun r -> theta (free_bind (k r) f) in
          let rhs = fun r -> st_bind_wp state.t a b (theta (k r)) (fun x -> theta (f x)) in
          introduce forall (r:squash pre). lhs r ⊑ rhs r with begin
            lemma_theta_is_lax_morphism_bind #a #b #state (k r) f
          end
          }
      st_bind_wp state.t (squash pre) b (partial_call_wp state pre) (fun r -> st_bind_wp state.t a b (theta (k r)) (fun x -> theta (f x)));
      ⊑ {}
      st_bind_wp state.t a b (st_bind_wp state.t (squash pre) a (partial_call_wp state pre) (fun r -> theta (k r))) (fun x -> theta (f x));
      ⊑ {}
      st_bind_wp state.t a b (theta (PartialCall pre k)) (fun x -> theta (f x));
    }
  end
(** ** END Section 3: theta **)

(** ** START Section 4: Dijkstra Monad **)
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
  lemma_theta_is_lax_morphism_bind v f;
  free_bind v f
  
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

(* We can build non-monotonic syntax, but it won't be in mst effect *)
let test_not_in_mst () : free nat_state int =
  (get ())
  `free_bind`
  (fun h0 -> 
    (put (h0 + 1))
    `free_bind`
    (fun () -> 
      witness (fun s -> s > 0)
      `free_bind`
      (fun () -> 
        (Put 0 (fun _ -> f ())))))

[@expect_failure]
let test_not_in_mst' () : mst nat_state int (fun p h0 -> forall r h1. p r h1) =
  test_not_in_mst ()


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
  FStar.Monotonic.Pure.elim_pure_wp_monotonicity_forall ();
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

val landins_knot_fs' : unit -> Dv (_mst nat (fun p _ -> forall r h1. p r h1))
let landins_knot_fs' () = 
  reify (landins_knot_fs ())