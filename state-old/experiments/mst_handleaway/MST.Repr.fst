module MST.Repr


open FStar.Tactics
open FStar.Calc

module W = FStar.Monotonic.Witnessed

(**
  File structured as follows:
  1. Spec monad
  2. Free monad
  3. Define theta and proofs that is a lax morphism
  4. Define Dijkstra Monad
**)

(** ** START Section 1: specification monad **)

(** Most of it defined in FStar.Pervasives, here just adding monotonicity *)
unfold
let st_post_ord (#heap:Type) (p1 p2:st_post_h heap 'a) =
  forall r h. p1 r h ==> p2 r h

unfold
let st_wp_monotonic (heap:Type) (wp:st_wp_h heap 'a) =
  forall p1 p2. (p1 `st_post_ord` p2) ==> (forall h. wp p1 h ==> wp p2 h)

let st_mwp_h (heap a: Type) = wp:(st_wp_h heap a){st_wp_monotonic heap wp}

unfold
let (⊑) #heap #a wp1 wp2 = st_stronger heap a wp2 wp1
(** ** END Section 1: specification monad **)



(** ** START Section 2: free monad **)
noeq type tstate = {
  t: Type u#a;
  ref : Type0 -> Type0;

  rel: FStar.Preorder.preorder t;

  contains : #a:Type0 -> t -> ref a -> Type0;

  alloc : #a:Type0 -> h0:t -> a ->
    Pure (ref a * t) 
      (requires True)
      (ensures fun rh1 -> 
        ~(h0 `contains` (fst rh1)) /\ (snd rh1) `contains` (fst rh1) /\
        (forall b (r':ref b). h0 `contains` r' ==> (snd rh1) `contains` r'));
  select : #a:Type0 -> h0:t -> r:ref a -> 
    Pure a 
      (requires h0 `contains` r) 
      (ensures fun _ -> True);
  update : #a:Type0 -> h0:t -> r:ref a -> v:a -> 
    Pure t 
      (requires h0 `contains` r)
      (ensures fun h1 -> 
        h0 `rel` h1 /\ (** enforcing monotonicity. is this enough? **)
        (forall b (r':ref b). h0 `contains` r' ==> h1 `contains` r') /\
        h1 `contains` r /\ select h1 r == v);
}

noeq
type free (state:tstate u#s) (a:Type u#a) : Type u#(max 1 a s) =
| Alloc : #b:Type0 -> b -> (state.ref b -> free state a) -> free state a
| Read : #b:Type0 -> state.ref b -> (b -> free state a) -> free state a
| Write : #b:Type0 -> state.ref b -> b -> (unit -> free state a) -> free state a
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
  | Read r cont -> Read r (fun v -> free_bind (cont v) k)
  | Write r v cont -> Write r v (fun _ -> free_bind (cont ()) k)
  | Alloc v cont -> Alloc v (fun r -> free_bind (cont r) k)
  | Witness pred cont -> Witness pred (fun _ -> free_bind (cont ()) k)
  | Recall pred cont -> Recall pred (fun _ -> free_bind (cont ()) k)
  | PartialCall pre fnc ->
      PartialCall pre (fun _ ->
        free_bind (fnc ()) k)
(** ** END Section 2: free monad **)

(** ** START Section 3: theta **)
unfold
let partial_call_wp (#state:tstate) (pre:pure_pre) : st_mwp_h state.t (squash pre) = 
  let wp' : st_wp_h state.t (squash pre) = fun p h0 -> pre /\ p () h0 in
  assert (st_wp_monotonic state.t wp');
  wp'

unfold
let alloc_wp (#state:tstate) #a (v:a) : st_mwp_h state.t (state.ref a) =
  fun p h0 -> let (r, h1) = state.alloc h0 v in p r h1

unfold
let read_wp (#state:tstate) #a (r:state.ref a) : st_mwp_h state.t a =
  fun p h0 -> h0 `state.contains` r /\ p (state.select h0 r) h0

unfold
let write_wp (#state:tstate) #a (r:state.ref a) (v:a) : st_mwp_h state.t unit =
  fun p h0 -> h0 `state.contains` r /\ p () (state.update h0 r v)

unfold
let witness_wp (#state:tstate) (pred:state.t -> Type0) : st_mwp_h state.t unit =
  fun p h -> pred h /\ FStar.Preorder.stable pred state.rel /\ (W.witnessed state.rel pred ==> p () h)

unfold
let recall_wp (#state:tstate) (pred:state.t -> Type0) : st_mwp_h state.t unit =
  fun p h -> W.witnessed state.rel pred /\ (pred h ==> p () h)

val theta : #a:Type u#a -> #state:tstate u#s -> free state a -> st_mwp_h state.t a
let rec theta #a #state m =
  match m with
  | Return x -> st_return state.t _ x
  | PartialCall pre k ->
      st_bind_wp state.t _ _ (partial_call_wp pre) (fun r -> theta (k r))
  | Alloc v k ->
      st_bind_wp state.t _ a (alloc_wp v) (fun r -> theta (k r))
  | Read r k ->
      st_bind_wp state.t _ a (read_wp r) (fun v -> theta (k v))
  | Write r v k ->
      st_bind_wp state.t _ _ (write_wp r v) (fun _ -> theta (k ()))
  | Witness pred k ->
      st_bind_wp state.t _ _ (witness_wp pred) (fun r -> theta (k r))
  | Recall pred k ->
      st_bind_wp state.t _ _ (recall_wp pred) (fun r -> theta (k r))

let lemma_theta_is_monad_morphism_ret (#state:tstate) (v:'a) :
  Lemma (theta (free_return state 'a v) == st_return state.t 'a v) by (compute ()) = ()


#push-options "--split_queries always"
let rec lemma_theta_is_lax_morphism_bind
  (#a:Type u#a) (#b:Type u#b) (#state:tstate u#s) (m:free state a) (f:a -> free state b) :
  Lemma
    (theta (free_bind m f) ⊑ st_bind_wp state.t a b (theta m) (fun x -> theta (f x))) = 
  match m with
  | Return x -> ()
  | Witness pred k -> begin
    calc (⊑) {
      theta (free_bind (Witness pred k) f);
      ⊑ {}
      st_bind_wp state.t unit b (witness_wp pred) (fun r -> theta (free_bind (k r) f));
      ⊑ { 
          let lhs = fun r -> theta (free_bind (k r) f) in
          let rhs = fun r -> st_bind_wp state.t a b (theta (k r)) (fun x -> theta (f x)) in
          introduce forall r. lhs r ⊑ rhs r with begin
            lemma_theta_is_lax_morphism_bind #a #b #state (k r) f
          end
          }
      st_bind_wp state.t unit b (witness_wp pred) (fun r -> st_bind_wp state.t a b (theta (k r)) (fun x -> theta (f x)));
      ⊑ {}
      st_bind_wp state.t a b (theta (Witness pred k)) (fun x -> theta (f x));
    }
  end  
  | Recall pred k -> begin
    calc (⊑) {
      theta (free_bind (Recall pred k) f);
      ⊑ {}
      st_bind_wp state.t unit b (recall_wp pred) (fun r -> theta (free_bind (k r) f));
      ⊑ { 
          let lhs = fun r -> theta (free_bind (k r) f) in
          let rhs = fun r -> st_bind_wp state.t a b (theta (k r)) (fun x -> theta (f x)) in
          introduce forall r. lhs r ⊑ rhs r with begin
            lemma_theta_is_lax_morphism_bind #a #b #state (k r) f
          end
          }
      st_bind_wp state.t unit b (recall_wp pred) (fun r -> st_bind_wp state.t a b (theta (k r)) (fun x -> theta (f x)));
      ⊑ {}
      st_bind_wp state.t a b (theta (Recall pred k)) (fun x -> theta (f x));
    }
  end  
  | PartialCall pre k -> begin
    calc (⊑) {
      theta (free_bind (PartialCall pre k) f);
      ⊑ {}
      st_bind_wp state.t (squash pre) b (partial_call_wp pre) (fun r -> theta (free_bind (k r) f));
      ⊑ { 
          let lhs = fun r -> theta (free_bind (k r) f) in
          let rhs = fun r -> st_bind_wp state.t a b (theta (k r)) (fun x -> theta (f x)) in
          introduce forall (r:squash pre). lhs r ⊑ rhs r with begin
            lemma_theta_is_lax_morphism_bind #a #b #state (k r) f
          end
          }
      st_bind_wp state.t (squash pre) b (partial_call_wp pre) (fun r -> st_bind_wp state.t a b (theta (k r)) (fun x -> theta (f x)));
      ⊑ {}
      st_bind_wp state.t a b (theta (PartialCall pre k)) (fun x -> theta (f x));
    }
  end
  | _ -> admit ()
#pop-options
(** ** END Section 3: theta **)

(** ** START Section 4: Dijkstra Monad **)
let mst (state:tstate) (a:Type) (wp:st_mwp_h state.t a)=
  m:(free state a){theta m ⊑ wp}

let mst_return (#state:tstate) (#a:Type) (x:a) : mst state a (st_return state.t _ x) =
  free_return state a x

let mst_bind
  (#state:tstate u#s)
  (#a : Type u#a)
  (#b : Type u#b)
  (#wp_v : st_mwp_h state.t a)
  (#wp_f: a -> st_mwp_h state.t b)
  (v : mst state a wp_v)
  (f : (x:a -> mst state b (wp_f x))) :
  Tot (mst state b (st_bind_wp state.t a b wp_v wp_f)) =
  lemma_theta_is_lax_morphism_bind v f;
  free_bind v f
  
let mst_subcomp
  (#state:tstate u#s)
  (#a : Type u#a)
  (#wp1 : st_mwp_h state.t a)
  (#wp2 : st_mwp_h state.t a)
  (v : mst state a wp1)
  :
  Pure (mst state a wp2) (requires (wp1 ⊑ wp2)) (ensures (fun _ -> True)) =
  v

let mst_require #state (pre:pure_pre) : mst state (squash pre) (partial_call_wp pre) =
  PartialCall pre (Return)

let mst_alloc #state #a (v:a) : mst state (state.ref a) (alloc_wp v) =
  Alloc v Return

let mst_read #state #a (r:state.ref a) : mst state a (read_wp r) =
  Read r Return

let mst_write #state #a (r:state.ref a) (v:a) : mst state unit (write_wp r v) =
  Write r v Return

let mst_witness #state (pred:state.t -> Type0) : mst state unit (witness_wp pred) =
  Witness pred Return

let mst_recall #state (pred:state.t -> Type0) : mst state unit (recall_wp pred) =
  Recall pred Return
(** ** END Section 4: Dijkstra Monad **)
