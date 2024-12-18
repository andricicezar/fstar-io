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

let st_wp (heap a: Type) = wp:(st_wp_h heap a){st_wp_monotonic heap wp}

unfold
let (⊑) #heap #a wp1 wp2 = st_stronger heap a wp2 wp1
(** ** END Section 1: specification monad **)



(** ** START Section 2: free monad **)
noeq type tstate = {
  t: Type u#a;
  rel: FStar.Preorder.preorder t;
}

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
unfold
let partial_call_wp (#state:tstate) (pre:pure_pre) : st_wp state.t (squash pre) = 
  let wp' : st_wp_h state.t (squash pre) = fun p h0 -> pre /\ p () h0 in
  assert (st_wp_monotonic state.t wp');
  wp'

unfold
let get_wp (#state:tstate) : st_wp state.t state.t =
  fun p h0 -> p h0 h0

unfold
let put_wp (#state:tstate) (h1:state.t) : st_wp state.t unit =
  fun p h0 -> (h0 `state.rel` h1) /\ p () h1

unfold
let witness_wp (#state:tstate) (pred:state.t -> Type0) : st_wp state.t unit =
  fun p h -> pred h /\ FStar.Preorder.stable pred state.rel /\ (W.witnessed state.rel pred ==> p () h)

unfold
let recall_wp (#state:tstate) (pred:state.t -> Type0) : st_wp state.t unit =
  fun p h -> W.witnessed state.rel pred /\ (pred h ==> p () h)

val theta : #a:Type u#a -> #state:tstate u#s -> free state a -> st_wp state.t a
let rec theta #a #state m =
  match m with
  | Return x -> st_return state.t _ x
  | PartialCall pre k ->
      st_bind_wp state.t _ _ (partial_call_wp pre) (fun r -> theta (k r))
  | Get k ->
      st_bind_wp state.t state.t a get_wp (fun r -> theta (k r))
  | Put h1 k ->
      st_bind_wp state.t _ _ (put_wp h1) (fun r -> theta (k r))
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
  | Get k -> begin
    calc (⊑) {
      theta (free_bind (Get k) f);
      ⊑ {}
      st_bind_wp state.t state.t b get_wp (fun (h:state.t) -> theta (free_bind (k h) f));
      ⊑ { 
          let lhs = fun r -> theta (free_bind (k r) f) in
          let rhs = fun r -> st_bind_wp state.t a b (theta (k r)) (fun x -> theta (f x)) in
          introduce forall r. lhs r ⊑ rhs r with begin
            lemma_theta_is_lax_morphism_bind #a #b #state (k r) f
          end
          }
      st_bind_wp state.t state.t b get_wp (fun (h:state.t) -> st_bind_wp state.t a b (theta (k h)) (fun x -> theta (f x)));
      ⊑ {}
      st_bind_wp state.t a b (theta (Get k)) (fun x -> theta (f x));
    }
  end
  | Put h1 k -> begin
    calc (⊑) {
      theta (free_bind (Put h1 k) f);
      ⊑ {}
      st_bind_wp state.t unit b (put_wp h1) (fun r -> theta (free_bind (k r) f));
      ⊑ { 
          let lhs = fun r -> theta (free_bind (k r) f) in
          let rhs = fun r -> st_bind_wp state.t a b (theta (k r)) (fun x -> theta (f x)) in
          introduce forall r. lhs r ⊑ rhs r with begin
            lemma_theta_is_lax_morphism_bind #a #b #state (k r) f
          end
          }
      st_bind_wp state.t unit b (put_wp h1) (fun r -> st_bind_wp state.t a b (theta (k r)) (fun x -> theta (f x)));
      ⊑ {}
      st_bind_wp state.t a b (theta (Put h1 k)) (fun x -> theta (f x));
    }
  end
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
#pop-options
(** ** END Section 3: theta **)

(** ** START Section 4: Dijkstra Monad **)
let mst (state:tstate) (a:Type) (wp:st_wp state.t a)=
  m:(free state a){theta m ⊑ wp}

let mst_return (#state:tstate) (#a:Type) (x:a) : mst state a (st_return state.t _ x) =
  free_return state a x

let mst_bind
  (#state:tstate u#s)
  (#a : Type u#a)
  (#b : Type u#b)
  (#wp_v : st_wp state.t a)
  (#wp_f: a -> st_wp state.t b)
  (v : mst state a wp_v)
  (f : (x:a -> mst state b (wp_f x))) :
  Tot (mst state b (st_bind_wp state.t a b wp_v wp_f)) =
  lemma_theta_is_lax_morphism_bind v f;
  free_bind v f
  
let mst_subcomp
  (#state:tstate u#s)
  (#a : Type u#a)
  (#wp1 : st_wp state.t a)
  (#wp2 : st_wp state.t a)
  (v : mst state a wp1)
  :
  Pure (mst state a wp2) (requires (wp1 ⊑ wp2)) (ensures (fun _ -> True)) =
  v

let partial_return state (pre:pure_pre) : mst state (squash pre) (partial_call_wp pre) =
  PartialCall pre (Return)

let mst_get #state () : mst state state.t get_wp =
  Get Return

let mst_put #state (h1:state.t) : mst state unit (put_wp h1) =
  Put h1 Return

let mst_witness #state (pred:state.t -> Type0) : mst state unit (witness_wp pred) =
  Witness pred Return

let mst_recall #state (pred:state.t -> Type0) : mst state unit (recall_wp pred) =
  Recall pred Return
(** ** END Section 4: Dijkstra Monad **)

(** ** START Some test **)
let nat_state = {
  t = nat;
  rel = (fun x y -> x <= y == true);
}

assume val div : #state:tstate -> x:int -> y:int -> mst state int (fun p h -> y <> 0 /\ p (x/y) h)


// put(get() + 1); witness (fun s -> s > 0); let f () = recall (fun s -> s > 0); 1 / get() in f () 0

let f () : mst nat_state int (fun p h0 -> W.witnessed nat_state.rel (fun s -> s > 0) /\ (forall r. p r h0)) =
  (mst_get ())
  `mst_bind`
  (fun h -> 
    (mst_recall (fun s -> s > 0))
    `mst_bind`
    (fun () ->
      (1 `div` h)))

(* We can build non-monotonic syntax, but it won't be in mst effect *)
let test_not_in_mst () : free nat_state int =
  (mst_get ())
  `free_bind`
  (fun h0 -> 
    (mst_put (h0 + 1))
    `free_bind`
    (fun () -> 
      mst_witness (fun s -> s > 0)
      `free_bind`
      (fun () -> 
        (Put 0 (fun _ -> f ())))))

[@expect_failure]
let test_not_in_mst' () : mst nat_state int (fun p h0 -> forall r h1. p r h1) =
  test_not_in_mst ()