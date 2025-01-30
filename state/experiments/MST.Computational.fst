module MST.Computational


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
  rel: FStar.Preorder.preorder t;
}

noeq
type free (state:tstate u#s) (a:Type u#a) : Type u#(max 1 a s) =
| Get : cont:(state.t -> free state a) -> free state a
| Put : state.t -> cont:(unit -> free state a) -> free state a
| Witness : p:(state.t -> Type0) -> cont:(unit -> free state a) -> free state a
| Recall : p:(state.t -> Type0) -> cont:(unit -> free state a) -> free state a

| PartialCall : (pre:pure_pre) -> cont:(unit -> free state a) -> free state a
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
let partial_call_wp (#state:tstate) (pre:pure_pre) : st_mwp_h state.t (squash pre) = 
  let wp' : st_wp_h state.t (squash pre) = fun p h0 -> pre /\ p () h0 in
  assert (st_wp_monotonic state.t wp');
  wp'

unfold
let get_wp (#state:tstate) : st_mwp_h state.t state.t =
  fun p h0 -> p h0 h0

unfold
let put_wp (#state:tstate) (h1:state.t) : st_mwp_h state.t unit =
  fun p h0 -> (h0 `state.rel` h1) /\ p () h1

type witnessed_typ = 
  #state:Type -> rel:FStar.Preorder.preorder state -> p:(state -> Type0) -> Type0

unfold
let witness_wp (#state:tstate) (witnessed:witnessed_typ) (pred:state.t -> Type0) : st_mwp_h state.t unit =
  fun p h -> pred h /\ FStar.Preorder.stable pred state.rel /\ (witnessed state.rel pred ==> p () h)

unfold
let recall_wp (#state:tstate) (witnessed:witnessed_typ) (pred:state.t -> Type0) : st_mwp_h state.t unit =
  fun p h -> witnessed state.rel pred /\ (pred h ==> p () h)

val theta : #a:Type u#a -> #state:tstate u#s -> witnessed:witnessed_typ u#s -> free state a -> st_mwp_h state.t a
let rec theta #a #state witnessed m =
  match m with
  | Return x -> st_return state.t _ x
  | PartialCall pre k ->
      st_bind_wp state.t _ _ (partial_call_wp pre) (fun r -> theta witnessed (k r))
  | Get k ->
      st_bind_wp state.t state.t a get_wp (fun r -> theta witnessed (k r))
  | Put h1 k ->
      st_bind_wp state.t _ _ (put_wp h1) (fun r -> theta witnessed (k r))
  | Witness pred k ->
      st_bind_wp state.t _ _ (witness_wp witnessed pred) (fun r -> theta witnessed (k r))
  | Recall pred k ->
      st_bind_wp state.t _ _ (recall_wp witnessed pred) (fun r -> theta witnessed (k r))

val interp : #a:Type u#a -> #state:tstate u#s -> free state a -> (state.t -> a * state.t)
let rec interp #a #state m =
  match m with
  | Return x -> (fun s0 -> (x, s0))
  | PartialCall pre k -> (fun s0 -> interp (k ()) s0)
  | Get k -> (fun s0 -> interp (k s0) s0)
  | Put s1 k -> (fun s0 -> interp (k ()) s1)
  | Witness pred k -> (fun s0 -> interp (k ()) s0)
  | Recall pred k -> (fun s0 -> interp (k ()) s0)

//let impl_witnessed : witnessed_typ = fun rel p -> exists h0. p h0 /\ (forall h1. h0 `rel` h1 ==> p h1)
//let impl_witnessed : witnessed_typ = fun rel p -> forall h0. p h0 /\ (forall h1. h0 `rel` h1 ==> p h1)
let impl_witnessed : witnessed_typ = fun rel p -> 
  (forall h0 h1. p h0 /\ h0 `rel` h1 ==> p h1) /\
  (exists h0. p h0)

let rec my_lemma #a #state (m:free state a) wp :
  Lemma (requires (theta impl_witnessed m ⊑ wp))
        (ensures (forall p s0. wp p s0 ==> (let (r, s1) = interp m s0 in p r s1))) = 
  match m with
  | Return x -> ()
  | Witness pred k -> begin
    my_lemma (k ()) (theta impl_witnessed (k ()));
    assert (theta impl_witnessed (k ()) ⊑ st_bind_wp state.t unit a (witness_wp impl_witnessed pred) (fun r -> theta impl_witnessed (k ()))) by (
      norm [delta_only [`%st_bind_wp;`%witness_wp;`%impl_witnessed];iota];
      explode ();
      let s0 = nth_binder (2) in
      let x = nth_binder (-1) in
      let (x1, x2) = destruct_and x in
      mapply x2;
      split ();
      tadmit ()
    )
  end
  | Recall pred k -> begin
    my_lemma (k ()) (theta impl_witnessed (k ()));
    assert (theta impl_witnessed (k ()) ⊑ st_bind_wp state.t unit a (recall_wp impl_witnessed pred) (fun r -> theta impl_witnessed (k ()))) by (
      norm [delta_only [`%st_bind_wp;`%recall_wp;`%impl_witnessed];iota];
      explode ();
     (** let s0 = nth_binder (-2) in
      let p = nth_binder (-3) in
      let lemH = nth_binder (-1) in
      let (exsH, s0pH) =  destruct_and lemH in
      clear lemH;
  // mapply s0pH;
      let (preH, smth) = destruct_and (nth_binder 5) in
      clear smth;
      let preH' = instantiate preH p in clear preH;
      let preH'' = instantiate preH' s0 in clear preH'; let preH = preH'' in**)
   //   binder_retype preH; rewrite (nth_binder 12); norm [delta_only [`%theta]; zeta; iota]; trefl ();
      dump "H"
    )
  end
(**  | Get k -> 
    introduce forall p s0. wp p s0 ==> (let (r, s1) = interp (k s0) s0 in p r s1) with begin
      my_lemma (k s0) (theta impl_witnessed (k s0))
    end;
    admit ();
    assert (forall p s0. wp p s0 ==> (let (r, s1) = interp (k s0) s0 in p r s1));
    assert (forall p s0. wp p s0 ==> (let (r, s1) = interp (Get k) s0 in p r s1)) **)
  | _ -> admit ()

let lemma_theta_is_monad_morphism_ret (#state:tstate) (witnessed:witnessed_typ) (v:'a) :
  Lemma (theta witnessed (free_return state 'a v) == st_return state.t 'a v) by (compute ()) = ()

#push-options "--split_queries always"
let rec lemma_theta_is_lax_morphism_bind
  (#a:Type u#a) (#b:Type u#b) (#state:tstate u#s) (witnessed:witnessed_typ) (m:free state a) (f:a -> free state b) :
  Lemma
    (theta witnessed (free_bind m f) ⊑ st_bind_wp state.t a b (theta witnessed m) (fun x -> theta witnessed (f x))) = 
  match m with
  | Return x -> ()
  | Get k -> begin
    calc (⊑) {
      theta witnessed (free_bind (Get k) f);
      ⊑ {}
      st_bind_wp state.t state.t b get_wp (fun (h:state.t) -> theta witnessed (free_bind (k h) f));
      ⊑ { 
          let lhs = fun r -> theta witnessed (free_bind (k r) f) in
          let rhs = fun r -> st_bind_wp state.t a b (theta witnessed (k r)) (fun x -> theta witnessed (f x)) in
          introduce forall r. lhs r ⊑ rhs r with begin
            lemma_theta_is_lax_morphism_bind #a #b #state witnessed (k r) f
          end
          }
      st_bind_wp state.t state.t b get_wp (fun (h:state.t) -> st_bind_wp state.t a b (theta witnessed (k h)) (fun x -> theta witnessed (f x)));
      ⊑ {}
      st_bind_wp state.t a b (theta witnessed (Get k)) (fun x -> theta witnessed (f x));
    }
  end
  | Put h1 k -> begin
    calc (⊑) {
      theta witnessed (free_bind (Put h1 k) f);
      ⊑ {}
      st_bind_wp state.t unit b (put_wp h1) (fun r -> theta witnessed (free_bind (k r) f));
      ⊑ { 
          let lhs = fun r -> theta witnessed (free_bind (k r) f) in
          let rhs = fun r -> st_bind_wp state.t a b (theta witnessed (k r)) (fun x -> theta witnessed (f x)) in
          introduce forall r. lhs r ⊑ rhs r with begin
            lemma_theta_is_lax_morphism_bind #a #b #state witnessed (k r) f
          end
          }
      st_bind_wp state.t unit b (put_wp h1) (fun r -> st_bind_wp state.t a b (theta witnessed (k r)) (fun x -> theta witnessed (f x)));
      ⊑ {}
      st_bind_wp state.t a b (theta witnessed (Put h1 k)) (fun x -> theta witnessed (f x));
    }
  end
  | Witness pred k -> begin
    calc (⊑) {
      theta witnessed (free_bind (Witness pred k) f);
      ⊑ {}
      st_bind_wp state.t unit b (witness_wp witnessed pred) (fun r -> theta witnessed (free_bind (k r) f));
      ⊑ { 
          let lhs = fun r -> theta witnessed (free_bind (k r) f) in
          let rhs = fun r -> st_bind_wp state.t a b (theta witnessed (k r)) (fun x -> theta witnessed (f x)) in
          introduce forall r. lhs r ⊑ rhs r with begin
            lemma_theta_is_lax_morphism_bind #a #b #state witnessed (k r) f
          end
          }
      st_bind_wp state.t unit b (witness_wp witnessed pred) (fun r -> st_bind_wp state.t a b (theta witnessed (k r)) (fun x -> theta witnessed (f x)));
      ⊑ {}
      st_bind_wp state.t a b (theta witnessed (Witness pred k)) (fun x -> theta witnessed (f x));
    }
  end  
  | Recall pred k -> begin
    calc (⊑) {
      theta witnessed (free_bind (Recall pred k) f);
      ⊑ {}
      st_bind_wp state.t unit b (recall_wp witnessed pred) (fun r -> theta witnessed (free_bind (k r) f));
      ⊑ { 
          let lhs = fun r -> theta witnessed (free_bind (k r) f) in
          let rhs = fun r -> st_bind_wp state.t a b (theta witnessed (k r)) (fun x -> theta witnessed (f x)) in
          introduce forall r. lhs r ⊑ rhs r with begin
            lemma_theta_is_lax_morphism_bind #a #b #state witnessed (k r) f
          end
          }
      st_bind_wp state.t unit b (recall_wp witnessed pred) (fun r -> st_bind_wp state.t a b (theta witnessed (k r)) (fun x -> theta witnessed (f x)));
      ⊑ {}
      st_bind_wp state.t a b (theta witnessed (Recall pred k)) (fun x -> theta witnessed (f x));
    }
  end  
  | PartialCall pre k -> begin
    calc (⊑) {
      theta witnessed (free_bind (PartialCall pre k) f);
      ⊑ {}
      st_bind_wp state.t (squash pre) b (partial_call_wp pre) (fun r -> theta witnessed (free_bind (k r) f));
      ⊑ { 
          let lhs = fun r -> theta witnessed (free_bind (k r) f) in
          let rhs = fun r -> st_bind_wp state.t a b (theta witnessed (k r)) (fun x -> theta witnessed (f x)) in
          introduce forall (r:squash pre). lhs r ⊑ rhs r with begin
            lemma_theta_is_lax_morphism_bind #a #b #state witnessed (k r) f
          end
          }
      st_bind_wp state.t (squash pre) b (partial_call_wp pre) (fun r -> st_bind_wp state.t a b (theta witnessed (k r)) (fun x -> theta witnessed (f x)));
      ⊑ {}
      st_bind_wp state.t a b (theta witnessed (PartialCall pre k)) (fun x -> theta witnessed (f x));
    }
  end
#pop-options
(** ** END Section 3: theta witnessed **)

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
