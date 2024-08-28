module Bad_State_Passing

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
let st_wp_h (heap a: Type) = st_post_h heap a -> Tot (st_pre_h heap)

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

open FStar.Tactics
module W = FStar.Monotonic.Witnessed

noeq type tstate = {
  t: Type u#s;
  rel: FStar.Preorder.preorder t;
}

let stable (#state) (pred:state.t -> Type0) =
  forall h1 h2. (pred h1 /\ h1 `state.rel` h2) ==> pred h2

type m (state:tstate u#s) (a:Type u#a) : Type u#(max a s) =
  state.t -> state.t * a

(* 
  Heap has to be one universe higher than the things it stores, 
  and it seems like the monad has to be at least in the universe of the heap.
  So, can one store monadic arrows in the heap while being total? 

  This was already aknowledged in DM4Free: Forbidding recursion through the store
  *)

private noeq type heap_rec : Type u#(1+a) = {
  next_addr: pos;
  memory   : FStar.FunctionalExtensionality.restricted_t pos (fun (x:pos) 
             -> option (a:Type u#a & rel:(option (FStar.Preorder.preorder a)) & b:bool & a)) 
                      //type, preorder, mm flag, and value
  }
  
  

let m_return (state:tstate) (a:Type) (x:a) : m state a =
  fun h -> (h, x)

let m_bind
  (state:tstate u#s)
  (a:Type u#a)
  (b:Type u#b)
  (l : m state a)
  (k : a -> m state b)
  : m state b =
  fun h0 ->
    let (h1, v) = l h0 in
    k v h1

let partial_call_wp (state:Type0) (pre:pure_pre) : st_wp_h state (squash pre) = 
  fun p h0 -> pre /\ p () h0

val theta : #a:Type u#a -> #state:tstate -> m state a -> st_wp_h state.t a
let rec theta #a #state m =
  fun p h0 -> forall h1 v. h0 `state.rel` h1 /\ m h0 == (h1, v) ==> p v h1

let mst (state:tstate) (a:Type) (wp:st_wp_h state.t a)=
  mm:(m state a){theta mm ⊑ wp}

let mst_return state (a:Type) (x:a) : mst state a (st_return state.t _ x) =
  m_return state a x

let mst_bind
  (#state:tstate)
  (#a : Type u#a)
  (#b : Type u#b)
  (#wp_v : st_wp_h state.t a)
  (#wp_f: a -> st_wp_h state.t b)
  (v : mst state a wp_v)
  (f : (x:a -> mst state b (wp_f x))) :
  Tot (mst state b (st_bind_wp state.t a b wp_v wp_f)) =
  admit (); (* TODO: prove monad morphism *)
  m_bind state a b v f

let mst_subcomp
  (#state:tstate)
  (#a : Type u#a)
  (#wp1 : st_wp_h state.t a)
  (#wp2 : st_wp_h state.t a)
  (v : mst state a wp1)
  :
  Pure (mst state a wp2) (requires (wp1 ⊑ wp2)) (ensures (fun _ -> True)) =
  v

// let partial_return state (pre:pure_pre) : mst state (squash pre) (partial_call_wp state.t pre) =
//   fun h0 -> (h0, ())

let get #state () : mst state state.t (fun p h0 -> p h0 h0) =
  fun h0 -> (h0, h0)

let put #state (h1:state.t) : mst state unit (fun p h0 -> (h0 `state.rel` h1) /\ p () h1) =
  fun _ -> (h1, ())

(* CA: There is no way to have an implementation for witness and recall because FStar.Monotonic.Witnessed does not provide any way to create a `witnessed`. *)
assume val witness #state (pred:state.t -> Type0) : mst state unit (fun p h -> pred h /\ stable pred /\ (W.witnessed state.rel pred ==> p () h))
assume val recall #state (pred:state.t -> Type0) : mst state unit (fun p h -> W.witnessed state.rel pred /\ (pred h ==> p () h)) 

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

let test () : mst nat_state int (fun p h0 -> forall r h1. p r h1) =
  (get ())
  `mst_bind`
  (fun h0 -> 
    (put (h0 + 1))
    `mst_bind`
    (fun () -> 
      mst_return nat_state unit () // I don't even need the witness? witness (fun s -> s > 0)
      `mst_bind`
      (fun () ->
        (fun hi -> (** here I directly use the state monad *)
          let (_, r) = f () 0 in (** BROKEN!!!! I can call f with state 0.
               ^ we cannot return this state because it is not greater than h0 *)
          (hi, r)) <: mst nat_state int (fun p h -> (forall r. p r h)))))