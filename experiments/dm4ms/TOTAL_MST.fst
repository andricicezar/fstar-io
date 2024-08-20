module TOTAL_MST

open WMonad


open FStar.Tactics
module W = FStar.Monotonic.Witnessed

noeq type tstate = {
  t: Type0;
  rel: FStar.Preorder.preorder t;
}

let stable (#state) (pred:state.t -> Type0) =
  forall h1 h2. (pred h1 /\ h1 `state.rel` h2) ==> pred h2

noeq
type free (state:tstate) (a:Type u#a) : Type u#(max 1 a) =
| Get : cont:(state.t -> free state a) -> free state a
| Put : state.t -> cont:(unit -> free state a) -> free state a
| Witness : p:(state.t -> Type0) -> cont:(unit -> free state a) -> free state a
| Recall : p:(state.t -> Type0) -> cont:(unit -> free state a) -> free state a

| PartialCall : (pre:pure_pre) -> cont:((squash pre) -> free u#a state a) -> free state a
| Return : a -> free state a

let free_return (state:tstate) (a:Type) (x:a) : free state a =
  Return x

let rec free_bind
  (state:tstate)
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

let partial_call_wp (state:Type0) (pre:pure_pre) : st_wp_h state (squash pre) = 
  fun p h0 -> pre /\ p () h0

val theta : #a:Type u#a -> #state:tstate -> free state a -> st_wp_h state.t a
let rec theta #a #state m =
  match m with
  | Return x -> st_return state.t _ x
  | PartialCall pre k ->
      st_bind_wp state.t _ _ (partial_call_wp state.t pre) (fun r -> theta (k r))
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

let mst_return state (a:Type) (x:a) : mst state a (st_return state.t _ x) =
  free_return state a x

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
  free_bind state a b v f

let mst_subcomp
  (#state:tstate)
  (#a : Type u#a)
  (#wp1 : st_wp_h state.t a)
  (#wp2 : st_wp_h state.t a)
  (v : mst state a wp1)
  :
  Pure (mst state a wp2) (requires (wp1 ⊑ wp2)) (ensures (fun _ -> True)) =
  v

let partial_return state (pre:pure_pre) : mst state (squash pre) (partial_call_wp state.t pre) =
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
        put (h0+1) // TODO: can I revert the state to h0?
        `mst_bind`
        (fun () -> f ()))))
