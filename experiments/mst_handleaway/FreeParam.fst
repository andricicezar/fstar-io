module FreeParam

open FStar.Tactics
open FStar.Tactics.Typeclasses

noeq
type free (ref:Type0 -> Type0) (a:Type u#a) : Type u#(max 1 a) = (* because of the references *)
| Alloc : b:Type0 -> b -> (ref b -> free ref a) -> free ref a
| Read : b:Type0 -> ref b -> (b -> free ref a) -> free ref a
| Write : b:Type0 -> ref b -> b -> (unit -> free ref a) -> free ref a
| Return : a -> free ref a

let free_return #ref (x:'a) : free ref 'a = Return x

let rec free_bind #ref (m:free ref 'a) (k:'a -> free ref 'b) : free ref 'b =
  match m with
  | Return x -> k x
  | Alloc b x cont -> Alloc b x (fun x -> free_bind (cont x) k)
  | Read b r cont -> Read b r (fun x -> free_bind (cont x) k)
  | Write b r v cont -> Write b r v (fun x -> free_bind (cont x) k)

noeq
type heap_t (ref:Type0 -> Type0) = {
  t:Type0;

  contains : #a:Type0 -> t -> ref a -> Type0;

  alloc : #a:Type0 -> h0:t -> a -> Pure (ref a * t) True (fun rh1 -> 
    ~(h0 `contains` (fst rh1)) /\ (snd rh1) `contains` (fst rh1) /\
    (forall b (r':ref b). h0 `contains` r' ==> (snd rh1) `contains` r'));
  select : #a:Type0 -> h0:t -> r:ref a -> Pure a (h0 `contains` r) (fun _ -> True);
  update : #a:Type0 -> h0:t -> r:ref a -> v:a -> Pure t (h0 `contains` r) (fun h1 -> 
    (forall b (r':ref b). h0 `contains` r' ==> h1 `contains` r') /\
    h1 `contains` r /\ select h1 r == v);
}

let rec theta 
  (ref:Type0 -> Type0)
  (heap:heap_t ref)
  (m:free ref 'a) : st_wp_h heap.t 'a =
  match m with
  | Return x -> st_return heap.t _ x
  | Alloc b x k ->
      st_bind_wp heap.t (ref b) 'a (fun p h0 -> let rh1 = heap.alloc h0 x in p (fst rh1) (snd rh1)) (fun r -> theta ref heap (k r))
  | Read b r k ->
      st_bind_wp heap.t b 'a (fun p h0 -> h0 `heap.contains` r /\ p (heap.select h0 r) h0) (fun r -> theta ref heap (k r))
  | Write b r v k ->
      st_bind_wp heap.t unit 'a (fun p h0 -> h0 `heap.contains` r /\ p () (heap.update h0 r v)) (fun r -> theta ref heap (k r))

unfold
let (⊑) #heap #a wp1 wp2 = st_stronger heap a wp2 wp1

type dm (ref:Type0 -> Type0) (heap:heap_t ref) (a:Type) (wp:st_wp_h heap.t a) =
  m:(free ref a){theta ref heap m ⊑ wp}

let dm_return #ref #heap #a (x:a) : dm ref heap a (st_return heap.t a x) = Return x
let dm_bind #ref #heap #a #b #wpm #wpk (m:dm ref heap a wpm) (k:(x:a -> dm ref heap b (wpk x))) : dm ref heap b (st_bind_wp _ _ _ wpm wpk) = 
  let m' = free_bind m k in
  assume (theta ref heap m' ⊑ st_bind_wp heap.t a b wpm wpk);
  m'

let dm_subcomp #ref #heap #a #wpm #wpk (m:dm ref heap a wpm) : Pure (dm ref heap a wpk) (requires (wpm ⊑ wpk)) (ensures (fun _ -> True)) =
  m


let unit_test_return ref heap : dm ref heap int (fun p h0 -> p 1 h0) = Return 1
let unit_test_alloc ref heap : dm ref heap (ref int) (fun p _ -> forall r h1. p r h1) = Alloc int 5 Return

unfold
let st_post_ord (#heap:Type) (p1 p2:st_post_h heap 'a) =
  forall r h. p1 r h ==> p2 r h

unfold
let st_wp_monotonic (heap:Type) (wp:st_wp_h heap 'a) =
  forall p1 p2. (p1 `st_post_ord` p2) ==> (forall h. wp p1 h ==> wp p2 h)

module M = MST

type icontext (ref:Type0 -> Type0) =
  #b:Type0 -> ref b -> Type0

val icontext_empty : ref:(Type0 -> Type0) -> icontext ref
let icontext_empty ref r = False

let extend_icontext #ref (ig:icontext ref) #b (r:ref b) : icontext ref =
  fun #b' r' -> (b == b' /\ r == r' ==> True) /\ (b =!= b' \/ r =!= r' ==> ig r')

let rec closed_free #ref #a (ig:icontext ref) (m:free ref a) : Type0 =
  match m with
  | Return x -> True
  | Alloc b v k -> forall r. closed_free (extend_icontext ig #b r) (k r)
  | Read b r k -> ig r /\ (forall r. closed_free ig (k r))
  | Write b r v k -> ig r /\ (closed_free ig (k ()))

type cfree ref a = m:(free ref a){closed_free (icontext_empty ref) m}

let test1 #ref : cfree ref unit = Return ()
let test2 #ref : cfree ref (ref int) = Alloc int 5 Return
let test3 #ref : cfree ref unit = 
  Alloc int 5 (fun r -> 
    Read int r (fun x -> 
      Write int r (x + 1) Return))

[@expect_failure]
let test4 (#ref:Type0 -> Type0) (r:ref int) : cfree ref unit = 
  Read int r (fun x -> 
    Write int r (x + 1) Return)

let test4' (#ref:Type0 -> Type0) (r:ref int) : m:(free ref unit){closed_free (extend_icontext (icontext_empty ref) r) m} = 
  Read int r (fun x -> 
    Write int r (x + 1) Return)

[@expect_failure]
let test5 (#ref:Type0 -> Type0) (f:unit -> cfree ref (ref int)) : cfree ref unit = 
  free_bind (f ()) (fun r -> 
    Read int r (fun x -> 
      Write int r (x + 1) Return))

let closed_alloc_cont #ref #a (ig:icontext ref) (b:Type0) (v:b) (k:ref b -> free ref a) (r:ref b) :
  Lemma
    (requires (closed_free ig (Alloc b v k)))
    (ensures (closed_free (extend_icontext ig #b r) (k r))) = ()

let trivial_wp #ref (heap:heap_t ref) a : st_wp_h heap.t a = fun p _ -> forall r h1. p r h1

let fixed_wp #ref (ig:icontext ref) (heap:heap_t ref) a : st_wp_h heap.t a =
  fun p h0 -> 
    (forall b (r:ref b). ig r ==> h0 `heap.contains` r) /\ (** pre-cond **)
    (forall res h1. p res h1) (** post-cond **)

val lift_to_dm #ref #heap #a ig (m:free ref a) (#_:squash (closed_free ig m)) : dm ref heap a (fixed_wp ig heap a)
let rec lift_to_dm #ref #heap #a ig m #sq =
  match m with
  | Return x -> Return x
  | Alloc b v k -> 
    let k' (r:ref b) : dm ref heap a (fixed_wp (extend_icontext ig r) heap a) = 
      lift_to_dm #ref #heap #a (extend_icontext ig r) (k r) in 
    let m' = Alloc b v k' in
    // assume (closed_free ig m');
    assume (theta ref heap m' ⊑ fixed_wp ig heap a);
    m'
  | Read b r k ->
    let k' x : dm ref heap a (fixed_wp ig heap a) = lift_to_dm #ref #heap ig (k x) in 
    let m' = Read b r k' in
    assert (ig r);
    assert (theta ref heap m' ⊑ fixed_wp ig heap a);
    m'
  | Write b r v k ->
    let k' x : dm ref heap a (fixed_wp ig heap a) = lift_to_dm #ref #heap ig (k x) in
    let m' = Write b r v k' in
    assert (ig r);
    assert (theta ref heap m' ⊑ fixed_wp ig heap a);
    m'

assume val lift_to_dm' #ref #heap #a (m:free ref a) : dm ref heap a (trivial_wp heap a)

type tgt_ctx0 (ref:Type0 -> Type0) (t t':Type)= t -> free ref t'
type src_ctx0 (ref:Type0 -> Type0) (heap:heap_t ref) (t t':Type) = t -> dm ref heap t' (trivial_wp heap t')
let bt0 #ref #heap #t #t' (ct:tgt_ctx0 ref t t') : src_ctx0 ref heap t t' =
  fun x -> lift_to_dm' (ct x)

type tgt_ctx0' (ref:Type0 -> Type0) (t t':Type)= ref t -> free ref t'
type src_ctx0' (ref:Type0 -> Type0) (heap:heap_t ref) (t t':Type) = r:ref t -> dm ref heap t' (fun p h0 -> h0 `heap.contains` r /\ (forall r' h1. p r' h1))
let bt0' #ref #heap #t #t' (ct:tgt_ctx0' ref t t') : src_ctx0' ref heap t t' =
  fun x -> lift_to_dm' #ref #heap (ct x)

type tgt_ctx0'' (ref:Type0 -> Type0) (t t':Type)= t -> free ref (ref t')
type src_ctx0'' (ref:Type0 -> Type0) (heap:heap_t ref) (t t':Type) = t -> dm ref heap (ref t') (fun p h0 -> (forall r h1. h1 `heap.contains` r ==> p r h1))
let bt0'' #ref #heap #t #t' (ct:tgt_ctx0'' ref t t') : src_ctx0'' ref heap t t' =
  fun x -> 
    let r = lift_to_dm' #ref #heap (ct x) in
    admit (); (* TODO: this admit can be removed by strengthening the spec lift_to_dm lifts to *)
    r

type tgt_ctx1 (ref:Type0 -> Type0) (t t':Type) = (t -> free ref t') -> free ref unit
type src_ctx1 (ref:Type0 -> Type0) (heap:heap_t ref) (t t':Type) = (t -> dm ref heap t' (trivial_wp heap t')) -> dm ref heap unit (trivial_wp heap unit)
let bt1 #ref #heap #t #t' (ct:tgt_ctx1 ref t t') : src_ctx1 ref heap t t' =
  fun cb -> lift_to_dm' (ct cb)

type tgt_ctx1' (ref:Type0 -> Type0) (t t':Type) = (ref t -> free ref t') -> free ref unit
type src_ctx1' (ref:Type0 -> Type0) (heap:heap_t ref) (t t':Type) = 
  (r:(ref t) -> dm ref heap t' (fun p h0 -> h0 `heap.contains` r /\ forall r' h1. p r' h1)) -> dm ref heap unit (trivial_wp heap unit)
let bt1' #ref #heap #t #t' (ct:tgt_ctx1' ref t t') : src_ctx1' ref heap t t' =
  fun cb -> lift_to_dm' (ct cb)

type tgt_ctx1'' (ref:Type0 -> Type0) (t t':Type) = (t -> free ref (ref t')) -> free ref unit
type src_ctx1'' (ref:Type0 -> Type0) (heap:heap_t ref) (t t':Type) = 
  (t -> dm ref heap (ref t') (fun p _ -> forall r h1. h1 `heap.contains` r ==> p r h1)) -> dm ref heap unit (trivial_wp heap unit)
let bt1'' #ref #heap #t #t' (ct:tgt_ctx1'' ref t t') : src_ctx1'' ref heap t t' =
  fun cb -> lift_to_dm' (ct cb)

type tgt_ctx6 (ref:Type0 -> Type0) (t t':Type) = unit -> free ref (t -> free ref t')
type src_ctx6 (ref:Type0 -> Type0) (heap:heap_t ref) (t t':Type) = unit -> dm ref heap (t -> dm ref heap t' (trivial_wp heap t')) (trivial_wp heap _)
let bt6 #ref #heap #t #t' (ct:tgt_ctx6 ref t t') : src_ctx6 ref heap t t' =
  fun x -> dm_subcomp (dm_bind (lift_to_dm' (ct x)) (fun (cb:t -> free ref t') -> dm_return #ref #heap (bt0 cb)))

type tgt_ctx6' (ref:Type0 -> Type0) (t t':Type) = unit -> free ref (ref t -> free ref t')
type src_ctx6' (ref:Type0 -> Type0) (heap:heap_t ref) (t t':Type) =
  unit -> dm ref heap (r:(ref t) -> dm ref heap t' (fun p h0 -> h0 `heap.contains` r /\ forall r' h1. p r' h1)) (trivial_wp heap _)
let bt6' #ref #heap #t #t' (ct:tgt_ctx6' ref t t') : src_ctx6' ref heap t t' =
  fun () -> dm_subcomp (dm_bind (lift_to_dm' (ct ())) (fun (cb:ref t -> free ref t') -> dm_return #ref #heap (bt0' cb)))

type tgt_ctx6'' (ref:Type0 -> Type0) (t t':Type) = unit -> free ref (t -> free ref (ref t'))
type src_ctx6'' (ref:Type0 -> Type0) (heap:heap_t ref) (t t':Type) =
  unit -> dm ref heap (t -> dm ref heap (ref t') (fun p h0 -> forall r h1. h1 `heap.contains` r ==> p r h1)) (trivial_wp heap _)
let bt6'' #ref #heap #t #t' (ct:tgt_ctx6'' ref t t') : src_ctx6'' ref heap t t' =
  fun () -> dm_subcomp (dm_bind (lift_to_dm'(ct ())) (fun (cb:t -> free ref (ref t')) -> dm_return #ref #heap (bt0'' cb)))

(** TODO:
  - [ ] Figure out if parametricity would be enough.
  - [ ] Doing Secure Compilation would not work because the source context has to be also parametic in the heap,
        which would not be possible with the effect system


**)