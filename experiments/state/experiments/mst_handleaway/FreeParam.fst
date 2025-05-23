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
  t:Type u#1;

  contains : #a:Type0 -> t -> ref a -> Type0;

  alloc : #a:Type0 -> h0:t -> a -> Pure (ref a * t) True (fun rh1 -> 
    ~(h0 `contains` (fst rh1)) /\ (snd rh1) `contains` (fst rh1) /\
    (forall b (r':ref b). h0 `contains` r' ==> (snd rh1) `contains` r'));
  select : #a:Type0 -> h0:t -> r:ref a -> Pure a (h0 `contains` r) (fun _ -> True);
  update : #a:Type0 -> h0:t -> r:ref a -> v:a -> Pure t (h0 `contains` r) (fun h1 -> 
    (forall b (r':ref b). h0 `contains` r' ==> h1 `contains` r') /\
    h1 `contains` r /\ select h1 r == v);
}

type cref a = FStar.Monotonic.Heap.mref a (fun _ _ -> True)
assume val heap : heap_t cref
// type heap : heap_t cref = {
//   t = FStar.Monotonic.Heap.heap;

//   contains = (fun h r -> FStar.Monotonic.Heap.contains h r);

//   alloc = (fun h v -> admit ());
//   select = (fun h r -> admit ());
//   update = (fun h r v -> admit ());
// }


let rec theta
  (m:free cref 'a) : st_wp_h heap.t 'a =
  match m with
  | Return x -> st_return heap.t _ x
  | Alloc b x k ->
      st_bind_wp heap.t (cref b) 'a (fun p h0 -> let rh1 = heap.alloc h0 x in p (fst rh1) (snd rh1)) (fun r -> theta (k r))
  | Read b r k ->
      st_bind_wp heap.t b 'a (fun p h0 -> h0 `heap.contains` r /\ p (heap.select h0 r) h0) (fun r -> theta (k r))
  | Write b r v k ->
      st_bind_wp heap.t unit 'a (fun p h0 -> h0 `heap.contains` r /\ p () (heap.update h0 r v)) (fun r -> theta (k r))

unfold
let (⊑) #heap #a wp1 wp2 = st_stronger heap a wp2 wp1

type dm (a:Type) (wp:st_wp_h heap.t a) =
  m:(free cref a){theta m ⊑ wp}

let dm_return #a (x:a) : dm a (st_return heap.t a x) = Return x
let dm_bind #a #b #wpm #wpk (m:dm a wpm) (k:(x:a -> dm b (wpk x))) : dm b (st_bind_wp _ _ _ wpm wpk) = 
  let m' = free_bind m k in
  assume (theta m' ⊑ st_bind_wp heap.t a b wpm wpk);
  m'

let dm_subcomp #a #wpm #wpk (m:dm a wpm) : Pure (dm a wpk) (requires (wpm ⊑ wpk)) (ensures (fun _ -> True)) =
  m


let unit_test_return : dm int (fun p h0 -> p 1 h0) = Return 1
let unit_test_alloc  : dm (cref int) (fun p _ -> forall r h1. p r h1) = Alloc int 5 Return

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

let rec closed_free #a (ig:icontext cref) (m:free cref a) : Type0 =
  match m with
  | Return x -> True
  | Alloc b v k -> forall r. closed_free (extend_icontext ig #b r) (k r)
  | Read b r k -> ig r /\ (forall x. closed_free ig (k x))
  | Write b r v k -> ig r /\ (closed_free ig (k ()))

type cfree a = m:(free cref a){closed_free (icontext_empty cref) m}

let test1  : cfree unit = Return ()
let test2  : cfree (cref int) = Alloc int 5 Return
let test3  : cfree unit = 
  Alloc int 5 (fun r -> 
    Read int r (fun x -> 
      Write int r (x + 1) Return))

[@expect_failure]
let test4 (#ref:Type0 -> Type0) (r:ref int) : cfree ref unit = 
  Read int r (fun x -> 
    Write int r (x + 1) Return)

let test4' (r:cref int) : m:(free cref unit){closed_free (extend_icontext (icontext_empty cref) r) m} = 
  Read int r (fun x -> 
    Write int r (x + 1) Return)

[@expect_failure]
let test5 (#ref:Type0 -> Type0) (f:unit -> cfree ref (ref int)) : cfree ref unit = 
  free_bind (f ()) (fun r -> 
    Read int r (fun x -> 
      Write int r (x + 1) Return))

let closed_alloc_cont #a (ig:icontext cref) (b:Type0) (v:b) (k:cref b -> free cref a) :
  Lemma
    (requires (closed_free ig (Alloc b v k)))
    (ensures (forall r. closed_free (extend_icontext ig #b r) (k r))) = ()

let trivial_wp a : st_wp_h heap.t a = fun p _ -> forall r h1. p r h1

let fixed_wp (ig:icontext cref) a : st_wp_h heap.t a =
  fun p h0 -> 
    (forall b (r:cref b). ig r ==> h0 `heap.contains` r) /\ (** pre-cond **)
    (forall res h1. p res h1) (** post-cond **)

val lift_to_dm #a (m:free cref a) : dm a (theta m)
let lift_to_dm m = m

let rec lift_subcomp_lemma #a (ig:icontext cref) (m:free cref a) : Lemma
  (requires (closed_free ig m))
  (ensures (theta m ⊑ fixed_wp ig a)) =
  match m with
  | Return x -> ()
  | Alloc b v k -> 
    closed_alloc_cont ig b v k;
    introduce forall r. closed_free (extend_icontext ig #b r) (k r) ==> (theta (k r) ⊑ fixed_wp (extend_icontext ig #b r) a) with begin
      introduce closed_free (extend_icontext ig #b r) (k r) ==> (theta (k r) ⊑ fixed_wp (extend_icontext ig #b r) a)  with _. begin
        lift_subcomp_lemma (extend_icontext ig #b r) (k r)
      end
    end;
    assert (theta (Alloc b v k) ⊑ (fun p h0 -> let r, h1 = heap.alloc h0 v in theta (k r) p h1));
    assert (theta (Alloc b v k) ⊑ fixed_wp ig a)
  | Read b r k ->
    introduce forall x. closed_free ig (k x) ==> (theta (k x) ⊑ fixed_wp ig a) with begin
      introduce closed_free ig (k x) ==> (theta (k x) ⊑ fixed_wp ig a)  with _. begin
        lift_subcomp_lemma ig (k x)
      end
    end
  | Write b r v k ->
    introduce forall x. closed_free ig (k x) ==> (theta (k x) ⊑ fixed_wp ig a) with begin
      introduce closed_free ig (k x) ==> (theta (k x) ⊑ fixed_wp ig a)  with _. begin
        lift_subcomp_lemma ig (k x)
      end
    end

val lift_subcomp #a ig (m:free cref a) (#_:squash (closed_free ig m)) : dm a (fixed_wp ig a)
let lift_subcomp ig m #_ =
  let m' = lift_to_dm m in
  lift_subcomp_lemma ig m;
  dm_subcomp m'




type tgt_ctx0 (t t':Type)= ref:(Type0 -> Type0) -> t -> free ref t'
type src_ctx0 (t t':Type) = t -> dm t' (trivial_wp t')
let bt0 #t #t' (ct:tgt_ctx0 t t') : src_ctx0 t t' =
  fun x ->
    let c = ct cref x in
    assume (closed_free (icontext_empty cref) c);
    lift_subcomp (icontext_empty cref) c

type tgt_ctx0' (t t':Type)= ref:(Type0 -> Type0) -> ref t -> free ref t'
type src_ctx0' (t t':Type) = r:cref t -> dm t' (fun p h0 -> h0 `heap.contains` r /\ (forall r' h1. p r' h1))
let bt0' #ref #heap #t #t' (ct:tgt_ctx0' t t') : src_ctx0' t t' =
  fun r -> 
    let c = ct cref r in
    assume (closed_free (extend_icontext (icontext_empty cref) r) c);
    lift_subcomp (extend_icontext (icontext_empty cref) r) c

type tgt_ctx0'' (t t':Type)= ref:(Type0 -> Type0) -> t -> free ref (ref t')
type src_ctx0'' (t t':Type) = t -> dm (cref t') (fun p h0 -> (forall r h1. h1 `heap.contains` r ==> p r h1))
let bt0'' #t #t' (ct:tgt_ctx0'' t t') : src_ctx0'' t t' =
  fun x -> 
    let c = ct cref x in
    assume (closed_free (icontext_empty cref) c);
    let comp = lift_subcomp (icontext_empty cref) c in
    admit (); (* TODO: this admit can be removed by strengthening the spec lift_to_dm lifts to *)
    comp

type tgt_ctx1 (t t':Type) = ref:(Type0 -> Type0) -> (t -> free ref t') -> free ref unit
type src_ctx1 (t t':Type) = (t -> dm t' (trivial_wp t')) -> dm unit (trivial_wp unit)
let bt1 #ref #heap #t #t' (ct:tgt_ctx1 t t') : src_ctx1 t t' =
  fun cb -> 
    let c = ct cref cb in
    assume (closed_free (icontext_empty cref) c);
    lift_subcomp (icontext_empty cref) c

type tgt_ctx1' (t t':Type) = ref:(Type0 -> Type0) -> (ref t -> free ref t') -> free ref unit
type src_ctx1' (t t':Type) = 
  (r:(cref t) -> dm t' (fun p h0 -> h0 `heap.contains` r /\ forall r' h1. p r' h1)) -> dm unit (trivial_wp unit)
let bt1' #t #t' (ct:tgt_ctx1' t t') : src_ctx1' t t' =
  fun cb ->
    let c = ct cref cb in
    assume (closed_free (icontext_empty cref) c);
    lift_subcomp (icontext_empty cref) c

type tgt_ctx1'' (t t':Type) = ref:(Type0 -> Type0) -> (t -> free ref (ref t')) -> free ref unit
type src_ctx1'' (t t':Type) = 
  (t -> dm (cref t') (fun p _ -> forall r h1. h1 `heap.contains` r ==> p r h1)) -> dm unit (trivial_wp unit)
let bt1'' #t #t' (ct:tgt_ctx1'' t t') : src_ctx1'' t t' =
  fun cb ->
    let c = ct cref cb in
    assume (closed_free (icontext_empty cref) c);
    lift_subcomp (icontext_empty cref) c

type tgt_ctx6 (t t':Type) = ref:(Type0 -> Type0) -> unit -> free ref (t -> free ref t')
type src_ctx6 (t t':Type) = unit -> dm (t -> dm t' (trivial_wp t')) (trivial_wp _)
let bt6 #t #t' (ct:tgt_ctx6 t t') : src_ctx6 t t' =
  fun () -> 
    let c = ct cref () in
    assume (closed_free (icontext_empty cref) c);
    admit ();
    dm_subcomp #_ #_ #(trivial_wp _) (
      dm_bind 
        (lift_subcomp (icontext_empty cref) c) 
        (fun (cb:t -> free cref t') -> 
          dm_return cb)) // <-- one has to lift this too, but under which assumption

type tgt_ctx6' (t t':Type) = ref:(Type0 -> Type0) -> unit -> free ref (ref t -> free ref t')
type src_ctx6' (t t':Type) =
  unit -> dm (r:(cref t) -> dm t' (fun p h0 -> h0 `heap.contains` r /\ forall r' h1. p r' h1)) (trivial_wp _)
let bt6' #t #t' (ct:tgt_ctx6' t t') : src_ctx6' t t' =
  fun () -> 
    let c = ct cref () in
    assume (closed_free (icontext_empty cref) c);
    admit ();
    dm_subcomp #_ #_ #(trivial_wp _) (
      dm_bind 
        (lift_subcomp (icontext_empty cref) c) 
        (fun (cb:cref t -> free cref t') ->
          dm_return cb)) // <-- one has to lift this too, but under which assumption

type tgt_ctx6'' (t t':Type) = ref:(Type0 -> Type0) -> unit -> free ref (t -> free ref (ref t'))
type src_ctx6'' (t t':Type) =
  unit -> dm (t -> dm (cref t') (fun p h0 -> forall r h1. h1 `heap.contains` r ==> p r h1)) (trivial_wp _)
let bt6'' #t #t' (ct:tgt_ctx6'' t t') : src_ctx6'' t t' =
  fun () -> 
    let c = ct cref () in
    assume (closed_free (icontext_empty cref) c);
    admit ();
    dm_subcomp #_ #_ #(trivial_wp _) (
        dm_bind 
          (lift_subcomp (icontext_empty cref) c) 
          (fun (cb:t -> free cref (cref t')) -> 
            dm_return cb)) // <-- one has to lift this too, but under which assumption

(** TODO:
  - [ ] Figure out if parametricity would be enough.


**)