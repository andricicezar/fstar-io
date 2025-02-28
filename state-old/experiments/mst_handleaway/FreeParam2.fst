module FreeParam2

open FStar.Tactics
open FStar.Tactics.Typeclasses


noeq
type freeT (ref:Type0 -> Type0) (a:Type u#a) : Type u#(max 1 a) = (* because of the references *)
| TAlloc : #b:Type0 -> b -> (ref b -> freeT ref a) -> freeT ref a
| TRead : #b:Type0 -> ref b -> (b -> freeT ref a) -> freeT ref a
| TWrite : #b:Type0 -> ref b -> b -> (unit -> freeT ref a) -> freeT ref a
| TReturn : a -> freeT ref a

let freeT_return #ref (x:'a) : freeT ref 'a = TReturn x

let rec freeT_bind #ref (m:freeT ref 'a) (k:'a -> freeT ref 'b) : freeT ref 'b =
  match m with
  | TReturn x -> k x
  | TAlloc x cont -> TAlloc x (fun x -> freeT_bind (cont x) k)
  | TRead r cont -> TRead r (fun x -> freeT_bind (cont x) k)
  | TWrite r v cont -> TWrite r v (fun x -> freeT_bind (cont x) k)

open MST.Repr
open MHeap

type cref a =
  r:(ref a){ witnessed (contains_pred r) }

// let rec lift_freeT #a (c:freeT cref a) : free heap_state a =
//   match c with
//   | TReturn x -> Return x
//   | TRead r cont -> Read r (fun x -> lift_freeT (cont x))
//   | TWrite r v cont -> Write r v (fun _ -> lift_freeT (cont ()))
//   | TAlloc x cont -> Alloc x (fun r -> lift_freeT (cont r)) (** here one needs to witness that r is allocated, not possible with ghost witnessed **)

let rec lift_freeT #a (c:freeT cref a) : mheap a (fun p h -> forall r h1. h `heap_rel` h1 ==> p r h1) =
  match c with
  | TReturn x -> mheap_return _ x
  | TRead r cont -> 
      mheap_bind _ _ _ _
        (mheap_recall (contains_pred r))
        (fun _ -> mheap_bind _ _ _ _  (mheap_read r)
                                   (fun x -> lift_freeT (cont x)))
  | TWrite r v cont -> 
      mheap_bind _ _ _ _
        (mheap_recall (contains_pred r))
        (fun _ -> mheap_bind _ _ _ _  (mheap_write r v)
                                   (fun x -> lift_freeT (cont x)))

  | TAlloc init cont -> 
      mheap_bind _ _ _ _
        (mheap_alloc init)
        (fun (r:ref _) ->
          mheap_bind _ _ _ _
            (mheap_witness (contains_pred #_ #(FStar.Heap.trivial_preorder _) r))
            (fun _ -> 
              mheap_bind _ _ _ _
                (mheap_require (witnessed (contains_pred r))) (** "revealing" ghost witnessed **)
                (fun _ -> lift_freeT (cont r))))

type tgt_ctx0 (t t':Type)= ref:(Type0 -> Type0) -> t -> freeT ref t'
type src_ctx0 (t t':Type) = t -> mheap t' (fun p h -> forall r h1. p r h1)
let bt0 #t #t' (ct:tgt_ctx0 t t') : src_ctx0 t t' =
  fun x ->
    let c = ct cref x in
    lift_freeT c

type tgt_ctx0' (t t':Type)= ref:(Type0 -> Type0) -> ref t -> freeT ref t'
type src_ctx0' (t t':Type) = r:cref t -> mheap t' (fun p h0 -> h0 `heap_state.contains` r /\ (forall r' h1. p r' h1))
let bt0' #t #t' (ct:tgt_ctx0' t t') : src_ctx0' t t' =
  fun r -> 
    let c = ct cref r in
    lift_freeT c


(**
type tgt_ctx0'' (t t':Type)= ref:(Type0 -> Type0) -> t -> freeT ref (ref t')
type src_ctx0'' (t t':Type) = t -> mheap (cref t') (fun p h0 -> (forall r h1. h1 `heap_state.contains` r ==> p r h1)) (** cannot prove monotonicity **)
let bt0'' #t #t' (ct:tgt_ctx0'' t t') : src_ctx0'' t t' =
  fun x -> 
    let c = ct cref x in
    lift_freeT c
**)

let trivial_wp a : st_wp_h heap_state.t a = fun p _ -> forall r h1. p r h1

let rec erase_mheap #a (c:free heap_state a) : freeT cref a =
  match c with
  | Return x -> TReturn x
  | Witness _ k -> erase_mheap (k ())
  | Recall _ k -> erase_mheap (k ())
 // | Read r k -> TRead (r <: cref _) (fun v -> erase_mheap (k v)) 
    (** r does not have the refinement that it is witnessed **)
  | _ -> admit ()

type tgt_ctx1 (t t':Type) = ref:(Type0 -> Type0) -> (t -> freeT ref t') -> freeT ref unit
type src_ctx1 (t t':Type) = (t -> mheap t' (trivial_wp t')) -> mheap unit (trivial_wp unit)
let bt1 #ref #heap #t #t' (ct:tgt_ctx1 t t') : src_ctx1 t t' =
  fun cb -> 
    let c = ct cref cb in (** cb is typed as `free` but `freeT` is expected. TODO: implement erase_mheap **)
    lift_freeT c
