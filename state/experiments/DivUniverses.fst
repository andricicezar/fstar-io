module DivUniverses

open FStar.Universe

#set-options "--print_universes"

type test_pure_arr (a:Type u#a) (b:Type u#b) : Type u#(max a b) =
  a -> b

type test_pure_123_arr (a:Type u#a) (b:Type u#b) : Type u#(max a b) =
  a -> Pure b (requires (5 > 2)) (ensures fun _ -> True)
  
type test_dv_arr (a:Type u#a) (b:Type u#b) : Type u#a =
  a -> Dv b

(* 
Looks like the representation of Div has to be constant in a universe (desirably 0),
so we're looking for

Dv : Type u#a -> Type u#0
*)

(** Representation of state using state passing **)
type div_st (ht:Type u#s) (a:Type u#a) : Type u#s = (* the universe of the Monotonic Heap is 1 *)
  ht -> Dv (ht * a)

type arrow_div_st (ht:Type u#s) (a:Type u#a) (b:Type u#b) : Type u#(max a s) =
  a -> div_st ht b

(* Not marking an effect with total, it defines the effect in universe 0,
   even if the representation is not.
   
   One can think about it as a transformer of the following type: **)

assume val trans : (m:Type u#a -> Type u#b) -> Type u#a -> Type u#0

type div_mst (a:Type u#a) : Type u#1 = div_st FStar.Monotonic.Heap.heap a

type div_mst0 (a:Type u#a) : Type u#0 = trans div_mst a

type arrow_mst (a:Type u#a) (b:Type u#b) : Type u#a =
  a -> div_mst0 b
(* ^ compared to `arrow_div_st`, this arrow is in universe a, even if the heap is universe 1 *)

(** This is Theo's Iter type constructor from non-terminating IO *)
noeq
type dv (a:Type u#a) : Type u#1 =
// Return : a -> dv a (** this pushes the type in universe a *)
| Iter : i:Type0 -> ii:i -> b:Type0 -> (i -> dv (raise_t (either i b))) -> (b -> dv a) -> dv a
| PartialCall : pre:Type0 -> (squash pre -> dv a) -> dv a

let dv_return a (x:a) : dv a = admit () (* TODO *)
