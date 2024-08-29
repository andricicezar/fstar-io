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

(** This is Theo's Iter type constructor from non-terminating IO *)
noeq
type dv (a:Type u#a) : Type u#1 =
// Return : a -> dv a (** this pushes the type in universe a *)
| Iter : i:Type0 -> ii:i -> b:Type0 -> (i -> dv (raise_t (either i b))) -> (b -> dv a) -> dv a
| PartialCall : pre:Type0 -> (squash pre -> dv a) -> dv a

let dv_return a (x:a) : dv a = admit () (* TODO *)

(** Looking at state for a second **)
type div_st (ht:Type u#s) (a:Type u#a) : Type u#s =
  ht -> Dv (ht * a)

type arrow_div_st (ht:Type u#s) (a:Type u#a) (b:Type u#b) : Type u#(max a s) =
  a -> div_st ht b

noeq
type st (ht:Type u#s) (a:Type u#a) : Type u#(max 1 s) =
| StIter : i:Type0 -> ii:i -> b:Type0 -> (i -> st ht (raise_t (either i b))) -> (b -> st ht a) -> st ht a
| StPut : h:ht -> (unit -> st ht a) -> st ht a
| StGet : unit -> (ht -> st ht a) -> st ht a
| StPartialCall : pre:Type0 -> (squash pre -> st ht a) -> st ht a

type arrow_my_st (ht:Type u#s) (a:Type u#a) (b:Type u#b) : Type u#(max 1 a s) =
  a -> st ht b
