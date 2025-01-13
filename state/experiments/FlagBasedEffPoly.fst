module FlagBasedEffPoly

open FStar.Monotonic.Heap
open FStar.ST

type myref a =
  Heap.mref a (fun _ _ -> True)

type fo_ctx =
  // fl:erased tflag -> (** we don't have flag yets for ST **)
  #inv:(heap -> Type0) -> (** invariant on the heap **)
  #prref:((#a:Type0) -> ref a -> Type0) -> (** predicate that refines references **)
  read : ((#a:Type0) -> x:ref a -> ST a (fun h0 -> inv h0 /\ prref x) (fun _ _ h1 -> inv h1)) ->
  write : ((#a:Type0) -> x:ref a -> v:a -> ST unit (fun h0 -> inv h0 /\ prref x) (fun _ _ h1 -> inv h1)) ->
  alloc : ((#a:Type0) -> init:a -> ST (ref a) (fun h0 -> inv h0) (fun _ r h1 -> inv h1 /\ prref r)) ->
  ST unit (inv) (fun _ _ -> inv)

val ctx1 : fo_ctx
let ctx1 my_read my_write my_alloc =
  let x = my_alloc 5 in
  let y = my_read x in
  my_write x (y+1);
  ()

type rho_ctx =
  // fl:erased tflag ->
  #inv:(heap -> Type0) ->
  #prref:((#a:Type0) -> myref a -> Type0) ->
  read : ((#a:Type0) -> x:ref a -> ST a (fun h0 -> inv h0 /\ prref x) (fun _ _ h1 -> inv h1)) ->
  write : ((#a:Type0) -> x:ref a -> v:a -> ST unit (fun h0 -> inv h0 /\ prref x) (fun _ _ h1 -> inv h1)) ->
  alloc : ((#a:Type0) -> init:a -> ST (ref a) (fun h0 -> inv h0) (fun _ r h1 -> inv h1 /\ prref r)) ->
  ST (unit -> ST unit (inv) (fun _ _ -> inv)) (inv) (fun _ _ -> inv)

val ctx2 : rho_ctx
let ctx2 #_ #prref my_read my_write my_alloc =
  let x : ref int = my_alloc 5 in
  (fun () -> 
    assert (prref x); (** why is this working? because ref cannot change. the predicate is not over the heap **)
    let y = my_read x in ())
