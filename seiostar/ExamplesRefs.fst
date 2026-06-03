module ExamplesRefs

open Trace

let refbool : (t:bool{t == true}) = true

let falsepre : (x:bool{False} -> bool) =
  fun x -> x

let just_true
  : bool -> (x:bool{x == true})
  = fun x -> true

assume val some_ref : Type0
let moving_ref
  : _:bool{some_ref} -> _:unit{some_ref}
  = fun _ -> ()

let always_false
  : bool -> y:bool{y == false}
  = fun x -> if x then false else x

let always_false_complex
  : bool -> y:bool{y == false}
  = fun x -> if x then if x then false else true else false

let always_false_ho
  : (f:(unit -> x:bool{x == true})) -> y:bool{y == false}
  = fun f -> if f () then false else true

let if_x
  : (f:(x:bool{x == true}) -> bool) -> bool -> bool
  = fun f x -> if x then f x else false

assume val p_ref : bool -> Type0
assume val q_ref : Type0

let seq_basic
  : (f: (unit -> unit)) -> unit
  = fun f -> (f ()) ; ()

let seq_qref
  : (f: (unit -> _:unit{q_ref})) -> (_:unit{q_ref})
  = fun f -> (f ()) ; ()

let seq_p_implies_q
  : (f: (x:bool{p_ref x} -> _:unit{q_ref})) -> (x:bool{p_ref x}) -> (x:bool{q_ref})
  = fun f x -> f x ; x

let if_seq
  : (f: (x:bool{x == true} -> _:unit{q_ref})) -> (x:bool) -> (r:bool{r == true ==>  q_ref})
  = fun f x -> if x then (f x ; x) else x

let context
  : (x:bool) -> (f:(x:bool{x == true}) -> bool -> bool) -> bool -> bool
  = fun x f ->
    if x then (f x)
    else (fun y -> y)

let needs_true (b:bool{b == true}) : bool = b
let proj_into_refined
  : (p:(bool & bool){fst p == true}) -> bool
  = fun p -> needs_true (fst p)

let fun_beh_ref
  : (f:(b:bool{b == true} -> bool){forall (b:bool{b == true}). f b == b})
  = fun b -> true

let refined_pair_inner
  : (x:bool) -> ((x:bool{x == true}) & y:bool{y == false})
  = fun x ->
  if x then (x, false) else (true, false)

let refined_pair
  : (x:bool) -> p:(bool & bool){fst p == true /\ snd p == false}
  = fun x ->
  if x then (x, false) else (true, false)

assume val valid : string -> Type0

let ret_refined_arg : (x:string{valid x}) -> (x:string{valid x}) = fun x -> x

let inl_refined_arg : (x:string{valid x}) -> (resexn (x:string{valid x})) = fun x -> Inl x

let pure_validate (x:string) (f:(string -> bool){forall x. f x ==> valid x}) : (resexn (x:string{valid x})) =
  if f x
  then Inl x
  else Inr ()

let pure_validate2 (x:string{valid x}) (f:(x:string{valid x} -> bool)) : bool = f x
let pure_validate3 (x:string{valid x}) (f:(x:string{valid x} -> bool)) : (Trace.resexn (x:string{valid x})) =
  if f x
  then Inl x
  else Inr ()

type nat8 = x:nat{x <= 255}

let incr_nat8 (p:nat8{p + 1 <= 255}) : nat8 =
  p + 1


let incr_nat8' : f:(x:nat8{x + 1 <= 255} -> nat8){forall x. f x == x + 1} =
 fun x -> x + 1
