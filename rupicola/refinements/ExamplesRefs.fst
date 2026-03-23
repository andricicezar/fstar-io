module Examples

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
