module Examples

let test_just_true
  : bool -> (x:bool{x == true})
  = fun x -> true

assume val some_ref : Type0
let test_moving_ref
  : _:bool{some_ref} -> _:unit{some_ref}
  = fun _ -> ()

let test_always_false
  : bool -> y:bool{y == false}
  = fun x -> if x then false else x

let test_always_false_complex
  : bool -> y:bool{y == false}
  = fun x -> if x then if x then false else true else false

let test_always_false_ho
  : (f:(unit -> x:bool{x == true})) -> y:bool{y == false}
  = fun f -> if f () then false else true

let test_if_x
  : (f:(x:bool{x == true}) -> bool) -> bool -> bool
  = fun f x -> if x then f x else false

assume val p_ref : bool -> Type0
assume val q_ref : Type0
let test_p_implies_q_simpl
  : (f: (unit -> _:unit{q_ref})) -> (_:unit{q_ref})
  = fun f -> f (); ()

let test_p_implies_q_simpl'
  : (f: (unit -> _:unit{q_ref})) -> bool -> (_:bool{q_ref})
  = fun f x -> f (); x

let test_p_implies_q
  : (f: (x:bool{p_ref x} -> _:unit{q_ref})) -> (x:bool{p_ref x}) -> (x:bool{q_ref})
  = fun f x -> f x; x

let test_true_implies_q
  : (f: (x:bool{x == true} -> _:unit{q_ref})) -> (x:bool) -> (x:bool{x == true ==>  q_ref})
  = fun f x -> if x then (f x; x) else false

let test_context
  : (x:bool{p_ref x}) -> (f:(x:bool{p_ref x}) -> bool -> bool) -> (bool -> bool)
  = fun x f y -> f x y
