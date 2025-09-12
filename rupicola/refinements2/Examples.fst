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

let test_if_x
  : (f:(x:bool{x == true}) -> bool) -> bool -> bool
  = fun f x -> if x then f x else false

assume val p_ref : bool -> Type0
assume val q_ref : bool -> Type0
let test_p_implies_q
  : (f: (x:bool{p_ref x} -> _:unit{q_ref x})) -> (x:bool{p_ref x}) -> (x:bool{q_ref x})
  = fun f x -> f x; x

let test_false_elim0
  : bool -> bool
  = fun x -> if x then if x then true else false_elim () else true

let test_false_elim1
  : x:unit{False} -> Tot bool
  = fun x -> false_elim ()

let test_false_elim2
  : f:(unit -> x:bool{x == true}) -> Tot bool
  = fun f -> if f () then true else false_elim ()

let test_erase_ref
  : (x:bool{x == true} -> bool)
  = fun x -> x
