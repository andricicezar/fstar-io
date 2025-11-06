module Examples

let identity : bool -> bool =
  fun x -> x

let thunked_id : bool -> bool -> bool =
  fun x y -> y

let call_arg : (unit -> unit) -> unit =
  fun f -> f ()

let call_arg2 : (bool -> bool -> bool) -> bool =
  fun f -> f true false

let proj1 : bool -> bool -> bool -> bool =
  fun x y z -> x

let proj2 : bool -> bool -> bool -> bool =
  fun x y z -> y

let proj3 : bool -> bool -> bool -> bool =
  fun x y z -> z

let anif : bool = if true then false else true

let negb : bool -> bool =
  fun x -> if x then false else true

let negb_pred : (bool -> bool) -> bool -> bool =
  fun f x -> negb (f x)

let if2 : bool -> bool -> bool =
  fun x y -> if x then false else y

let callback_return : bool -> (bool -> bool) =
  fun x -> if x then (fun _ -> x) else (fun z -> z)

let callback_return' : bool -> (bool -> bool) =
  fun x -> if x then (fun _ -> x) else identity
