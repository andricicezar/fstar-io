module ExamplesIO

open Free

let u_return : free bool = free_return true


(** let papply_free_return : bool -> free bool = free_return **)

let apply_free_return : bool -> free bool = fun x -> free_return x

let apply_free_read : free bool = free_read ()
let apply_free_write_const : free unit = free_write true
let apply_free_write : bool -> free unit = fun x -> free_write x

let apply_free_bind_const : free bool =
  free_bind (free_return true) (fun y -> free_return y)

let apply_free_bind_identity : bool -> free bool =
  fun x ->
    free_bind (free_return x) (fun y -> free_return y)

let apply_free_bind_pure_if : bool -> free bool =
  fun x ->
    free_bind (free_return x) (fun y -> if y then free_return false else free_return true)

let apply_free_bind_write : bool -> free unit =
  fun x ->
    free_bind (free_return x) (fun y -> free_write y)

let apply_free_bind_read_write : free unit =
    free_bind (free_read ()) (fun y -> free_write y)

let apply_free_bind_read_write' : free unit =
    free_bind (free_read ()) free_write

let apply_free_bind_read_if_write : free unit =
    free_bind (free_read ()) (fun y -> if y then free_write false else free_write true)
