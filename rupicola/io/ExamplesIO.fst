module ExamplesIO

open IO

let u_return : io bool = return true


(** let papply_io_return : bool -> io bool = io_return **)

let apply_io_return : bool -> io bool = fun x -> return x

let apply_read : io bool = read ()
let apply_write_const : io unit = write true
let apply_write : bool -> io unit = fun x -> write x

let apply_io_bind_const : io bool =
  let!@ x = return true in
  return x

let apply_io_bind_identity : bool -> io bool =
  fun x ->
    let!@ y = return x in
    return y

let apply_io_bind_pure_if : bool -> io bool =
  fun x ->
    if!@ (return x) then return false
    else return true

let apply_io_bind_write : bool -> io unit =
  fun x ->
    let!@ y = return x in
    write y

let apply_io_bind_read_write : io unit =
  let!@ x = read () in
  write x

let apply_io_bind_read_write' : io unit =
  io_bind (read ()) (fun x -> write x)

let apply_io_bind_read_if_write : io unit =
  let!@ x = read () in
  if x
  then write false
  else write true

(** Examples inspired from the Web Server **)
val utf8_encode : bool -> bool
let utf8_encode x = x

let sendError400 (fd:bool) : io unit =
  let x = utf8_encode true in
  let p = (fd, x) in
  write fd ;!@
  return ()

let get_req (fd:bool) : io (either bool bool) =
  let x = utf8_encode fd in
  if!@ (read ())
  then return (Inl true)
  else return (Inr false)
