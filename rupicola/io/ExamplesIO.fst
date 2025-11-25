module ExamplesIO

open IO

let u_return : io bool = io_return true


(** let papply_io_return : bool -> io bool = io_return **)

let apply_io_return : bool -> io bool = fun x -> io_return x

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
  io_bind (read ()) write

let apply_io_bind_read_if_write : io unit =
  let!@ x = read () in
  if x
  then write false
  else write true
