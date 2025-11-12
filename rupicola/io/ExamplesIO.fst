module ExamplesIO

open IO

let u_return : io bool = io_return true


(** let papply_io_return : bool -> io bool = io_return **)

let apply_io_return : bool -> io bool = fun x -> io_return x

let apply_read : io bool = read ()
let apply_write_const : io unit = write true
let apply_write : bool -> io unit = fun x -> write x

let apply_io_bind_const : io bool =
  io_bind (io_return true) (fun y -> io_return y)

let apply_io_bind_identity : bool -> io bool =
  fun x ->
    io_bind (io_return x) (fun y -> io_return y)

let apply_io_bind_pure_if : bool -> io bool =
  fun x ->
    io_bind (io_return x) (fun y -> if y then io_return false else io_return true)

let apply_io_bind_write : bool -> io unit =
  fun x ->
    io_bind (io_return x) (fun y -> write y)

let apply_io_bind_read_write : io unit =
    io_bind (read ()) (fun y -> write y)

let apply_io_bind_read_write' : io unit =
    io_bind (read ()) write

let apply_io_bind_read_if_write : io unit =
    io_bind (read ()) (fun y -> if y then write false else write true)
