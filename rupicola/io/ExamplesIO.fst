module ExamplesIO

open IO

let u_return : io bool = return true


(** let papply_io_return : bool -> io bool = io_return **)

let apply_io_return : bool -> io bool = fun x -> return x

let apply_read : io (resexn bool) = read 0
let apply_write_const : io (resexn unit) = write (2,true)
let apply_write : bool -> io (resexn unit) = fun x -> write (1,x)

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

let apply_io_bind_write : bool -> io (resexn unit) =
  fun x ->
    let!@ y = return x in
    write (2,y)

let apply_io_bind_read_write : io (resexn unit) =
  match!@ read 4 with
  | Inl x -> write (1,x)
  | Inr x -> return (Inr x)

let apply_io_bind_read_write' : io (resexn unit) =
  io_bind (read 9) (fun x -> match x with | Inl x -> write (2,x) | Inr x -> return (Inr x))

let apply_io_bind_read_if_write : io (resexn unit) =
  match!@ read 0 with
  | Inl x -> if x
            then write (7,false)
            else write (8,true)
  | Inr x -> return (Inr x)

(** Examples inspired from the Web Server **)
val utf8_encode : bool -> bool
let utf8_encode x = x

let sendError400 (fd:bool) : io unit =
  let x = utf8_encode true in
  let p = (fd, x) in
  write (9, fd) ;!@
  return ()

let get_req (fd:bool) : io (either bool bool) =
  let x = utf8_encode fd in
  match!@ read 11 with
  | Inl x -> if x then return (Inl true) else return (Inr false)
  | Inr x -> return (Inr false)
