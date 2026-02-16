module ExamplesIO

open IO

let u_return () : io bool = return true

let apply_io_return : bool -> io bool = fun x -> io_return x

let apply_read () : io (resexn string) = read 0
let apply_write_const () : io (resexn unit) = write (2,"hello")
let apply_write : string -> io (resexn unit) = fun x -> write (1,x)

let apply_io_bind_const () : io bool =
  let!@ x = io_return true in
  io_return x

let apply_io_bind_identity : bool -> io bool =
  fun x ->
    let!@ y = io_return x in
    io_return y

let apply_io_bind_pure_if : bool -> io bool =
  fun x ->
    if!@ (io_return x) then io_return false
    else io_return true

let apply_io_bind_write : string -> io (resexn unit) =
  fun x ->
    let!@ y = io_return x in
    write (2,y)

let apply_io_bind_read_write () : io (resexn unit) =
  match!@ read 4 with
  | Inl _ -> write (1,"data")
  | Inr x -> io_return (Inr x)

let apply_io_bind_read_write' () : io (resexn unit) =
  io_bind (read 9) (fun x -> match x with | Inl _ -> write (2,"data") | Inr x -> io_return (Inr x))

let apply_io_bind_read_if_write () : io (resexn unit) =
  match!@ read 0 with
  | Inl _ -> write (7,"data")
  | Inr x -> return (Inr x)

(** Examples inspired from the Web Server **)
val utf8_encode : bool -> bool
let utf8_encode x = x

let sendError400 (fd:bool) : io unit =
  write (9, "error400") ;!@
  return ()

let get_req (fd:bool) : io (either bool bool) =
  let x = utf8_encode fd in
  match!@ read 11 with
  | Inl _ -> return (Inl true)
  | Inr _ -> return (Inr false)

let (let!@!) #a #b (m:io (resexn a)) (k:a -> io (resexn b)) =
  match!@ m with
  | Inl x -> k x
  | Inr x -> return (Inr x)

let open2_read_write () =
  let!@! fd1 = openfile "/tmp/input" in
  let!@! fd2 = openfile "/tmp/output" in
  let!@! data = read fd1 in
  write (fd2, data)
