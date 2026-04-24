module ExamplesIO

open IOStar

let u_return () : io bool = return true

let apply_io_return : bool -> io bool = fun x -> io_return x

let apply_read (fd:file_descr) : io (resexn string) = io_call ORead fd
let apply_write_const (fd:file_descr) : io (resexn unit) = io_call OWrite (fd,"hello")
let apply_write : file_descr -> string -> io (resexn unit) = fun fd x -> io_call OWrite (fd,x)

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

let apply_io_bind_write : file_descr -> string -> io (resexn unit) =
  fun fd x ->
    let!@ y : string = io_return x in
    io_call OWrite (fd, y) <: io (resexn unit)

let apply_io_bind_read_write (fd1 fd2:file_descr) : io (resexn unit) =
  match!@ io_call ORead fd1 with
  | Inl _ -> io_call OWrite (fd2,"data")
  | Inr x -> io_return (Inr x)

let apply_io_bind_read_write' (fd1 fd2:file_descr) : io (resexn unit) =
  io_bind (io_call ORead fd1) (fun x -> match x with | Inl _ -> io_call OWrite (fd2,"data") | Inr x -> io_return (Inr x))

let apply_io_bind_read_if_write (fd1 fd2:file_descr) : io (resexn unit) =
  match!@ io_call ORead fd1 with
  | Inl _ -> io_call OWrite (fd2,"data")
  | Inr x -> return (Inr x)

(** Examples inspired from the Web Server **)
val utf8_encode : bool -> bool
let utf8_encode x = x

let sendError400 (fd:file_descr) : io unit =
  io_call OWrite (fd, "error400") ;!@
  return ()

let get_req (fd:file_descr) (msg:bool) : io (either bool bool) =
  let x = utf8_encode msg in
  match!@ io_call ORead fd with
  | Inl _ -> return (Inl true)
  | Inr _ -> return (Inr false)

let (let!@!) #a #b (m:io (resexn a)) (k:a -> io (resexn b)) =
  match!@ m with
  | Inl x -> k x
  | Inr x -> io_return (Inr x)

let open2_read_write () =
  let!@! fd1 = io_call OOpen "/tmp/input" in
  let!@! fd2 = io_call OOpen "/tmp/output" in
  let!@! data = io_call ORead fd1 in
  io_call OWrite (fd2, data)

val eq_string : string -> string -> bool
let eq_string s t =
  s = t

let echo (fd1 fd2:file_descr) =
  let!@! data = io_call ORead fd1 in
  io_call OWrite (fd2, data)
