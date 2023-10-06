open CommonUtils
open FStar_Pervasives
open UnixTypes

(** This file is a wrapper over the OCaml's Unix module to accomodate
    F* needs. This should be as close as possible to the Unix interface **)

let openfile (file_name, flags, perm) : file_descr =
  Unix.openfile file_name flags (Z.to_int perm)

let read (fd, limit) : (FStar_Bytes.bytes * int) =
  let buff = Bytes.make 256 '\000' in
  let c = Unix.read fd buff 0 limit in
  ((Bytes.to_string buff), c)

let write (fd, message) : unit =
  let _ = Unix.write_substring fd message 0 (String.length message) in
  ()

let close fd : unit =
  Unix.close fd

let socket () : file_descr =
  Unix.socket Unix.PF_INET Unix.SOCK_STREAM 0

let setsockopt (socket, opt, value) : unit =
  Unix.setsockopt socket opt value

let bind (socket, address, port) : unit =
  Unix.bind socket (Unix.ADDR_INET(Unix.inet_addr_of_string address, port))

let setnonblock fd : unit = 
  Unix.set_nonblock fd

let listen (fd, limit) : unit = 
  Unix.listen fd limit

let accept fd : Unix.file_descr = 
  let fd', _ = Unix.accept fd in
  fd'

let select (l1, l2, l3, t) : (lfds * lfds * lfds) =
  Unix.select l1 l2 l3 (100.0 /. 1000.0)

let access m l : unit =
  Unix.access m l

let stat m : stats =
  Unix.stat m
