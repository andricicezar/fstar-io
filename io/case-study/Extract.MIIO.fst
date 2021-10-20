module Extract.MIIO

open FStar.All
open Common
open Free
open Free.IO
open DM
open Export
open Extract.ML

val ml_cmd : cmd:cmds -> args cmd -> ML (res cmd)
let ml_cmd cmd =
  match cmd with
  | Openfile -> ml_openfile
  | Read -> ml_read
  | Write -> ml_write
  | Close -> ml_close
  | Socket -> ml_socket
  | Setsockopt -> ml_setsockopt
  | Bind -> ml_bind
  | SetNonblock -> ml_setnonblock
  | Listen -> ml_listen
  | Accept -> ml_accept
  | Select -> ml_select
  | GetTrace -> ml_gettrace

let rec iio_interpreter #t1 (t:iio t1) : ML t1 =
  match t with
  | Return r -> r
  | Call cmd argz fnc ->
      iio_interpreter #t1 (fnc (ml_cmd cmd argz))

let extract_MIIO
  (#t1:Type) {| d1:importable t1 |}
  (#t2:Type) {| d2:exportable t2 |}
  (f:t1 -> MIIO t2)
  (x:d1.itype) :
  ML d2.etype =
  match import x with
  | Some x ->
     let tree : iio t2 = reify (f x) [] (fun _ _ -> True) in
     let r : t2 = iio_interpreter tree in
     export r
  | None -> FStar.All.raise Contract_failure
