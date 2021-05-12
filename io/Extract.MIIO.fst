module Extract.MIIO

open FStar.All
open Common
open DM
open Extract.ML

val ml_io_cmds : (cmd:io_cmds) -> args cmd -> ML (io_res cmd)
let ml_io_cmds cmd args =
  match cmd with
  | Openfile -> ml_openfile args
  | Read -> ml_read args
  | Close -> ml_close args

val ml_io_all : (cmd:io_cmds) -> args cmd -> ML (io_resm cmd)
let ml_io_all cmd args =
  try_with
    (fun _ -> (Inl (ml_io_cmds cmd args)) <: io_resm cmd)
    (fun err -> (Inr err) <: io_resm cmd)

val ml_io_execute : (cmd:cmds) -> args cmd -> ML (res cmd)
let ml_io_execute cmd argz =
  match cmd with
  | GetTrace -> ml_gettrace argz
  | _ -> ml_io_all cmd argz

let rec iio_interpreter #t1 (t:iio t1) : ML t1 =
  match t with
  | Return (Inl r) -> r
  | Return (Inr r) -> FStar.All.raise r
  | Call cmd argz fnc ->
      iio_interpreter #t1 (fnc (ml_io_execute cmd argz))

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
