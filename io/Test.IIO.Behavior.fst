module Test.IIO.Behavior

open Free.IO
open IIO.Behavior

let prog1 : iio int =
  Return 5

let _ = assert (behavior prog1 ([], 5))

[@expect_failure]
let _ = assert (behavior prog1 ([], 7))

let prog2 : iio trace =
  Call GetTrace () (fun h -> Return h)

open FStar.Tactics

let empty_trace : trace = []

let _ = assert (behavior prog2 ([], []))
  by (
    compute ();
    witness (`empty_trace))

let prog3 : iio trace =
  Call Openfile "../Makefile" (fun _ -> prog2)

let _ = assert (
  forall r'. behavior prog3 ([EOpenfile "../Makefile" r'],
                        [EOpenfile "../Makefile" r'])) by (
  compute ())

let prog4 : iio (io_resm Openfile) =
  Call Openfile "../Makefile" Return

let _ = assert (
  forall r'.
    behavior prog4 ([EOpenfile "../Makefile" r'], r')) by (
  compute ())
