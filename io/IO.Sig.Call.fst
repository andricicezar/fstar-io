module IO.Sig.Call

open IO.Sig

(** This file is replaced during linking with a file that contains the real
implementation of the commands. **)
let io_call (cmd:io_cmds) (arg:io_sig.args cmd) : io (io_sig.res cmd arg) =
  Call cmd arg Return

let iio_call (cmd:cmds) (arg:iio_sig.args cmd) : iio (iio_sig.res cmd arg) =
  Call cmd arg Return
