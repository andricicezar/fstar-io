module Free.IO.Call

open Free
open Free.IO.Sig

(** This file is replaced during linking with a file that contains the real
implementation of the commands. **)
let io_call (cmd:io_cmds) (arg:io_sig.args cmd) : io (io_sig.res cmd arg) =
  Call cmd arg Return

(** Since we can lift from io to iio, `iio_call` should be used only for 
`GetTrace`. **)
let iio_call (cmd:cmds) (arg:iio_sig.args cmd) : iio (iio_sig.res cmd arg) =
  Call cmd arg Return
