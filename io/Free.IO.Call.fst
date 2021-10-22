module Free.IO.Call

open Free
open Free.IO

(** This file is replaced during linking with a file that contains the real
implementation of the commands. **)
let io_call (cmd:io_cmds) (arg:io_args cmd) : io (io_resm cmd) =
  Call cmd arg Return

(** Since we can lift from io to iio, `iio_call` should be used only for 
`GetTrace`. **)
let iio_call (cmd:inst_cmds) (arg:args cmd) : iio (res cmd) =
  Call cmd arg Return
