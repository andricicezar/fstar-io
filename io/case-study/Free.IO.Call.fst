module Free.IO.Call

open Free
open Free.IO

let io_call (cmd:io_cmds) (arg:io_args cmd) : io (io_resm cmd) =
  Call cmd arg Return

let iio_call (cmd:inst_cmds) (arg:args cmd) : iio (res cmd) =
  Call cmd arg Return
