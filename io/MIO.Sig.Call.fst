module MIO.Sig.Call

open MIO.Sig

(** This file is replaced during linking with a file that contains the real
implementation of the commands. **)
let mio_call (caller:bool) (cmd:cmds) (arg:mio_sig.args cmd) : mio (mio_sig.res cmd arg) =
  Call caller cmd arg Return
