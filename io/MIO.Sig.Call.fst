module MIO.Sig.Call

open MIO.Sig

assume val print_string2 : string -> Tot bool

(** This file is replaced during linking with a file that contains the real
implementation of the commands. **)
let mio_call (c:caller) (cmd:cmds) (arg:mio_sig.args cmd) : mio (mio_sig.res cmd arg) =
  Call c cmd arg Return
