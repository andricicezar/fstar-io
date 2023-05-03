module MIO.Sig.Call

open MIO.Sig

assume val print_string2 : string -> Tot bool

(** This file is replaced during linking with a file that contains the real
implementation of the commands. **)
let mio_call (#mst:mst) (caller:bool) (cmd:cmds) (arg:(mio_sig mst).args cmd) : mio mst ((mio_sig mst).res cmd arg) =
  Call caller cmd arg Return
