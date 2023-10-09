module MIO.Sig.Call

open MIO.Sig

(** This is used only for debugging code when running it **)
assume val print_string2 : string -> Tot bool

(** This file is replaced during linking with a file that contains the real
implementation of the commands. **)

let mio_call (#mst:mstate) caller (op:mio_ops) (arg:(mio_sig mst).args op) : mio mst ((mio_sig mst).res op arg) =
  Call caller op arg Return
