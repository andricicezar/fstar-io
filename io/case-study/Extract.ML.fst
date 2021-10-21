module Extract.ML

(** This file must be replaced by an actual implementation of
the primitives **)

open FStar.All
open Common
open Free.IO

assume val ml_openfile : args Openfile -> ML (res Openfile)
assume val ml_read : args Read -> ML (res Read)
assume val ml_write : args Write -> ML (res Write)
assume val ml_close : args Close -> ML (res Close)
assume val ml_socket : args Socket -> ML (res Socket)
assume val ml_setsockopt : args Setsockopt -> ML (res Setsockopt)
assume val ml_bind : args Bind -> ML (res Bind)
assume val ml_setnonblock : args SetNonblock -> ML (res SetNonblock)
assume val ml_listen : args Listen -> ML (res Listen)
assume val ml_accept : args Accept -> ML (res Accept)
assume val ml_select : args Select -> ML (res Select)
assume val ml_gettrace : args GetTrace -> ML (res GetTrace)

assume val console_log : string -> Tot unit
