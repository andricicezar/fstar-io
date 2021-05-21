module Extract.ML

(** This file must be replaced by an actual implementation of
the primitives **)

open FStar.All
open Common
open Free.IO

assume val ml_gettrace : args GetTrace -> ML (res GetTrace)
assume val ml_openfile : args Openfile -> ML (io_res Openfile)
assume val ml_read : args Read -> ML (io_res Read)
assume val ml_close : args Close -> ML (io_res Close)

