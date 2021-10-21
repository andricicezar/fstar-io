module Extract.ML

(** This file must be replaced by an actual implementation of
the primitives **)

open FStar.All
open Common
open Free.IO

assume val ml_io_cmd : (cmd:io_cmds) -> args cmd -> ML (res cmd)
assume val ml_gettrace : args GetTrace -> ML (res GetTrace)
