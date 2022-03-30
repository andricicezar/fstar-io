module WebServer.Compiled

open FStar.Tactics
open FStar.All
open FStar.List.Tot

open Common
open DM
open Shared
open TC.Export
open WebServer

(** TODO: can these two steps be combined? **)
val compiled_webserver : plugin_type -> IIOwp (maybe unit) (trivial_hist ())
let compiled_webserver = 
  simpl_trivialize
    (fun _ _ -> true)
    (fun _ h r lt -> iio_post shr.pi h r lt)
    webserver

let webserver_mlify = 
  mlifyable_inst_iiowp
    plugin_type 
    (maybe unit)
    #(instrumentable_IIO #shr.ctx_arg #shr.ctx_ret #ml_file_descr shr.pre shr.post shr.pi #shr.post_c) 
    #(ml_maybe unit)

let compiled_webserver'' : (Types.file_descr -> Tot (maybe unit)) -> ML (maybe unit) =
  (mlify #_
    #webserver_mlify
    compiled_webserver)
