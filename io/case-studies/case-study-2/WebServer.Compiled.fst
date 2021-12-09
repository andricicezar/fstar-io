module WebServer.Compiled

open FStar.Tactics
open FStar.All
open FStar.List.Tot

open Common
open DM
open Model
open Shared
open TC.Export
open TC.MLify.MIIO
open TC.Instrumentable.IIO
open WebServer

(** TODO: can these two steps be combined? **)
val compiled_webserver : (x:Types.file_descr -> IIO (maybe unit) (m.pi) (m.pre x) (m.post x)) -> MIIO (maybe unit)
let compiled_webserver = 
  _IIOwp_as_MIIO
    (fun _ _ -> true)
    (fun _ h r lt -> iio_post m.pi h r lt)
    webserver

let webserver_mlify = 
  mlifyable_inst_miio
    (x:file_descr -> IIO (maybe unit) (m.pi) (m.pre x) (m.post x))
    (maybe unit)
    #(instrumentable_IIO #Types.file_descr #unit #ml_file_descr m.pre m.post m.pi #m.post_c) 
    #(ml_maybe unit)

let compiled_webserver'' : (Types.file_descr -> Tot (maybe unit)) -> ML (maybe unit) =
  (mlify #_
    #webserver_mlify
    compiled_webserver)
