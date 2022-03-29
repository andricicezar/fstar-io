module WebServer.Compiled

open FStar.Tactics
open FStar.All
open FStar.List.Tot

open Common
open DM
open Shared
open TC.Export
open WebServer
open Utils

(** TODO: can these two steps be combined? **)
val compiled_webserver : (x:Types.file_descr -> IIOpi (maybe unit) (shr.pi) (shr.pre x) (shr.post x)) -> IIOwp (maybe unit) (trivial_hist ())
let compiled_webserver = 
  _IIOwp_as_MIIO
    (fun _ _ -> true)
    (fun _ h r lt -> iio_post shr.pi h r lt)
    webserver

let webserver_mlify = 
  mlifyable_inst_iiowp
    (x:file_descr -> IIOpi (maybe unit) (shr.pi) (shr.pre x) (shr.post x))
    (maybe unit)
    #(instrumentable_IIO #Types.file_descr #unit #ml_file_descr shr.pre shr.post shr.pi #shr.post_c) 
    #(ml_maybe unit)

let compiled_webserver'' : (Types.file_descr -> Tot (maybe unit)) -> ML (maybe unit) =
  (mlify #_
    #webserver_mlify
    compiled_webserver)
