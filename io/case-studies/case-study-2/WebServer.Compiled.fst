module WebServer.Compiled

open FStar.Tactics
open FStar.All
open FStar.List.Tot

open Common
open DM
open Model
open Shared
open TC.MLify.MIIO
open WebServer

let compiled_webserver : prog_t i pi = model.compile_prog #i #pi webserver
let compiled_webserver'' : (Types.file_descr -> Tot (maybe unit)) -> ML (maybe unit) =
  (mlify #_
    #(mlifyable_iio_miio file_descr (maybe unit) (maybe unit) pi #TC.Export.ml_file_descr)
    compiled_webserver)
