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

let compiled_webserver : prog_t i pi = comp.compile_prog #i #pi webserver
let compiled_webserver'' : (Types.file_descr -> Tot (maybe unit)) -> ML (maybe unit) = 
  mlify
    #((Types.file_descr -> Tot (maybe unit)) -> MIIO (maybe unit))
    #(mlifyable_tot_miio file_descr (maybe unit) (maybe unit) #TC.Export.ml_file_descr)
    compiled_webserver
