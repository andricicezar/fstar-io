module WebServer.Compiled

open FStar.Tactics
open FStar.All

open Common
open DM
open Model
open Shared
open TC.MLify.MIIO
open WebServer
  
let lift_tot_to_IIO
  (#i:interface)
  (#pi:monitorable_prop)
  (f:i.ctx_arg -> Tot (maybe i.ctx_ret))
  (x:i.ctx_arg) :
  IIO (maybe i.ctx_ret) pi (fun _ -> True) (i.ctx_post x) by (DM.IIO.Tactics.iio_tactic (); dump "H") =
  let r = f x in
  assume (forall h lt. i.ctx_post x h r lt);
  r

let compiled_webserver : prog_t i pi = comp.compile_prog #i #pi webserver
val compiled_webserver' : (file_descr -> Tot (maybe unit)) -> MIIO (maybe unit)
let compiled_webserver' f = compiled_webserver (lift_tot_to_IIO #i #pi f)

let compiled_webserver'' : (Types.file_descr -> Tot (maybe unit)) -> ML (maybe unit) = 
  mlify
    #((Types.file_descr -> Tot (maybe unit)) -> MIIO (maybe unit))
    #(mlifyable_tot_miio file_descr (maybe unit) (maybe unit) #TC.Export.ml_file_descr)
    compiled_webserver'
