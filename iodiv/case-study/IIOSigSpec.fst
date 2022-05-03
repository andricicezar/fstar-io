module IIOSigSpec

open FStar.List.Tot
open FStar.List.Tot.Properties
open FStar.Tactics // Also defines forall_intro so place before Classical
open FStar.Classical
open FStar.IndefiniteDescription
open FStar.Calc
open FStar.FunctionalExtensionality

open Util
open Stream
open IIOSig
open DivFree
open DivFreeTauSpec
open DivFreeTauDM

unfold
let i_get_trace : iwp history =
  as_iwp (fun post hist -> post (Ocv [] hist))

let convert_call_to_event
  (cmd:io_sig.act)
  (arg:io_sig.arg cmd)
  (r:io_sig.res arg) =
  match cmd with
  | Openfile -> EOpenfile arg r
  | Read     -> ERead arg r
  | Write -> EWrite arg r
  | Close -> EClose arg r
  | Socket -> ESocket arg r
  | Setsockopt -> ESetsockopt arg r
  | Bind -> EBind arg r
  | SetNonblock -> ESetNonblock arg r
  | Listen -> EListen arg r
  | Accept -> EAccept arg r
  | Select -> ESelect arg r

unfold
let iodiv_act : action_iwp io_sig =
  fun ac arg ->
    as_iwp (fun post hist -> forall res. post (Ocv [ Some (convert_call_to_event ac arg res) ] res))

let iiodiv_act : action_iwp iio_sig =
  fun ac arg ->
    match ac with
    | GetTrace -> i_get_trace
    | _ -> iodiv_act ac arg 
