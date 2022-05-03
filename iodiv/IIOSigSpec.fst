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
let i_open (s : string) : iwp file_descr =
  as_iwp (fun post hist -> forall fd. post (Ocv [ Some (EOpenfile s fd) ] fd))

unfold
let i_read (fd : file_descr) : iwp string =
  as_iwp (fun post hist -> is_open fd hist /\ (forall s. post (Ocv [ Some (ERead fd s) ] s)))

unfold
let i_close (fd : file_descr) : iwp unit =
  as_iwp (fun post hist -> is_open fd hist /\ (post (Ocv [ Some (EClose fd) ] ())))

unfold
let i_get_trace : iwp history =
  as_iwp (fun post hist -> post (Ocv [] hist))

unfold
let iodiv_act : action_iwp io_sig =
  fun ac arg ->
    match ac with
    | Openfile -> i_open arg
    | Read -> i_read arg
    | Close -> i_close arg
