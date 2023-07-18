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


[@@ (postprocess_with (pp_unfold [ `%iprepost ]))]
unfold let i_open (s : string) : iwp file_descr =
  iprepost (fun _ -> True) (fun hist r -> terminates r /\ ret_trace r == [ EOpenfile s (result r) ])

[@@ (postprocess_with (pp_unfold [ `%iprepost ]))]
unfold let i_read (fd : file_descr) : iwp string =
  iprepost (fun hist -> is_open fd hist) (fun hist r -> terminates r /\ ret_trace r == [ ERead fd (result r) ])

[@@ (postprocess_with (pp_unfold [ `%iprepost ]))]
unfold let i_print (s : string) : iwp unit =
  iprepost (fun hist -> True) (fun hist r -> terminates r /\ ret_trace r == [ EPrint s ])

[@@ (postprocess_with (pp_unfold [ `%iprepost ]))]
unfold let i_close (fd : file_descr) : iwp unit =
  iprepost (fun hist -> is_open fd hist) (fun hist r -> terminates r /\ ret_trace r == [ EClose fd ])

unfold
let i_get_trace : iwp history =
  as_iwp (fun post hist -> post (Cv [] hist))

unfold
let i_act : action_iwp io_sig =
  fun ac arg ->
    match ac with
    | Openfile -> i_open arg
    | Read -> i_read arg
    | Print -> i_print arg
    | Close -> i_close arg

let i_iio_call : action_iwp iio_sig =
  fun ac arg ->
    match ac with
    | GetTrace -> i_get_trace
    | _ -> i_act ac arg
