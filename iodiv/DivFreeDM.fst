(** Partial Dijkstra monad definition on top of DivFree *)

module DivFreeDM

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
open DivFreeSpec

type action_wp (sg : signature) =
  ac : sg.act -> x : sg.arg ac -> wp (sg.res x)

let rec theta (#a : Type u#a) #sg (w_act : action_wp sg) (c : m sg a) : wp a =
  match c with
  | Ret x -> w_ret x
  | Req pre k -> w_bind (w_req pre) (fun x -> theta w_act (k x))
  | Iter index b f i k -> w_bind (w_iter u#a (fun j -> theta w_act (f j)) i) (fun x -> theta w_act (k x))
  | Call ac x k -> w_bind (w_act ac x) (fun x -> theta w_act (k x))
