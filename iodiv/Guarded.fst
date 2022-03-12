module Guarded

open FStar.List.Tot
open FStar.List.Tot.Properties
open FStar.Classical
open FStar.IndefiniteDescription
open FStar.Calc
open FStar.FunctionalExtensionality
open Util

(** Partiality monad *)

let guarded (a : Type) : Type =
  pre : Type0 & (squash pre -> a)

let gmk #a (pre : Type0) (f : squash pre -> a) : guarded a =
  (| pre , f |)

let g_ret #a (x : a) : guarded a =
  gmk True (fun _ -> x)

let g_pre #a (c : guarded a) : Type0 =
  let (| pre , f |) = c in pre

let g_val #a (c : guarded a) : Pure a (requires g_pre c) (ensures fun r -> True) =
  let (| pre, f |) = c in f ()

let g_bind #a #b (c : guarded a) (f : a -> guarded b) : guarded b =
  gmk (g_pre c /\ (forall (x : a). g_pre (f x))) (fun _ ->
    g_val (f (g_val c))
  )

let g_req (pre : Type0) : guarded (squash pre) =
  gmk pre (fun h -> h)

let g_reqk #a (pre : Type0) (k : squash pre -> guarded a) : guarded a =
  g_bind (g_req pre) k
