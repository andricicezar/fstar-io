module IUnix

open FStar.All

include Types
open Common
open Free.IO 
open DM.IIO.Primitives
open DM.MIIO
open TC.Export
open TC.Weaken.MIIO
open TC.MLify.MIIO
open Shared

let lift_error (x:maybe (maybe 'a)) : ML 'a =
  match x with
  | Inl (Inl y) -> y
  | Inl (Inr err) -> raise err
  | Inr err -> raise err

val miio_cmd : (cmd:io_cmds) -> args cmd -> MIIO (maybe (io_resm cmd))
let miio_cmd cmd argz = dynamic_cmd cmd pi argz

val openfile : string -> (list open_flag) -> zfile_perm -> ML file_descr
let openfile x y z = 
  lift_error (
    (mlify #_ #(mlifyable_miio _ _ #(ml_pair_2 _ _ _))
      (miio_cmd Openfile))
      (x,y,z))

val read : file_descr -> UInt8.t -> ML (Bytes.bytes * UInt8.t)
let read x y = 
  lift_error (
    (mlify #_ #(mlifyable_miio _ _ #(ml_pair _ _))
      (miio_cmd Read))
      (x,y))

val write : file_descr -> Bytes.bytes -> ML unit 
let write x y = 
  lift_error (
    (mlify #_ #(mlifyable_miio _ _ #(ml_pair _ _))
      (miio_cmd Write))
      (x,y))

val close : file_descr -> ML unit 
let close x = 
  lift_error (
    (mlify #_ #(mlifyable_miio _ _)
      (miio_cmd Close))
      x)

val socket : unit -> ML file_descr
let socket x = 
  lift_error (
    (mlify #_ #(mlifyable_miio _ _)
      (miio_cmd Socket))
      x)

val set_sock_opt : file_descr -> socket_bool_option -> bool -> ML unit
let set_sock_opt x y z = 
  lift_error (
    (mlify #_ #(mlifyable_miio _ _ #(ml_pair_2 _ _ _))
      (miio_cmd Setsockopt))
      (x,y,z))

val bind : file_descr -> string -> UInt8.t -> ML unit
let bind x y z = 
  lift_error (
    (mlify #_ #(mlifyable_miio _ _ #(ml_pair_2 _ _ _))
      (miio_cmd Bind))
      (x,y,z))

val set_nonblock : file_descr -> ML unit 
let set_nonblock x = 
  lift_error (
    (mlify #_ #(mlifyable_miio _ _)
      (miio_cmd SetNonblock))
      x)

val listen : file_descr -> UInt8.t -> ML unit 
let listen x y = 
  lift_error (
    (mlify #_ #(mlifyable_miio _ _ #(ml_pair _ _))
      (miio_cmd Listen))
      (x,y))

val accept : file_descr -> ML file_descr
let accept x = 
  lift_error (
    (mlify #_ #(mlifyable_miio _ _)
      (miio_cmd Accept))
      x)

val select : lfds -> lfds -> lfds -> UInt8.t -> ML (lfds * lfds * lfds)
let select x y z w = 
  lift_error (
    (mlify #_ #(mlifyable_miio _ _ #(ml_pair_3 _ _ _ _))
      (miio_cmd Select))
      (x,y,z,w))
