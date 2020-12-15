module Test.Minterop

open Common
open IO.Free
open IO.Effect
open IIO.Effect
open MIO.Effect
open Minterop

val allowed_file : string -> bool
let allowed_file fnm = match fnm with
  | "../Makefile" -> false
  | "Demos.fst" -> true
  | _ -> false

val allowed_fd : file_descr -> trace -> bool
let rec allowed_fd fd s0 =
  match s0 with
  | [] -> false
  | EOpenfile fnm (Inl fd') :: t -> if fd = fd' then allowed_file(fnm)
                                  else allowed_fd fd t
  | EClose fd' _  :: t -> if fd = fd' then false else allowed_fd fd t
  | _ :: t -> allowed_fd fd t

let pi : monitorable_prop = (fun s0 action -> 
  match action with
  | (| Openfile, fnm |) -> allowed_file(fnm)
  | (| Read, fd |) -> allowed_fd fd s0
  | (| Close, fd |) -> allowed_fd fd s0)

// the plugin will be written in GIO (should be ML?)
let plugin_type = (pi:monitorable_prop) -> file_descr -> IIO unit pi (fun _ -> True) (fun _ _ _ -> True)

// import plugin_type 
let webserver (plugin:plugin_type) : IIO unit pi (fun _ -> True) (fun _ _ _ -> True) =
  rev_append_rev_append ();
  let fd = static_cmd pi Openfile "Demos.fst" in
  plugin pi fd

let ml_plugin1 : file_descr -> MIO unit = fun fd ->
  unsafe_cmd Close fd

val pre : file_descr -> trace -> Type0
let pre = (fun _ _ -> true)
val post : file_descr -> trace -> maybe unit -> trace -> Type0
let post = (fun _ _ _ _ -> true)

(** TODO: Why is this failing? Seems similar with the problem of
incr' in the Minterop file. **)
val plugin1 : x:file_descr -> IIO unit pi (pre x) (post x)
// let plugin1 = safe_import ml_plugin1
