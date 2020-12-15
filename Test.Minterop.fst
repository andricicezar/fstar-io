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

let plugin1 : file_descr -> MIO unit = fun fd ->
  unsafe_cmd Close fd

(** TODO: Why is this failing? **)
val safe_plugin1 : file_descr -> IIO unit pi (fun _ -> true) (fun _ _ _ -> true)
let safe_plugin1 = safe_import plugin1
