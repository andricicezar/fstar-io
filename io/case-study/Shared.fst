module Shared

open FStar.Tactics

open Common
open Free.IO
open Checkable
open Model

let rec is_open (fd:file_descr) (h: trace) : Tot bool =
  match h with
  | [] -> false
  | h :: tail -> match h with
               | EOpenfile _ (Inl fd') ->
                   if fd = fd' then true
                   else is_open fd tail
               | ESocket _ (Inl fd') ->
                   if fd = fd' then true
                   else is_open fd tail
               | EClose fd' _ ->
                    if fd = fd' then false
                    else is_open fd tail
               | _ -> is_open fd tail

let ctx_post : file_descr -> trace -> maybe unit -> trace -> Tot bool = 
  fun fd h r lt -> is_open fd (apply_changes h lt)

let i : comp.interface = {
  ctx_arg = file_descr;
  ctx_ret = unit;
  ctx_post = (fun fd h r lt -> ctx_post fd h r lt);
  ctx_post_c = general_is_checkable4 file_descr trace (maybe unit) trace ctx_post;
  ret = unit;
}
  
val pi : monitorable_prop
let pi h action =
  match action with
  | (| Openfile, arg |) -> 
    let (fnm, _, _) : io_args Openfile = arg in not (fnm = "/etc/passwd")
  | _ -> true

(** The following pi is too hardcore for our current state. 
    This pi implies to have pre-/post- conditions that keep track of what
    file descriptors are open or not. But, the plugin can close some of those
    file descriptors and we can not prevent this bad behavior. **)
val pi' : monitorable_prop
let pi' h action =
  match action with
  | (| Openfile, _ |) -> true
  | (| Read, arg |) -> 
    let (fd, _) : io_args Read = arg in is_open fd h

  | (| Write, arg |) -> 
    let (fd, _) : io_args Write = arg in is_open fd h

  | (| Close, fd |) -> is_open fd h
  | (| Socket, _ |) -> true
  | (| Setsockopt, arg |) ->
    let (fd, _, _) : io_args Setsockopt = arg in is_open fd h
  
  | (| Bind, arg |) ->
    let (fd, _, _) : io_args Bind = arg in is_open fd h

  | (| SetNonblock, fd |) -> is_open fd h
  | (| Listen, arg |) ->
    let (fd, _) : io_args Listen = arg in is_open fd h
  
  | (| Accept, fd |) -> is_open fd h
  | (| Select, _ |) -> true
