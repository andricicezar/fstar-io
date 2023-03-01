module WebServer

open FStar.Tactics
open ExtraTactics

open Common
open Types
open IIO
open Shared
  
type plugin_type =
  (x:shr.ctx_arg) -> IIOpi (maybe shr.ctx_ret) shr.pi (shr.pre x) (shr.post x)

(** since we do not have exceptions, we have to handle errors manually **)

let rec process_connections 
  (clients : lfds) 
  (to_read : lfds) 
  (plugin : plugin_type) : 
  IIOpi lfds pi =
  match clients with
  | [] -> []
  | client :: tail -> begin
    let rest = process_connections tail to_read (plugin) in
    if List.mem client to_read then begin
      let _ = plugin client in 
      let _ = static_cmd Close pi client in
      lemma_append_enforced_locally pi;
      tail 
    end else clients
  end
 
let get_new_connection (socket : file_descr) :
  IOpi (option file_descr) shr.pi
    (requires (fun _ -> True))
    (ensures (fun _ _ _ -> True)) =
  match static_cmd Select pi (([socket] <: lfds), ([] <: lfds), ([] <: lfds), 100uy) with
  | Inl (to_accept, _, _) ->
    if List.length to_accept > 0 then begin 
      match static_cmd Accept pi socket with
      | Inl client -> 
        let _ = static_cmd SetNonblock pi client in
        Some client
      | _ -> None
    end else None
  | _ -> None

let handle_connections
  (clients:lfds)
  (plugin : plugin_type) :
  IIOpi lfds shr.pi 
    (requires (fun _ -> True))
    (ensures (fun _ _ _ -> True)) =
  match static_cmd Select pi (clients, ([] <: lfds), ([] <: lfds), 100uy) with
  | Inl (to_read, _, _) ->
    let clients'' = process_connections clients to_read plugin in
    clients''
  | _ -> clients

let server_loop_body 
  (socket : file_descr) 
  (plugin : plugin_type)
  (clients : lfds) :
  IIOpi lfds shr.pi
    (requires (fun h -> True)) 
    (ensures (fun h r lt -> True)) = 
  lemma_append_enforced_locally shr.pi;
  let clients' = (match get_new_connection socket with
                 | None -> clients
                 | Some fd -> fd :: clients) in
  handle_connections clients' plugin

let rec server_loop 
  (iterations_count : nat)
  (socket : file_descr) 
  (plugin : plugin_type)
  (clients : lfds) :
  IIOpi unit shr.pi
    (requires (fun h -> True))
    (ensures (fun h r lt -> True)) =
  lemma_append_enforced_locally shr.pi;
  if iterations_count = 0 then ()
  else begin
    let clients' = server_loop_body socket plugin clients in
    server_loop (iterations_count - 1) socket plugin clients'
  end

let create_basic_server (ip:string) (port:UInt8.t) (limit:UInt8.t) :
  IOpi (maybe file_descr) shr.pi
    (requires (fun h -> True))
    (ensures (fun h r lt ->
      match r with
      | Inl socket -> is_open socket (apply_changes h lt)
      | _ -> True)) by (explode ()) = 
  match static_cmd Socket pi () with
  | Inl socket -> 
    let _ = static_cmd Setsockopt pi (socket, SO_REUSEADDR, true) in 
    let _ = static_cmd Bind pi (socket, ip, port) in
    let _ = static_cmd Listen pi (socket, limit) in
    let _ = static_cmd SetNonblock pi socket in
    lemma_append_enforced_locally shr.pi;
    Inl socket 
  | Inr err -> Inr err

let webserver 
  (plugin : plugin_type) :
  IIOpi shr.ret shr.pi
    (requires (fun h -> True))
    (ensures (fun h r lt -> True)) by (explode ()) =
  lemma_append_enforced_locally shr.pi;
  match create_basic_server "0.0.0.0" 81uy 5uy with
  | Inl server -> begin
      server_loop 100000000000 server plugin []
    end
  | Inr _ -> ()
