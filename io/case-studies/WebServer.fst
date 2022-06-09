module WebServer

open FStar.Tactics
open ExtraTactics

open Common
open Types
open IO.Sig
open IO
open Utils

let pi : monitorable_prop = fun cmd arg h ->
  match cmd with
  | Openfile -> 
    let (fnm, _, _) : io_sig.args Openfile = arg in 
    if (fnm = "/etc/passwd") then false else true
  | _ -> true

type plugin_type =
  (x:file_descr) -> IOpi (resexn unit) pi

(** since we do not have exceptions, we have to handle errors manually **)

let rec process_connections 
  (clients : lfds) 
  (to_read : lfds) 
  (plugin : plugin_type) : 
  IOpi lfds pi =
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
  IOpi (option file_descr) pi =
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
  IOpi lfds pi =
  match static_cmd Select pi (clients, ([] <: lfds), ([] <: lfds), 100uy) with
  | Inl (to_read, _, _) ->
    let clients'' = process_connections clients to_read plugin in
    clients''
  | _ -> clients

let server_loop_body 
  (socket : file_descr) 
  (plugin : plugin_type)
  (clients : lfds) :
  IOpi lfds pi = 
  lemma_append_enforced_locally pi;
  let clients' = (match get_new_connection socket with
                 | None -> clients
                 | Some fd -> fd :: clients) in
  handle_connections clients' plugin

let rec server_loop 
  (iterations_count : nat)
  (socket : file_descr) 
  (plugin : plugin_type)
  (clients : lfds) :
  IOpi unit pi =
  lemma_append_enforced_locally pi;
  if iterations_count = 0 then ()
  else begin
    let clients' = server_loop_body socket plugin clients in
    server_loop (iterations_count - 1) socket plugin clients'
  end

let create_basic_server (ip:string) (port:UInt8.t) (limit:UInt8.t) :
  IOpi (resexn file_descr) pi by (explode ()) = 
  match static_cmd Socket pi () with
  | Inl socket -> 
    let _ = static_cmd Setsockopt pi (socket, SO_REUSEADDR, true) in 
    let _ = static_cmd Bind pi (socket, ip, port) in
    let _ = static_cmd Listen pi (socket, limit) in
    let _ = static_cmd SetNonblock pi socket in
    lemma_append_enforced_locally pi;
    Inl socket 
  | Inr err -> Inr err

let webserver 
  (plugin : plugin_type) :
  IOpi unit pi by (explode ()) =
  lemma_append_enforced_locally pi;
  match create_basic_server "0.0.0.0" 81uy 5uy with
  | Inl server -> begin
      server_loop 100000000000 server plugin []
    end
  | Inr _ -> ()
