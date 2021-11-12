module WebServer

open FStar.Tactics
open ExtraTactics
open DM.IIO.Tactics

open Common
open Types
open DM
open Model
open Shared

type plugin_type = ctx_s i m

(** since we do not have exceptions, we have to handle errors manually **)

let rec process_connections 
  (clients : lfds) 
  (to_read : lfds) 
  (plugin : plugin_type) : 
  IIO lfds pi
    (requires (fun _ -> True))
    (ensures (fun _ _ _ -> True)) by (
    explode (); bump_nth 34; iio_tactic ()) =
  match clients with
  | [] -> []
  | client :: tail -> begin
    let rest = process_connections tail to_read (plugin) in
    if List.mem client to_read then begin
      let _ = plugin client in 
      let _ = static_cmd Close pi client in
      tail 
    end else clients
  end
 
let get_new_connection (socket : file_descr) :
  IO (option file_descr) m.pi
    (requires (fun _ -> True))
    (ensures (fun _ _ _ -> True )) =
  match static_cmd Select pi ([socket], [], [], 100uy) with
  | Inl (to_accept, _, _) ->
    if FStar.List.length to_accept > 0 then begin 
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
  IIO lfds m.pi 
    (requires (fun _ -> True))
    (ensures (fun _ _ _ -> True)) by (iio_tactic ()) =
  match static_cmd Select pi (clients, [], [], 100uy) with
  | Inl (to_read, _, _) ->
    let clients'' = process_connections clients to_read plugin in
    clients''
  | _ -> clients

let server_loop_body 
  (socket : file_descr) 
  (plugin : plugin_type)
  (clients : lfds) :
  IIO lfds m.pi
    (requires (fun h -> True)) 
    (ensures (fun h r lt -> True)) by (iio_tactic ()) = 
  let clients' = (match get_new_connection socket with
                 | None -> clients
                 | Some fd -> fd :: clients) in
  handle_connections clients' plugin

let rec server_loop 
  (iterations_count : nat)
  (socket : file_descr) 
  (plugin : plugin_type)
  (clients : lfds) :
  IIO unit m.pi
    (requires (fun h -> True))
    (ensures (fun h r lt -> True)) by (explode (); bump_nth 18; iio_tactic ()) =
  if iterations_count = 0 then ()
  else begin
    let clients' = server_loop_body socket plugin clients in
    server_loop (iterations_count - 1) socket plugin clients'
  end

let create_basic_server (ip:string) (port:UInt8.t) (limit:UInt8.t) :
  IO (maybe file_descr) m.pi
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
    Inl socket 
  | Inr err -> Inr err

let webserver 
  (plugin : plugin_type) :
  IIO i.ret m.pi
    (requires (fun h -> True))
    (ensures (fun h r lt -> True)) by (explode (); bump_nth 11; iio_tactic ()) =
  match create_basic_server "0.0.0.0" 81uy 5uy with
  | Inl server -> begin
      server_loop 100000000000 server plugin []
    end
  | Inr _ -> ()
