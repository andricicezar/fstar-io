module WebServer

open FStar.Tactics
open FStar.Ghost
open ExtraTactics

open FStar.List.Tot.Base
open FStar.List.Tot.Properties

open Compiler.Model1
open Utils

type req_handler =
  (client:file_descr) ->
  (req:Bytes.bytes) ->
  (send:(res:Bytes.bytes -> MIO (resexn unit) (requires (fun h -> did_not_respond h /\ valid_http_response res))
                                             (ensures (fun h _ lt -> exists r. lt == [EWrite Prog (client,res) r])))) ->
  MIO (resexn unit)
    (requires (fun h -> valid_http_request req /\ did_not_respond h))
    (ensures (fun h r lt -> enforced_locally sgm h lt /\
                          (wrote_to client (rev lt) \/ Inr? r)))

let static_op
  (op : io_ops)
  (arg : io_sig.args op) :
  MIO (io_sig.res op arg)
    (requires (fun h -> io_pre op arg h))
    (ensures (fun h (r:io_sig.res op arg) lt ->
        io_post op arg r /\
        lt == [convert_call_to_event Prog op arg r])) =
  static_op Prog op arg

#push-options "--compat_pre_core 1"
let sendError400 (fd:file_descr) : MIO unit
 (fun _ -> True) (fun _ _ lt -> exists res r. lt == [EWrite Prog (fd, res) r]) =
  let _ = static_op Write (fd,(Bytes.utf8_encode "HTTP/1.1 400\n")) in
  ()

let get_req (fd:file_descr) :
  MIO (resexn (r:Bytes.bytes{valid_http_request r})) (fun _ -> True) (fun _ _ lt -> exists r'. lt == [ERead Prog (fd, (UInt8.uint_to_t 255)) r']) =
  match static_op Read (fd, UInt8.uint_to_t 255) with
  | Inl (msg, _) ->
   Inl msg
  | Inr err -> Inr err

let process_connection
  (client : file_descr)
  (req_handler : req_handler) :
  MIO unit (fun _ -> True)
    (fun _ _ lt -> every_request_gets_a_response lt) =
  match get_req client with
  | Inr _ -> sendError400 client
  | Inl req ->
    begin match req_handler client req (fun res -> let _ = static_op Write (client,res) in Inl ()) with
    | Inr err -> sendError400 client
    | Inl client -> ()
    end

let rec process_connections
  (clients : lfds)
  (to_read : lfds)
  (req_handler : req_handler) :
  MIO lfds (fun _ -> True) (fun _ _ lt -> every_request_gets_a_response lt) =
  match clients with
  | [] -> []
  | client :: tail ->
    begin
      let rest = process_connections tail to_read req_handler in
      if mem client to_read then begin
        let p = async (fun () -> process_connection client req_handler; static_op Close client) in
        rest
      end else (client::rest)
    end

let get_new_connection (socket : file_descr) :
  MIO (option file_descr) (fun _ -> True)
    (fun _ _ lt -> every_request_gets_a_response lt) = (** TODO: can one verify that every socket that connects is accepted and processed? **)
  match static_op Select ([socket], [], [], 100uy) with
  | Inl (to_accept, _, _) ->
    if length to_accept > 0 then begin
      match static_op Accept socket with
      | Inl client ->
        let _ = static_op SetNonblock client in
        Some client
      | _ -> None
    end else None
  | _ -> None

let handle_connections
  (clients:lfds)
  (req_handler : req_handler) :
  MIO lfds (fun _ -> True)
    (fun _ _ lt -> every_request_gets_a_response lt) =
  match static_op Select (clients, [], [], 100uy) with
  | Inl (to_read, _, _) ->
    let clients'' = process_connections clients to_read req_handler in
    clients''
  | _ -> clients

let server_loop_body
  (socket : file_descr)
  (req_handler : req_handler)
  (clients : lfds) :
  MIO lfds (fun _ -> True)
    (fun _ _ lt -> every_request_gets_a_response lt) =
  (** To do something fancy here, one would need a non-blocking `await` as `state` of promises in JavaScript.
      Then, one could in parallel accept and handle connections, and manually syncronise promises **)
  let clients' = (match get_new_connection socket with
                 | None -> clients
                 | Some fd -> fd :: clients) in
  handle_connections clients' req_handler

let rec server_loop
  (iterations_count : nat)
  (socket : file_descr)
  (req_handler : req_handler)
  (clients : lfds) :
  MIO unit (fun _ -> True)
    (fun _ _ lt -> every_request_gets_a_response lt) =
  if iterations_count = 0 then ()
  else begin
    let clients' = server_loop_body socket req_handler clients in
    server_loop (iterations_count - 1) socket req_handler clients'
  end

let create_basic_server (ip:string) (port:UInt8.t) (limit:UInt8.t) :
  MIO (resexn file_descr) (fun _ -> True)
    (fun _ _ lt -> every_request_gets_a_response lt) =
  match static_op Socket () with
  | Inl socket ->
    let _ = static_op Setsockopt (socket, SO_REUSEADDR, true) in
    let _ = static_op Bind (socket, ip, port) in
    let _ = static_op Listen (socket, limit) in
    let _ = static_op SetNonblock socket in
    Inl socket
  | Inr err -> Inr err

let webserver
  (req_handler : req_handler)
  () :
  MIO int
    (requires (fun h -> True))
    (ensures (fun h r lt -> every_request_gets_a_response lt)) =
  match create_basic_server "0.0.0.0" 81uy 5uy with
  | Inl server -> begin
      server_loop 100000000000 server req_handler [] ;
      0
    end
  | Inr _ -> -1
