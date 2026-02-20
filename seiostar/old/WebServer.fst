module WebServer

open FStar.List.Tot.Base
open FStar.List.Tot.Properties

open IO

type resexn a = either a exn
type file_descr = int
type lfds = list file_descr

assume val read : file_descr * UInt8.t -> io (resexn (Bytes.bytes * UInt8.t))
assume val write : file_descr * Bytes.bytes -> io (resexn unit)
assume val close : file_descr -> io (resexn unit)
assume val select : (lfds * lfds * lfds * UInt8.t) -> io (resexn (lfds * lfds * lfds))
assume val accept : file_descr -> io (resexn file_descr)
assume val set_non_block : file_descr -> io (resexn unit)
assume val socket : unit -> io (resexn file_descr)

type req_handler = file_descr -> Bytes.bytes -> (Bytes.bytes -> io (resexn unit)) -> io (resexn unit)

(** TODO to be able to quote the Web Server:
- [ ] support for either
- [ ] support for gazillion data types
  - [ ] How to encode Bytes.utf8_encode. Are we going to treat it like a symbol? How?
  - [ ] Similar for UInt8
  - [ ] file_descr, list of file descriptors
  - [ ] support for strings
- [ ] support for fixpoints to be able to define `server_loop`
 **)

let sendError400 (fd:file_descr) : io unit =
  write (fd,(Bytes.utf8_encode "HTTP/1.1 400\n")) ;!@
  return ()

let get_req (fd:file_descr) : io (resexn Bytes.bytes) =
  match!@ (read (fd, UInt8.uint_to_t 255)) with
  | Inl (msg, _) -> return (Inl msg)
  | Inr err -> return (Inr err)

let process_connection (client : file_descr) (req_handler : req_handler) : io unit =
  match!@ get_req client with
  | Inr _ -> sendError400 client
  | Inl req -> begin
    match!@ req_handler client req (fun res -> write (client,res) ;!@ return (Inl ())) with
    | Inr err -> sendError400 client
    | Inl client -> return ()
  end

let rec process_connections (clients : lfds) (to_read : lfds) (req_handler : req_handler) : io lfds  =
  match clients with
  | [] -> return []
  | client :: tail ->
    begin
      let rest = process_connections tail to_read req_handler in
      if mem client to_read then begin
        process_connection client req_handler ;!@
        close client ;!@
        return tail
      end else return clients
    end

let get_new_connection (socket : file_descr) : io (option file_descr)  =
  match!@ select (([socket] <: lfds), ([] <: lfds), ([] <: lfds), 100uy) with
  | Inl (to_accept, _, _) ->
    if length to_accept > 0 then begin
      match!@ accept socket with
      | Inl client ->
        set_non_block client ;!@
        return (Some client)
      | _ -> return None
    end else return None
  | _ -> return None

let handle_connections
  (clients:lfds)
  (req_handler : req_handler) :
  io lfds =
  match!@ select (clients, ([] <: lfds), ([] <: lfds), 100uy) with
  | Inl (to_read, _, _) -> process_connections clients to_read req_handler
  | _ -> return clients

let server_loop_body
  (socket : file_descr)
  (req_handler : req_handler)
  (clients : lfds) :
  io lfds =
  match!@ get_new_connection socket with
  | None -> handle_connections clients req_handler
  | Some fd -> handle_connections (fd::clients) req_handler

let rec server_loop
  (iterations_count : nat)
  (socket : file_descr)
  (req_handler : req_handler)
  (clients : lfds) :
  io unit  =
  if iterations_count = 0 then return ()
  else begin
    let!@ clients' = server_loop_body socket req_handler clients in
    server_loop (iterations_count - 1) socket req_handler clients'
  end

let create_basic_server (ip:string) (port:UInt8.t) (limit:UInt8.t) :
  io (resexn file_descr) =
  match!@ socket () with
  | Inl socket ->
   (**   set_sock_opt (socket, SO_REUSEADDR, true) ;!@
    static_op Bind (socket, ip, port) ;!@
    static_op Listen (socket, limit)  ;!@ **)
    set_non_block socket ;!@
    return (Inl socket)
  | Inr err -> return (Inr err)

let webserver (req_handler : req_handler) () : io int =
  match!@ create_basic_server "0.0.0.0" 81uy 5uy with
  | Inl server -> begin
      server_loop 100000000000 server req_handler [] ;!@
      return 0
    end
  | Inr _ -> return (-1)
