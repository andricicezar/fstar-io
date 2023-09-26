module WebServer

open FStar.Tactics
open FStar.Ghost
open ExtraTactics

open FStar.List.Tot.Base
open FStar.List.Tot.Properties

open Compiler.Model1
open Utils

type req_handler (fl:erased tflag) =
  (client:file_descr) ->
  (req:Bytes.bytes) ->
  (send:(res:Bytes.bytes -> MIO (resexn unit) fl mymst (requires (fun h -> did_not_respond h /\ valid_http_response res))
                                            (ensures (fun h _ lt -> exists r. lt == [EWrite Prog (client,res) r])))) ->
  MIO (resexn unit) fl mymst
    (requires (fun h -> valid_http_request req /\ did_not_respond h))
    (ensures (fun h r lt -> enforced_locally sgm h lt /\
                          (wrote_to client (rev lt) \/ Inr? r)))

let static_op
  (op : io_ops)
  (arg : io_sig.args op) :
  MIO (io_sig.res op arg) IOOps mymst
    (requires (fun h -> io_pre op arg h))
    (ensures (fun h (r:io_sig.res op arg) lt ->
        io_post op arg r /\
        lt == [convert_call_to_event Prog op arg r])) =
  static_op Prog op arg

#push-options "--compat_pre_core 1"
let sendError400 (fd:file_descr) : MIO unit IOOps mymst
 (fun _ -> True) (fun _ _ lt -> exists res r. lt == [EWrite Prog (fd, res) r]) =
  let _ = static_op Write (fd,(Bytes.utf8_encode "HTTP/1.1 400\n")) in
  ()

let get_req (fd:file_descr) :
  MIO (resexn (r:Bytes.bytes{valid_http_request r})) IOOps mymst (fun _ -> True) (fun _ _ lt -> exists r'. lt == [ERead Prog (fd, (UInt8.uint_to_t 255)) r']) =
  match static_op Read (fd, UInt8.uint_to_t 255) with
  | Inl (msg, _) ->
   Inl msg
  | Inr err -> Inr err

#push-options "--split_queries always"
let process_connection
  (client : file_descr)
  (#fl:erased tflag)
  (req_handler : req_handler (IOOps + fl)) :
  MIO unit (IOOps+fl) mymst (fun _ -> True)
    (fun _ _ lt -> every_request_gets_a_response lt) =
  introduce forall h lthandler lt lt'. enforced_locally sgm h lthandler /\ every_request_gets_a_response (lt @ lt') ==> every_request_gets_a_response (lt @ lthandler @ lt')
  with begin
    introduce enforced_locally sgm h lthandler /\ every_request_gets_a_response (lt @ lt') ==> every_request_gets_a_response (lt @ lthandler @ lt')
    with _. ergar_pi_irr h lthandler lt lt'
  end ;
  introduce forall h lthandler limit r lt. enforced_locally sgm h lthandler /\ wrote_to client (rev lthandler) /\ every_request_gets_a_response lt ==> every_request_gets_a_response (lt @ [ ERead Prog (client, limit) (Inl r) ] @ lthandler)
  with begin
    introduce enforced_locally sgm h lthandler /\ wrote_to client (rev lthandler) /\ every_request_gets_a_response lt ==> every_request_gets_a_response (lt @ [ ERead Prog (client, limit) (Inl r) ] @ lthandler)
    with _. ergar_pi_write h lthandler client limit r lt
  end ;
  match get_req client with
  | Inr _ -> sendError400 client
  | Inl req ->
    begin match req_handler client req (fun res -> let _ = static_op Write (client,res) in Inl ()) with
    | Inr err -> sendError400 client
    | Inl client -> ()
    end
 #pop-options

let rec process_connections
  (clients : lfds)
  (to_read : lfds)
  (#fl:erased tflag)
  (req_handler : req_handler (IOOps + fl)) :
  MIO lfds (IOOps+fl) mymst (fun _ -> True)
    (fun _ _ lt -> every_request_gets_a_response lt) =
  match clients with
  | [] -> []
  | client :: tail ->
    begin
      let rest = process_connections tail to_read req_handler in
      if mem client to_read then begin
        process_connection client req_handler ;
        let _ = static_op Close client in
        every_request_gets_a_response_append () ;
        tail
      end else clients
    end

let get_new_connection (socket : file_descr) :
  MIO (option file_descr) IOOps mymst (fun _ -> True)
    (fun _ _ lt -> every_request_gets_a_response lt) =
  match static_op Select (([socket] <: lfds), ([] <: lfds), ([] <: lfds), 100uy) with
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
  (#fl:erased tflag)
  (req_handler : req_handler (IOOps + fl)) :
  MIO lfds (fl+IOOps) mymst (fun _ -> True)
    (fun _ _ lt -> every_request_gets_a_response lt) =
  match static_op Select (clients, ([] <: lfds), ([] <: lfds), 100uy) with
  | Inl (to_read, _, _) ->
    let clients'' = process_connections clients to_read req_handler in
    clients''
  | _ -> clients

let server_loop_body
  (socket : file_descr)
  (#fl:erased tflag)
  (req_handler : req_handler (IOOps + fl))
  (clients : lfds) :
  MIO lfds (fl+IOOps) mymst (fun _ -> True)
    (fun _ _ lt -> every_request_gets_a_response lt) =
  let clients' = (match get_new_connection socket with
                 | None -> clients
                 | Some fd -> fd :: clients) in
  every_request_gets_a_response_append () ;
  handle_connections clients' req_handler

let rec server_loop
  (iterations_count : nat)
  (socket : file_descr)
  (#fl:erased tflag)
  (req_handler : req_handler (IOOps + fl))
  (clients : lfds) :
  MIO unit (fl+IOOps) mymst (fun _ -> True)
    (fun _ _ lt -> every_request_gets_a_response lt) =
  if iterations_count = 0 then ()
  else begin
    let clients' = server_loop_body socket req_handler clients in
    every_request_gets_a_response_append () ;
    server_loop (iterations_count - 1) socket req_handler clients'
  end

let create_basic_server (ip:string) (port:UInt8.t) (limit:UInt8.t) :
  MIO (resexn file_descr) IOOps mymst (fun _ -> True)
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
  (#fl:erased tflag)
  (req_handler : req_handler (IOOps + fl))
  () :
  MIO int (IOOps + fl) mymst
    (requires (fun h -> True))
    (ensures (fun h r lt -> every_request_gets_a_response lt)) =
  match create_basic_server "0.0.0.0" 81uy 5uy with
  | Inl server -> begin
      server_loop 100000000000 server req_handler [] ;
      every_request_gets_a_response_append () ;
      0
    end
  | Inr _ -> -1


(** Compiling Web Server **)

let check_send_pre : tree (pck_dc mymst) =
  Node
    (| Bytes.bytes, unit, (fun res s0 _ _ -> s0.st = DidNotRespond && valid_http_response res) |)
    Leaf
    Leaf

let export_send (#fl:erased tflag) : exportable ((res:Bytes.bytes -> MIO (resexn unit) fl mymst (fun h -> did_not_respond h && valid_http_response res)
                                            (fun _ _ lt -> exists fd r. lt == [EWrite Prog (fd,res) r] ))) fl Utils.sgm mymst check_send_pre =
  exportable_arrow_pre_post_args Bytes.bytes unit _ _ #() #()

let check_handler_post : tree (pck_dc mymst) =
  Node (|
      file_descr,
      unit,
      (fun client s0 _ s1 -> not (client `mem` s0.written) && client `mem` s1.written)
    |)
    check_send_pre
    Leaf

val help_import :
  (fl:erased tflag) ->
  (wf:(file_descr -> Bytes.bytes -> (export_send #fl).ityp -> MIOpi (resexn unit) fl Utils.sgm mymst)) ->
  (eff_dcs:typ_eff_dcs fl mymst check_handler_post) ->
  req_handler fl
let help_import fl wf eff_dcs client req send :
  MIO (resexn unit) fl mymst
    (requires (fun h -> valid_http_request req /\ did_not_respond h))
    (ensures (fun h r lt -> enforced_locally sgm h lt /\
                          (wrote_to client (rev lt) \/ Inr? r)))
=
  introduce forall h lt client. ((not (wrote_to client h)) && wrote_to client ((rev lt) @ h)) ==> wrote_to client (rev lt)
  with begin
    if (not (wrote_to client h)) && wrote_to client ((rev lt) @ h)
    then wrote_to_split client (rev lt) h
    else ()
  end ;
  let lfcks : typ_eff_dcs fl mymst check_send_pre = typ_left eff_dcs in
  let send' = (export_send #fl).export lfcks send in
  let (| dc_pck, eff_dc |) = root eff_dcs in
  let (| _, eff_dc' |) = eff_dc client in
  let r : resexn unit = wf client req send' in
  let (_, b) = eff_dc' () in
  if b then r
  else Inr Contract_failure

instance import_request_handler (fl:erased tflag) : safe_importable (req_handler fl) fl Utils.sgm mymst check_handler_post = {
  ityp = file_descr -> Bytes.bytes -> export_send.ityp -> MIOpi (resexn unit) fl Utils.sgm mymst;
  c_ityp = interm_arrow3 fl Utils.sgm mymst file_descr Bytes.bytes export_send.ityp #export_send.c_ityp (resexn unit);
  safe_import = help_import fl
}

let cs_int : src_interface = {
  mst = mymst;
  sgm = Utils.sgm;
  pi = Utils.pi;
  ct = req_handler;
  ct_dcs = check_handler_post;
  ct_importable = (fun fl -> import_request_handler fl);
  psi = (fun _ _ lt -> Utils.every_request_gets_a_response lt);
}

let compiled_webserver =
  comp.compile_pprog #cs_int webserver
