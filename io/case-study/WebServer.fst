module WebServer

open FStar.Tactics
open FStar.Ghost
open ExtraTactics

open FStar.List.Tot.Base
open FStar.List.Tot.Properties

open Compiler.Model
open Utils

let static_cmd
  (cmd : io_cmds)
  (arg : io_sig.args cmd) :
  MIO (io_sig.res cmd arg) IOActions
    (requires (fun h -> io_pre cmd arg h))
    (ensures (fun h (r:io_sig.res cmd arg) lt ->
        lt == [convert_call_to_event true cmd arg r])) =
  static_cmd true cmd arg

type req_handler (fl:erased tflag) =
  (client:file_descr) ->
  (req:Bytes.bytes) ->
  (send:(msg:Bytes.bytes -> MIO (resexn unit) fl (requires (fun h -> did_not_respond h /\ Bytes.length msg < 500))
                                            (ensures (fun _ _ lt -> exists r. lt == [EWrite true (client,msg) r] /\
                                                                  wrote_at_least_once_to client lt)))) ->
  MIO (resexn unit) fl (requires (fun h -> did_not_respond h))
                       (ensures (fun h r lt -> enforced_locally pi h lt /\
                                             (wrote_at_least_once_to client lt \/ Inr? r)))


let sendError400 (fd:file_descr) : MIO unit IOActions
 (fun _ -> True) (fun _ _ lt -> exists msg r. lt == [EWrite true (fd, msg) r]) =
  let _ = static_cmd Write (fd,(Bytes.utf8_encode "HTTP/1.1 400\n")) in
  ()


let get_req (fd:file_descr) :
  MIO (resexn Bytes.bytes) IOActions (fun _ -> True) (fun h r lt -> exists limit r'. (Inl? r <==> Inl? r') /\ lt == [ERead true (fd, limit) r']) =
  let limit : unit -> UInt8.t = (fun () -> UInt8.uint_to_t 255) in
  match static_cmd Read (fd,limit ()) with
  | Inl (msg, _) -> Inl msg
  | Inr err -> Inr err

let process_connection
  (client : file_descr) 
  (#fl:erased tflag)
  (req_handler : req_handler (IOActions + fl)) : 
  MIO unit (IOActions+fl) (fun _ -> True)
    (fun _ _ lt -> every_request_gets_a_response lt) =
  admit ();
  introduce forall h lthandler lt lt'. enforced_locally pi h lthandler /\ every_request_gets_a_response (lt @ lt') ==> every_request_gets_a_response (lt @ lthandler @ lt')
  with begin
    introduce enforced_locally pi h lthandler /\ every_request_gets_a_response (lt @ lt') ==> every_request_gets_a_response (lt @ lthandler @ lt')
    with _. ergar_pi_irr h lthandler lt lt'
  end ;
  introduce forall h lthandler client limit r lt. enforced_locally pi h lthandler /\ wrote_at_least_once_to client lthandler /\ every_request_gets_a_response lt ==> every_request_gets_a_response (lt @ [ ERead true (client, limit) (Inl r) ] @ lthandler)
  with begin
    introduce enforced_locally pi h lthandler /\ wrote_at_least_once_to client lthandler /\ every_request_gets_a_response lt ==> every_request_gets_a_response (lt @ [ ERead true (client, limit) (Inl r) ] @ lthandler)
    with _. ergar_pi_write h lthandler client limit r lt
  end ;
  match get_req client with
  | Inr _ -> ()
  | Inl req ->
    begin match req_handler client req (fun res -> let _ = static_cmd Write (client,res) in Inl ()) with
    | Inr err -> sendError400 client
    | Inl client -> ()
    end

let rec process_connections
  (clients : lfds) 
  (to_read : lfds) 
  (#fl:erased tflag)
  (req_handler : req_handler (IOActions + fl)) : 
  MIO lfds (IOActions+fl) (fun _ -> True)
    (fun _ _ lt -> every_request_gets_a_response lt) =
  match clients with
  | [] -> []
  | client :: tail -> 
    begin
      let rest = process_connections tail to_read req_handler in
      if List.mem client to_read then begin
        process_connection client req_handler ;
        let _ = static_cmd Close client in
        every_request_gets_a_response_append () ;
        tail 
      end else clients
    end
 
let get_new_connection (socket : file_descr) :
  MIO (option file_descr) IOActions (fun _ -> True)
    (fun _ _ lt -> every_request_gets_a_response lt) =
  match static_cmd Select (([socket] <: lfds), ([] <: lfds), ([] <: lfds), 100uy) with
  | Inl (to_accept, _, _) ->
    if List.length to_accept > 0 then begin 
      match static_cmd Accept socket with
      | Inl client -> 
        let _ = static_cmd SetNonblock client in
        Some client
      | _ -> None
    end else None
  | _ -> None

let handle_connections
  (clients:lfds)
  (#fl:erased tflag)
  (req_handler : req_handler (IOActions + fl)) : 
  MIO lfds (fl+IOActions) (fun _ -> True)
    (fun _ _ lt -> every_request_gets_a_response lt) =
  match static_cmd Select (clients, ([] <: lfds), ([] <: lfds), 100uy) with
  | Inl (to_read, _, _) ->
    let clients'' = process_connections clients to_read req_handler in
    clients''
  | _ -> clients

let server_loop_body 
  (socket : file_descr) 
  (#fl:erased tflag)
  (req_handler : req_handler (IOActions + fl))
  (clients : lfds) :
  MIO lfds (fl+IOActions) (fun _ -> True)
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
  (req_handler : req_handler (IOActions + fl))
  (clients : lfds) :
  MIO unit (fl+IOActions) (fun _ -> True)
    (fun _ _ lt -> every_request_gets_a_response lt) =
  if iterations_count = 0 then ()
  else begin
    let clients' = server_loop_body socket req_handler clients in
    every_request_gets_a_response_append () ;
    server_loop (iterations_count - 1) socket req_handler clients'
  end

let create_basic_server (ip:string) (port:UInt8.t) (limit:UInt8.t) :
  MIO (resexn file_descr) IOActions (fun _ -> True)
    (fun _ _ lt -> every_request_gets_a_response lt) =
  match static_cmd Socket () with
  | Inl socket -> 
    let _ = static_cmd Setsockopt (socket, SO_REUSEADDR, true) in 
    let _ = static_cmd Bind (socket, ip, port) in
    let _ = static_cmd Listen (socket, limit) in
    let _ = static_cmd SetNonblock socket in
    Inl socket 
  | Inr err -> Inr err

let webserver 
  (#fl:erased tflag)
  (req_handler : req_handler (IOActions + fl)) 
  () :
  MIO int (IOActions + fl)
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

let check_send_pre : tree pck_rc = 
  Node 
    (| Bytes.bytes, unit, (fun msg h _ _ ->
      Utils.did_not_respond' h && (Bytes.length msg) < 500) |)
    Leaf
    Leaf

let export_send (#fl:erased tflag) : exportable ((msg:Bytes.bytes -> MIO (resexn unit) fl (fun h -> did_not_respond h && Bytes.length msg < 500)
                                            (fun _ _ lt -> exists fd r. lt == [EWrite true (fd,msg) r] ))) Utils.pi check_send_pre fl =
  exportable_arrow_pre_post_args Bytes.bytes unit
    (fun msg h -> did_not_respond h && Bytes.length msg < 500)
    (fun msg _ _ lt -> exists fd r. lt == [EWrite true (fd,msg) r])
    #()
    #()


let check_handler_post : tree pck_rc =
  Node (| file_descr, unit, (fun (client:file_descr) _ _ lt -> 
      Utils.wrote_at_least_once_to' client lt) |)
    check_send_pre 
    Leaf

instance import_request_handler (fl:erased tflag) : safe_importable (req_handler fl) Utils.pi check_handler_post fl = {
  swtyp = file_descr -> Bytes.bytes -> export_send.wtyp -> MIOpi (resexn unit) fl Utils.pi;
  c_swtyp = weak_arrow3 fl Utils.pi file_descr Bytes.bytes export_send.wtyp #export_send.c_wtyp (resexn unit);
  safe_import = (fun (wf:file_descr -> Bytes.bytes -> export_send.wtyp -> MIOpi (resexn unit) fl Utils.pi) eff_rcs -> 
    let f' : req_handler fl = (fun (fd:file_descr) req send -> 
      let send' = export_send.export (left eff_rcs) send in
      let (| rc_pck, eff_rc |) = root eff_rcs in
      // fd here is 4
      let (| h, eff_rc' |) = eff_rc fd in
      Classical.forall_intro (lemma_suffixOf_append h);
      let r : resexn unit = wf fd req send' in
      Classical.forall_intro_2 (Classical.move_requires_2 (lemma_append_rev_inv_tail h));
      if eff_rc' () then r
      else Inr Contract_failure
    ) in
    f'
  )
}

let cs_int : src_interface = {
  pi = Utils.pi;
  phi = Utils.phi;
  ct = req_handler;
  ct_rcs = check_handler_post;
  ct_importable = (fun fl -> import_request_handler fl); 
  psi = (fun _ _ lt -> Utils.every_request_gets_a_response lt);
}

let compiled_webserver = 
  comp.compile_pprog #cs_int webserver 
