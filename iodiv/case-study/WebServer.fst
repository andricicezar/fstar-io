module WebServer

open FStar.Tactics
open FStar.List

open IIOSig
open IIOSigSpec
open TauIODiv
open TauIIODiv
open DivFreeTauSpec



type monitorable_prop = (cmd:io_sig.act) -> (io_sig.arg cmd) -> (history:trace) -> Tot bool

let destruct_event (e:event) : ( cmd:io_sig.act & (arg:io_sig.arg cmd) & io_sig.res arg )  =
  match e with
  | EOpenfile arg res -> (| Openfile, arg, res |)
  | ERead arg res -> (| Read, arg, res |)
  | EWrite arg res -> (| Write, arg, res |)
  | EClose arg res -> (| Close, arg, res |)
  | ESocket arg res -> (| Socket, arg, res |)
  | ESetsockopt arg res -> (| Setsockopt, arg, res |)
  | EBind arg res -> (| Bind, arg, res |)
  | ESetNonblock arg res -> (| SetNonblock, arg, res |)
  | EListen arg res -> (| Listen, arg, res |)
  | EAccept arg res -> (| Accept, arg, res |)
  | ESelect arg res -> (| Select, arg, res |)

unfold
let has_event_respected_pi (e:event) (check:monitorable_prop) (h:trace) : bool =
  let (| ac, arg, res |) = destruct_event e in
  check ac arg h

let rec enforced_locally
  (check : monitorable_prop)
  (h l: trace) :
  Tot bool (decreases l) =
  match l with
  | [] -> true
  | e  ::  t ->
    if has_event_respected_pi e check h then enforced_locally (check) (e::h) t
    else false

let pi_post (check : monitorable_prop) (h:trace) (r : orun 'a) : Type0 =
  match r with
  | Ocv olt _ -> enforced_locally check h (to_trace olt)
  | Odv slt -> forall n. enforced_locally check h (to_trace (Stream.stream_trunc slt n))

effect IIODivpi (a : Type) (pi:monitorable_prop) (pre : history -> Type0) (post : (hist : history) -> orun a -> Pure Type0 (requires pre hist) (ensures fun _ -> True)) =
  IIODiv a pre (fun h r -> pi_post pi h r /\ post h r)

effect IIO (a : Type) (pre : history -> Type0) (post : (hist : history) -> orun a -> Pure Type0 (requires pre hist) (ensures fun _ -> True)) =
  IIODiv a pre (fun h r -> terminates r /\ post h r)

let pi : monitorable_prop = fun cmd (arg:io_sig.arg cmd) h ->
  match cmd with
  | Openfile -> let (fnm, _, _) = (arg <: string * (list open_flag) * zfile_perm) in not (fnm = "/etc/passwd")
  | _ -> true

type plugin_type =
  (fd:file_descr) -> IIODiv (option unit) (fun h -> True) (fun h r -> True)

#set-options "--log_queries"
let foreach #a
  (f:a -> IIODiv unit (fun _ -> True) (fun _ _ -> True))
  (l:list a) :
  IIODiv unit (fun _ -> True) (fun _ _ -> True) =
  admit ();
  TauIIODiv.iter 
    #nat 
    #unit
    #(fun index -> iprepost (fun _ -> True) (fun _ _ -> True))
    (fun index -> begin
       if index < List.Tot.length l then
         let client = List.Tot.index l index in
         f client;
         Inl (index + 1)
       else Inr ()
    end) 0

(** this generates 397 goals. not sure why **)
let process_connection
  (plugin : plugin_type)
  (client : file_descr) : 
  IIODiv unit
    (requires (fun _ -> True))
    (ensures (fun _ _ -> True)) by (
    explode ();
    dump "H")
    =
  let _ = plugin client in
  let _ = act_call Close client in
  ()

let process_connections 
  (clients : lfds) 
  (to_read : lfds) 
  (plugin : plugin_type) : 
  IIODiv lfds
    (requires (fun _ -> True))
    (ensures (fun _ _ -> True)) =
  let (ready, idle) = List.Tot.partition (fun cl -> List.mem cl to_read) clients in
  foreach (process_connection plugin) ready;
  idle

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
