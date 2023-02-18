module RunningExample

open FStar.Ghost
open FStar.List.Tot.Base

open Compiler.Model

assume val valid_http_response : string -> bool
assume val valid_http_request : string -> bool

val did_not_respond : trace -> bool
let did_not_respond h =
  match h with
  | EWrite _ _ _ :: _ -> false
  | _ -> true

val handler_only_openfiles_reads_client_acc : trace -> list file_descr -> bool
let rec handler_only_openfiles_reads_client_acc lt open_descrs =
  match lt with
  | [] -> true
  | EOpenfile true  _ _ :: tl -> handler_only_openfiles_reads_client_acc tl open_descrs
  | ERead true  _ _ :: tl -> handler_only_openfiles_reads_client_acc tl open_descrs
  | EWrite true _ _ :: tl -> handler_only_openfiles_reads_client_acc tl open_descrs
  | EClose true  _ _ :: tl -> handler_only_openfiles_reads_client_acc tl open_descrs
  | EOpenfile false fnm res :: tl -> 
    if fnm = "/temp" then begin
      match res with
      | Inl fd -> handler_only_openfiles_reads_client_acc tl (fd::open_descrs)
      | Inr err -> handler_only_openfiles_reads_client_acc tl open_descrs
    end else false
  | ERead false fd _ :: tl -> 
    if fd `mem` open_descrs then handler_only_openfiles_reads_client_acc tl open_descrs
    else false
  | EWrite false _ _ :: tl -> false
  | EClose false fd _ :: tl -> 
    if fd `mem` open_descrs then handler_only_openfiles_reads_client_acc tl (filter (fun fd' -> fd <> fd') open_descrs)
    else false

val handler_only_openfiles_reads_client : trace -> bool
let handler_only_openfiles_reads_client lt =
  handler_only_openfiles_reads_client_acc lt []

let rec is_opened_by_untrusted (h:trace) (fd:file_descr) : bool =
  match h with
  | [] -> false
  | EOpenfile false _ (Inl fd') :: tl -> begin
    if fd = fd' then true
    else is_opened_by_untrusted tl fd
  end
  | EClose _ fd' (Inl ()) :: tl -> if fd = fd' then false
                             else is_opened_by_untrusted tl fd
  | _ :: tl -> is_opened_by_untrusted tl fd

val pi : monitorable_prop
let pi h cmd arg =
  match cmd with
  | Openfile -> 
    if arg = "/temp" then true else false
  | Read -> is_opened_by_untrusted h arg
  | Close -> is_opened_by_untrusted h arg
  | _ -> false

let rec lemma1 (lt h:trace) : Lemma (requires (enforced_locally pi h lt)) (ensures (handler_only_openfiles_reads_client lt)) =
  match lt with
  | [] -> ()
  | e::tl -> admit ()//  lemma1 tl (e::h)


val wrote_at_least_once_to : file_descr -> trace -> bool
let rec wrote_at_least_once_to client lt =
  match lt with
  | [] -> false
  | EWrite true arg _::tl -> let (fd, msg):file_descr*string = arg in
                         client = fd
  | _ :: tl -> wrote_at_least_once_to client tl 

type request_handler =
  (client:file_descr) ->
  (req:string) ->
  (send:(msg:string -> IIO (resexn unit) IOActions (requires (fun h -> valid_http_response msg /\
                                                                      did_not_respond h))
                                                   (ensures (fun _ _ lt -> exists r. lt == [EWrite true (client,msg) r] /\
                                                                         wrote_at_least_once_to client lt)))) ->
  IIO (resexn unit) IOActions (requires (fun h -> valid_http_request req /\ did_not_respond h))
                              (ensures (fun h _ lt -> enforced_locally pi h lt /\
                                                    wrote_at_least_once_to client lt))

assume val req_res : req:string{valid_http_request req} -> res:string{valid_http_response res}

val source_handler : request_handler
let source_handler client req send =
  let res = req_res req in
  let _ = send res in 
  Inl ()

val every_request_gets_a_response_acc : trace -> list file_descr -> Type0
let rec every_request_gets_a_response_acc lt read_descrs =
  match lt with
  | [] -> read_descrs == []
  | ERead true fd (Inl _)::tl -> every_request_gets_a_response_acc tl (fd::read_descrs)
  | EWrite true (fd,_) _::tl -> every_request_gets_a_response_acc tl (filter (fun fd' -> fd <> fd') read_descrs)
  | _::tl -> every_request_gets_a_response_acc tl read_descrs

val every_request_gets_a_response : trace -> Type0
let every_request_gets_a_response lt =
  every_request_gets_a_response_acc lt []

assume val get_req : file_descr -> option (req:string{valid_http_request req})
assume val sendError : int -> fd:file_descr -> IIO unit IOActions
 (fun _ -> True) (fun _ _ lt -> exists (msg:string) r. lt == [EWrite true (fd, msg) r])

open FStar.Tactics

(* Stuck: enforcing the access policy on the context, gives as a 
   trace property that talks about the events produced by the context.
   However, one also has to talk about the events produced by the program
   inside the context. 

   Otherwise, we can not prove every_request_gets_a_response post-condition,
   because theoretically the partial program can produce events 
   inside the context that violate the condition.
   
   One can manually adnotate the post-condition of the handler to say 
   that it includes only writes of the partial program, but then
   we cannot enforce it with the access policy or higher-order contracts.
   Can we find some kind of property that makes it safe to
   ``forget"?

   Another strategy would be to find a different post-condition for
   the webserver :D.
*)

let webserver (handler:request_handler) :
  IIO (resexn unit) IOActions
    (requires (fun h -> True))
    (ensures (fun _ _ lt -> every_request_gets_a_response lt)) by
  (explode (); bump_nth 49; 
    rewrite_eqs_from_context (); dump "H") =
  let client = static_cmd true Openfile "test.txt" in
  match client with | Inr err -> Inr err | Inl client -> begin
    match get_req client with
    | Some req -> handler client req (fun res -> static_cmd true Write (client,res))
    | None -> sendError 400 client;
    static_cmd true Close client
  end


type tgt_handler =
  (fl:erased tflag) ->
  (pi:erased monitorable_prop) ->
  (io_acts:acts fl pi false) ->
  (client:file_descr) ->
  (req:string) ->
  (send:(msg:string -> IIOpi (resexn unit) fl pi)) ->
  IIOpi (resexn unit) fl pi

val target_handler : tgt_handler
let target_handler fl pi io_acts client req send =
  let _ = send req in 
  Inl ()
