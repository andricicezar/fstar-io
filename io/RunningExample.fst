module RunningExample

open Compiler.Languages

assume val valid_http_response : string -> bool
assume val valid_http_request : string -> bool

val did_not_respond : trace -> bool
let did_not_respond h =
  match h with
  | EWrite _ _ _ :: _ -> false
  | _ -> true

open FStar.List.Tot.Base

val handler_only_openfiles_reads_client_acc : trace -> list file_descr -> bool
let rec handler_only_openfiles_reads_client_acc lt open_descr =
  match lt with
  | [] -> true
  | EWrite true _ _ :: tl -> handler_only_openfiles_reads_client_acc tl open_descr
  | EOpenfile false fnm res :: tl -> 
    if fnm = "/temp" then begin
      match res with
      | Inl fd -> handler_only_openfiles_reads_client_acc tl (fd::open_descr)
      | Inr err -> handler_only_openfiles_reads_client_acc tl open_descr
    end else false
  | ERead false fd _ :: tl -> 
    if fd `mem` open_descr then handler_only_openfiles_reads_client_acc tl open_descr
    else false
  | EClose false fd _ :: tl -> 
    if fd `mem` open_descr then handler_only_openfiles_reads_client_acc tl (filter (fun fd' -> fd <> fd') open_descr)
    else false
  | _ :: tl -> false

val handler_only_openfiles_reads_client : trace -> bool
let handler_only_openfiles_reads_client lt =
  handler_only_openfiles_reads_client_acc lt []
  
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
                              (ensures (fun _ _ lt -> handler_only_openfiles_reads_client lt /\
                                                    wrote_at_least_once_to client lt))

assume val req_res : req:string{valid_http_request req} -> res:string{valid_http_response res}

open FStar.Tactics

val source_handler : request_handler
let source_handler client req send =
  let res = req_res req in
  let _ = send res in 
  Inl ()
