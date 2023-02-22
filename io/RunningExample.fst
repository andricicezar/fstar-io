module RunningExample

open FStar.Ghost
open FStar.List.Tot.Base

open Compiler.Model


(** ** Type of source handler **)
assume val valid_http_response : string -> bool
assume val valid_http_request : string -> bool
assume val req_res : req:string{valid_http_request req} -> res:string{valid_http_response res}


val did_not_respond : trace -> bool
let did_not_respond h =
  match h with
  | EWrite _ _ _ :: _ -> false
  | _ -> true

val handler_only_openfiles_reads_client_acc : trace -> list file_descr -> Type0
let rec handler_only_openfiles_reads_client_acc lt open_descrs =
  match lt with
  | [] -> true
  | EOpenfile true  _ _ :: tl -> false
  | ERead true  _ _ :: tl -> false
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

val handler_only_openfiles_reads_client : trace -> Type0
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

val pi : access_policy
let pi h isTrusted cmd arg =
  match isTrusted, cmd with
  | false, Openfile -> 
    if arg = "/temp" then true else false
  | false, Read -> is_opened_by_untrusted h arg
  | false, Close -> is_opened_by_untrusted h arg
  | true, Write -> true
  | _ -> false

val wrote_at_least_once_to : file_descr -> trace -> bool
let rec wrote_at_least_once_to client lt =
  match lt with
  | [] -> false
  | EWrite true arg _::tl -> let (fd, msg):file_descr*string = arg in
                         client = fd
  | _ :: tl -> wrote_at_least_once_to client tl 

type request_handler (fl:erased tflag) =
  (client:file_descr) ->
  (req:string) ->
  (send:(msg:string -> IIO (resexn unit) fl (requires (fun h -> valid_http_response msg /\
                                                               did_not_respond h))
                                            (ensures (fun _ _ lt -> exists r. lt == [EWrite true (client,msg) r] /\
                                                                         wrote_at_least_once_to client lt)))) ->
  IIO (resexn unit) fl (requires (fun h -> valid_http_request req /\ did_not_respond h))
                       (ensures (fun h r lt -> enforced_locally pi h lt /\
                                             (wrote_at_least_once_to client lt \/ Inr? r)))

(** ** E.g. of source handler **)
val source_handler : request_handler IOActions
let source_handler client req send =
  let res = req_res req in
  let _ = send res in 
  Inl ()

type acts (fl:erased tflag) (pi:access_policy) (isTrusted:bool) =
  (cmd : io_cmds) ->
  (arg : io_sig.args cmd) ->
  IIO (io_resm cmd arg) fl
    (requires (fun _ -> True))
    (ensures (fun h r lt ->
      enforced_locally pi h lt /\
      (match r with
       | Inr Contract_failure -> lt == []
       | r' -> lt == [convert_call_to_event isTrusted cmd arg r'])))


(** ** E.g. of target handler **)
type tgt_handler =
  (fl:erased tflag) ->
  (pi:erased access_policy) ->
  (io_acts:acts fl pi false) ->
  (client:file_descr) ->
  (req:string) ->
  (send:(msg:string -> IIOpi (resexn unit) fl pi)) ->
  IIOpi (resexn unit) fl pi

val target_handler1 : tgt_handler
let target_handler1 fl pi io_acts client req send =
  let _ = send req in 
  Inl ()

val target_handler2 : tgt_handler
let target_handler2 fl pi io_acts client req send =
  let _ = io_acts Openfile "/etc/passwd" in
  let _ = send req in 
  Inl ()

(** ** Source webserver **)
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

assume val get_req : file_descr -> (req:string{valid_http_request req})
assume val sendError : int -> fd:file_descr -> IIO unit IOActions
 (fun _ -> True) (fun _ _ lt -> exists (msg:string) r. lt == [EWrite true (fd, msg) r])

open FStar.Tactics
(* This may take a bit of effort to prove. *)
let webserver (handler:request_handler IOActions) :
  IIO int IOActions
    (requires (fun h -> True))
    (ensures (fun _ _ lt -> 
      every_request_gets_a_response lt))
(**    by (
      explode ();
      bump_nth 49; 
      l_to_r [`FStar.List.Tot.Properties.append_nil_l];
      let l = instantiate (nth_binder 3) (fresh_uvar None) in
      let l = instantiate l (nth_binder (-3)) in
      mapply l;
      binder_retype (nth_binder (-3));
        l_to_r [`FStar.List.Tot.Properties.append_nil_l];
      trefl ();
      tadmit ();
      dump "H")**) =
  admit ();
  let client = static_cmd true Openfile "test.txt" in
  match client with | Inr _ -> (-1) | Inl client -> begin
  let req = get_req client in
  (match handler client req (fun res -> static_cmd true Write (client,res)) with 
  | Inr err -> sendError 400 client 
  | Inl client -> ());
  0
  end

(** ** Instante source interface with the example **)

val phi : enforced_policy pi
let phi h cmd arg =
  match cmd with
  | Openfile -> 
    if arg = "/temp" then true else false
  | Read -> is_opened_by_untrusted h arg
  | Close -> is_opened_by_untrusted h arg
  | Write -> false

let psi : trace -> int -> trace -> Type0 =
  (fun _ _ lt -> every_request_gets_a_response lt)

  (*
let rec lemma1 (lt h:trace) : Lemma (requires (enforced_locally pi h lt)) (ensures (handler_only_openfiles_reads_client lt)) =
  match lt with
  | [] -> ()
  | e::tl -> admit ()//  lemma1 tl (e::h)

let ct_rcs' : tree pck_rc = 
  Node 
    (| string, resexn unit, (fun msg h _ _ -> valid_http_response msg && did_not_respond h) |)
    Leaf
    Leaf


let ct_rcs : tree pck_rc =
  Node (| file_descr -> string -> trace -> resexn unit -> trace -> bool, (fun (client, req) _ _ lt -> wrote_at_least_once_to client lt) |)
    ct_rcs'
    Leaf
*)
(** ** Tests: compile web-server, back-translate handler, linking **)
