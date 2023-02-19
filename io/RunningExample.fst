module RunningExample

open FStar.Ghost
open FStar.List.Tot.Base

open Compiler.Model

type access_policy = (history:trace) -> (isTrusted:bool) -> (cmd:io_cmds) -> (io_sig.args cmd) -> Type0

(** TODO: show that the type of access_policy is enough to enforce any monitorable property
 (from Grigore Rosu's paper) **)

unfold
let has_event_respected_pi (e:event) (ap:access_policy) (h:trace) : Type0 =
  match e with
  | EOpenfile isTrusted arg _ -> ap h isTrusted Openfile arg
  | ERead isTrusted arg _ -> ap h isTrusted Read arg
  | EWrite isTrusted arg _ -> ap h isTrusted Write arg
  | EClose isTrusted arg _ -> ap h isTrusted Close arg

(** `enforced_locally pi` is a prefix-closed safety trace property. **)
let rec enforced_locally
  (ap : access_policy)
  (h l: trace) :
  Tot Type0 (decreases l) =
  match l with
  | [] -> true
  | e  ::  t ->
    (has_event_respected_pi e ap h ==> enforced_locally (ap) (e::h) t) /\
    ~(has_event_respected_pi e ap h ==> False)
  
let pi_as_hist (#a:Type) (pi:access_policy) : hist a =
  (fun p h -> forall r lt. enforced_locally pi h lt ==> p lt r)

effect IIOpi (a:Type) (fl:FStar.Ghost.erased tflag) (pi : access_policy) = 
  IIOwp a fl (pi_as_hist #a pi)


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

val pi : access_policy
let pi h isTrusted cmd arg =
  match isTrusted, cmd with
  | false, Openfile -> 
    if arg = "/temp" then true else false
  | false, Read -> is_opened_by_untrusted h arg
  | false, Close -> is_opened_by_untrusted h arg
  | true, Write -> true
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

(* This may take a bit of effort to prove. *)

let webserver (handler:request_handler) :
  IIO (resexn unit) IOActions
    (requires (fun h -> True))
    (ensures (fun _ _ lt -> 
      every_request_gets_a_response lt))
    by (
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
      dump "H") =
  let client = static_cmd true Openfile "test.txt" in
  match client with | Inr err -> Inr err | Inl client -> begin
    match get_req client with
    | Some req -> handler client req (fun res -> static_cmd true Write (client,res))
    | None -> sendError 400 client;
    static_cmd true Close client
  end


type tgt_handler =
  (fl:erased tflag) ->
  (pi:erased access_policy) ->
  (io_acts:acts fl pi false) ->
  (client:file_descr) ->
  (req:string) ->
  (send:(msg:string -> IIOpi (resexn unit) fl pi)) ->
  IIOpi (resexn unit) fl pi

val target_handler : tgt_handler
let target_handler fl pi io_acts client req send =
  let _ = send req in 
  Inl ()
