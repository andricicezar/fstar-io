module GoodHandler1

open FStar.Tactics
open FStar.Ghost

open Compiler.Model1
open Utils
open WebServer

let tgt_cs_int = comp.comp_int cs_int

type tgt_handler = ctx_tgt tgt_cs_int

let link = comp.target.link #tgt_cs_int

let pi = tgt_cs_int.pi

#push-options "--compat_pre_core 1"

let rec _extract_path (header : list Char.char) : Tot (list Char.char) =
  match header with
    | [] -> []
    | ' ' :: tail -> []
    | h :: tail -> h :: _extract_path tail

let extract_path (header : list Char.char) =
  String.string_of_list (_extract_path header)

type request_type =
| GET : string -> request_type
| Error : request_type

let parse_http_header (header : UBytes.bytes) : request_type =
  match UBytes.iutf8_opt header with
  | None -> Error
  | Some header ->
  let h = String.list_of_string header in
  match h with
  | 'G' :: 'E :: 'T' :: ' ' :: tail -> GET (extract_path tail)
  | _ -> Error

let rec get_file
  (#fl:erased tflag)
  (call_io:io_lib fl pi mymst Ctx)
  (fd : file_descr) (limit : UInt8.t)
  (i:nat) :
  MIOpi UBytes.bytes fl pi mymst =
  match call_io Read (fd,limit) with
  | Inl (chunk, size) -> begin
    let chunk = UBytes.from_bytes chunk in
    if UInt8.lt size limit || i = 0 then
      UBytes.slice chunk 0ul (UInt32.uint_to_t (UInt8.v size))
    else (
      UBytes.append chunk (get_file call_io fd limit (i-1))
    )
  end
  | _ -> UBytes.utf8_encode ""

(**let write_string
  (#fl:erased tflag)
  (send:UBytes.bytes -> MIOpi (resexn unit) fl pi)
  (s:string) : MIOpi unit fl pi =
    admit (); // because of bytes
    let _ = send (UBytes.utf8_encode s) in ()

let write_int
  (#fl:erased tflag)
  (send:UBytes.bytes -> MIOpi (resexn unit) fl pi)
  (x:int) :
  MIOpi unit fl pi =
  let (s:string) = string_of_int x in
  write_string #fl send s
**)

// open FStar.Tactics

// let rec lemma1_0 (pi:policy_spec) (h lt1 lt2:trace) : Lemma
//   (requires (enforced_locally pi h lt1 /\ enforced_locally pi (List.rev lt1 @ h) lt2))
//   (ensures (enforced_locally pi h (lt1@lt2))) =
//   match lt2 with
//   | [] -> ()
//   | e::tl ->
//     assert (enforced_locally pi h (lt1@[e]));
//     assert (enforced_locally pi (List.rev (lt1@[e]) @ h) tl);
//     lemma1_0 pi h (lt1@[e]) tl

// let lemma1 (pi:policy_spec) : Lemma (
//   forall h lt1 lt2. enforced_locally pi h lt1 /\ enforced_locally pi (List.rev lt1 @ h) lt2 ==>
//     enforced_locally pi h (lt1@lt2)) =
//   Classical.forall_intro_3 (Classical.move_requires_3 (lemma1_0 pi))

let head
  (status_code:int) :
  Tot string =
  FStar.String.concat ""
    ["HTTP/1.1 ";
     string_of_int status_code;
    "\n"]

let set_headers
  (status_code:int) (media_type:string) (content_length: int) :
  Tot string =
  FStar.String.concat ""
    [head status_code;
    "Content-Length: ";
    string_of_int content_length;
    "\nContent-Type: ";
    media_type;
    "\n\n"]

let respond
  (#fl:erased tflag)
  (send:UBytes.bytes -> MIOpi (resexn unit) fl pi mymst)
  (status_code:int) (media_type:string) (content:UBytes.bytes) :
  MIOpi unit fl pi mymst =
  let hdrs = set_headers status_code media_type (UBytes.length content) in
  let msg = (UBytes.append (UBytes.utf8_encode hdrs) content) in
  let _ = send msg in
  ()

let get_fd_stats
  (#fl:erased tflag)
  (call_io:io_lib fl pi mymst Ctx)
  (file_full_path: string) :
  MIOpi (resexn (file_descr * stats)) fl pi mymst =
  let _ = call_io Access (file_full_path,[R_OK]) in
  let file_stats = call_io Stat file_full_path in
  let fd = call_io Openfile (file_full_path,[O_RDONLY],0) in
  match fd, file_stats with
  | Inl fd, Inl file_stats -> Inl (fd, file_stats)
  | _, _ -> Inr Contract_failure

let get_media_type (file_path : string) : (media_type:string{String.maxlen media_type (pow2 30)}) =
  if String.length file_path >= 3 then
    let extension = String.sub file_path ((String.length file_path)-3) 3 in
    match (String.list_of_string extension) with
    | 'j' :: 'p' :: 'g' :: _ -> "image/jpg"
    | 't' :: 'm' :: 'l' :: _ -> "text/html"
    | _ -> "text/plain"
  else "text/plain"

let get_query
  (#fl:erased tflag)
  (call_io:io_lib fl pi mymst Ctx)
  (send:UBytes.bytes -> MIOpi (resexn unit) fl pi mymst)
  (file_full_path : string) :
  MIOpi unit fl pi mymst =
  admit () ; // Should we prove something?
  match get_fd_stats call_io file_full_path with | Inr _ -> () | Inl (fd, stat) -> begin
    let hdrs = set_headers 200 (get_media_type file_full_path) (UInt8.v stat.st_size) in
    let file = get_file #fl call_io fd 100uy 100 in
    let msg = (UBytes.append (UBytes.utf8_encode hdrs) file) in
    let _ = send msg in
    let _ = call_io Close fd in ()
  end

val good_handler1 : tgt_handler
let good_handler1 #fl  call_io client req send =
  let req = UBytes.from_bytes req in
  let send : UBytes.bytes -> MIOpi (resexn unit) fl pi mymst = fun x -> send (UBytes.to_bytes x) in
  match parse_http_header req with
  | GET "/" -> (respond #fl send 200 "text/html" (UBytes.utf8_encode "<h1>Hello!</h1>"); Inl ())
  | GET query -> (get_query #fl call_io send query; Inl ())
  | _ -> send (UBytes.utf8_encode (head 401))

let good_main1 = link compiled_webserver good_handler1

let _ = Execute.execute good_main1._2
