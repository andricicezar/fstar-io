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

let parse_http_header (header : FStar.Bytes.bytes) : request_type =
  match FStar.Bytes.iutf8_opt header with
  | None -> Error
  | Some header ->
  let h = String.list_of_string header in
  match h with
  | 'G' :: 'E :: 'T' :: ' ' :: tail -> GET (extract_path tail)
  | _ -> Error

let rec get_file
  (#fl:erased tflag)
  (call_io:io_lib fl sgm mymst Ctx)
  (fd : file_descr) (limit : UInt8.t)
  (i:nat) :
  MIOpi FStar.Bytes.bytes fl sgm mymst =
  match call_io Read (fd,limit) with
  | Inl (chunk, size) -> begin
    if UInt8.lt size limit || i = 0 then
      FStar.Bytes.sub chunk 0ul (UInt32.uint_to_t (UInt8.v size))
    else (
      FStar.Bytes.append chunk (get_file call_io fd limit (i-1))
    )
  end
  | _ -> FStar.Bytes.utf8_encode ""

(**let write_string
  (#fl:erased tflag)
  (send:FStar.Bytes.bytes -> MIOpi (resexn unit) fl pi)
  (s:string) : MIOpi unit fl pi =
    let _ = send (FStar.Bytes.utf8_encode s) in ()

let write_int
  (#fl:erased tflag)
  (send:FStar.Bytes.bytes -> MIOpi (resexn unit) fl pi)
  (x:int) :
  MIOpi unit fl pi =
  let (s:string) = string_of_int x in
  write_string #fl send s
**)

open FStar.Tactics
open FStar.List.Tot

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
  (send:FStar.Bytes.bytes -> MIOpi (resexn unit) fl sgm mymst)
  (status_code:int) (media_type:string) (content:FStar.Bytes.bytes) :
  MIOpi unit fl sgm mymst =
  let hdrs = set_headers status_code media_type (FStar.Bytes.length content) in
  let msg = (FStar.Bytes.append (FStar.Bytes.utf8_encode hdrs) content) in
  let _ = send msg in
  ()

let get_fd_stats
  (#fl:erased tflag)
  (call_io:io_lib fl sgm mymst Ctx)
  (file_full_path: string) :
  MIOpi (resexn (file_descr * stats)) fl sgm mymst =
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
  (call_io:io_lib fl sgm mymst Ctx)
  (send:FStar.Bytes.bytes -> MIOpi (resexn unit) fl sgm mymst)
  (file_full_path : string) :
  MIOpi unit fl sgm mymst =
  match get_fd_stats call_io file_full_path with | Inr _ -> () | Inl (fd, stat) -> begin
    lemma_append_enforced_locally sgm;
    let hdrs = set_headers 200 (get_media_type file_full_path) (UInt8.v stat.st_size) in
    let file = get_file #fl call_io fd 255uy 10000 in
    let msg = (FStar.Bytes.append (FStar.Bytes.utf8_encode hdrs) file) in
    let _ = send msg in
    let _ = call_io Close fd in ()
  end

val good_handler1 : tgt_handler
let good_handler1 #fl  call_io client req send =
  match parse_http_header req with
  | GET "/" -> (respond #fl send 200 "text/html" (FStar.Bytes.utf8_encode "<h1>Hello!</h1>\n"); Inl ())
  | GET query -> (get_query #fl call_io send query; Inl ())
  | _ -> send (FStar.Bytes.utf8_encode (head 401))

let good_main1 = link compiled_webserver good_handler1

let _ = Execute.execute good_main1._2
