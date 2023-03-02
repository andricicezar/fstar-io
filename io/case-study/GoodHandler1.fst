module GoodHandler1

open FStar.Ghost
open Compiler.Model

open FStar.Tactics

open Compiler.Model

open WebServer

let tgt_cs_int = comp.comp_int cs_int

type tgt_handler = ctx_tgt tgt_cs_int

let link = comp.target.link #tgt_cs_int

let pi = tgt_cs_int.pi
  
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

let parse_http_header (header : Bytes.bytes) : request_type =
  match Bytes.iutf8_opt header with
  | None -> Error
  | Some header ->
  let h = String.list_of_string header in
  match h with
  | 'G' :: 'E :: 'T' :: ' ' :: tail -> GET (extract_path tail)
  | _ -> Error

let rec send_file 
  (#fl:erased tflag)
  (io_acts:acts fl pi false)
  (send:Bytes.bytes -> MIOpi (resexn unit) fl pi)
  (fd : file_descr) (limit : UInt8.t) :
  MIOpi unit fl pi =
      admit ();
  match io_acts Read (fd,limit) with
  | Inl (chunk, size) -> begin 
    if UInt8.lt size limit then
      let _ = send (Bytes.slice chunk 0ul (UInt32.uint_to_t (UInt8.v size))) in
      ()
    else (
      let _ = send chunk in
      send_file io_acts send fd limit 
    )
  end
  | _ -> ()

let write_string 
  (#fl:erased tflag)
  (send:Bytes.bytes -> MIOpi (resexn unit) fl pi)
  (s:string) : MIOpi unit fl pi =
    admit (); // because of bytes
    let _ = send (Bytes.utf8_encode s) in ()

let write_int 
  (#fl:erased tflag)
  (send:Bytes.bytes -> MIOpi (resexn unit) fl pi)
  (x:int) :
  MIOpi unit fl pi =
  let (s:string) = string_of_int x in
  write_string #fl send s

open FStar.Tactics

let rec lemma1_0 (pi:policy_spec) (h lt1 lt2:trace) : Lemma 
  (requires (enforced_locally pi h lt1 /\ enforced_locally pi (List.rev lt1 @ h) lt2))
  (ensures (enforced_locally pi h (lt1@lt2))) =
  admit ();
  match lt2 with
  | [] -> () 
  | e::tl -> 
    assert (enforced_locally pi h (lt1@[e]));
    assert (enforced_locally pi (List.rev (lt1@[e]) @ h) tl);
    lemma1_0 pi h (lt1@[e]) tl

let lemma1 (pi:policy_spec) : Lemma (
  forall h lt1 lt2. enforced_locally pi h lt1 /\ enforced_locally pi (List.rev lt1 @ h) lt2 ==>
    enforced_locally pi h (lt1@lt2)) =
  Classical.forall_intro_3 (Classical.move_requires_3 (lemma1_0 pi))

let head 
  (#fl:erased tflag)
  (send:Bytes.bytes -> MIOpi (resexn unit) fl pi)
  (status_code:int) :
  MIOpi unit fl pi =
  lemma1 pi;
  write_string #fl send "HTTP/1.1 ";
  write_int #fl send status_code;
  write_string #fl send "\n"  
  
let set_headers 
  (#fl:erased tflag)
  (send:Bytes.bytes -> MIOpi (resexn unit) fl pi)
  (status_code:int) (media_type:string) (content_length: int) : 
  MIOpi unit fl pi =
  lemma1 pi;
  head #fl send status_code;
  write_string #fl send "Content-Length: ";
  write_int #fl send content_length;
  write_string #fl send "\nContent-Type: ";
  write_string #fl send media_type;
  write_string #fl send "\n\n"

let respond
  (#fl:erased tflag)
  (send:Bytes.bytes -> MIOpi (resexn unit) fl pi)
  (status_code:int) (media_type:string) (content:Bytes.bytes) : 
  MIOpi unit fl pi =
  lemma1 pi;
  set_headers #fl send status_code media_type (Bytes.length content);
  let _ = send content in
  ()

let get_fd_stats 
  (#fl:erased tflag)
  (io_acts:acts fl pi false)
  (file_full_path: string) :
  MIOpi (resexn (file_descr * stats)) fl pi =
  let _ = io_acts Access (file_full_path,[R_OK]) in
  let file_stats = io_acts Stat file_full_path in
  let fd = io_acts Openfile (file_full_path,[O_RDONLY],0) in
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
  (io_acts:acts fl pi false)
  (send:Bytes.bytes -> MIOpi (resexn unit) fl pi)
  (file_full_path : string) :
  MIOpi unit fl pi =
  match get_fd_stats io_acts file_full_path with | Inr _ -> () | Inl (fd, stat) -> begin
    lemma1 pi;
    set_headers #fl send 200 (get_media_type file_full_path) (UInt8.v stat.st_size);
    send_file #fl io_acts send fd 100uy;
   
    let _ = io_acts Close fd in ()
  end

val good_handler1 : tgt_handler
let good_handler1 #fl  io_acts client req send =
    lemma1 pi;
  match parse_http_header req with
  | GET "/" -> Inl (respond #fl send 200 "text/html" (Bytes.utf8_encode "<h1>Hello!</h1>"))
  | GET query -> Inl (
    get_query #fl io_acts send query
  ) 
  | _ -> Inl (head #fl send 400)

let good_main1 = link compiled_webserver good_handler1

let _ = Execute.execute good_main1
