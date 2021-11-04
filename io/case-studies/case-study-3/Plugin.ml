open Types
open IUnix

let rec _extract_path (header : char list) : char list =
  match header with
    | [] -> []
    | ' ' :: tail -> []
    | h :: tail -> h :: _extract_path tail

let explode s = List.init (String.length s) (String.get s)

let extract_path (header : char list) =
  String.of_seq (List.to_seq (_extract_path header))

type request_type =
| GET : string -> request_type
| Error : request_type

let parse_http_header (header : string) : request_type =
  let h = explode header in
  match h with
  | 'G' :: 'E' :: 'T' :: ' ' :: tail -> GET (extract_path tail)
  | _ -> Error

let rec send_file (fd:file_descr) (client: file_descr) (limit : int) : unit =
  let (chunk, size) = read fd limit in
  if size <= limit then
    write client chunk
  else (
    write client chunk;
    send_file fd client limit 
  )

let write_string (client:file_descr) (s:string) : unit =
    write client s

let write_int (client:file_descr) (x:int) =
  let (s:string) = string_of_int x in
  write_string client s

let head (client:file_descr) (status_code:int) =
  write_string client "HTTP/1.1 ";
  write_int client status_code;
  write_string client "\n"  
  
let set_headers (client:file_descr) (status_code:int) (media_type:string) (content_length: int) =
  head client status_code;
  write_string client "Content-Length: ";
  write_int client content_length;
  write_string client "\nContent-Type: ";
  write_string client media_type;
  write_string client "\n\n"

let respond (client:file_descr) (status_code:int) (media_type:string) (content:string) : unit =
  set_headers client status_code media_type (String.length content);
  write client content
  
let get_fd_stats (file_full_path: string) : (file_descr * stats) =
  access file_full_path [R_OK];
  let file_stats = stat file_full_path in
  let fd = openfile file_full_path [O_RDONLY] (Z.of_int 0) in
  (fd, file_stats)


let get_media_type (file_path : string) : string =
  if String.length file_path >= 3 then
    let extension = String.sub file_path ((String.length file_path)-3) 3 in
    match (explode extension) with
    | 'j' :: 'p' :: 'g' :: _ -> "image/jpg"
    | 't' :: 'm' :: 'l' :: _ -> "text/html"
    | _ -> "text/plain"
  else "text/plain"

let get_query_body (client : file_descr) (file_full_path : string) =
  let fd, stat = get_fd_stats file_full_path in
  set_headers client 200 (get_media_type file_full_path) (stat.st_size);
  send_file fd client 50;
  close fd

let get_query (client : file_descr) (file_full_path : string) =
  get_query_body client file_full_path

let rec read_entire_file_descr (fd:file_descr) (limit:int) =
  let (chunk, size) = read fd limit in
  if size <= limit then begin
    chunk
  end else begin
    let chunk' = (read_entire_file_descr fd limit) in
    chunk^chunk' 
  end

let get_request (client:file_descr) =
  let x : string = read_entire_file_descr client 50 in
  print_string x;
  flush Stdlib.stdout;
  x

let plugin (client:file_descr) : unit =
  match parse_http_header (get_request client) with
  | GET "/" -> (respond client 200 "text/html" "<h1>Hello!</h1>")
  | GET query -> (
    get_query client query
  ) 
  | _ -> (head client 400)
