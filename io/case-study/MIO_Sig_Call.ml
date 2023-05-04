open Prims
open CommonUtils
open FStar_Pervasives
open MIO_Sig

let print_string2 str =
   print_string str; 
   flush stdout; true

let print_caller (caller:bool) : unit =
   if caller then print_string " Prog "
   else print_string " Ctx "

let print_event (e:event) : unit =
    match e with
       | EOpenfile (caller, arg, res) ->
          print_string "EOpenfile"; print_caller caller;
          print_string "_ _;"
       | ERead (caller, arg, res) -> begin
          print_string "ERead"; print_caller caller;
          let (fd,size) : UnixTypes.file_descr * int = Obj.magic arg in 
          print_string "(";
          print_int (Obj.magic fd);
          print_string "\", ";
          print_int (Obj.magic size);
          print_string ") ";
          let r : (bytes * int) resexn = Obj.magic res in 
          match r with
          | Inl (msg, size) -> begin
            print_string "(Inl (\"";
            print_string (Str.global_replace (Str.regexp "[\n\r]") "\\n" (Bytes.to_string msg));
            print_string "\",";
            print_int (Obj.magic size);
            print_string "));"
          end
          | Inr _ -> print_string "(Inr _);"
        end
       | EWrite (caller, arg, res) ->
          let (fd,msg) : UnixTypes.file_descr * bytes = Obj.magic arg in
          print_string "EWrite"; print_caller caller;
          print_string "(";
          print_int (Obj.magic fd);
          print_string ",\"";
          print_string (Str.global_replace (Str.regexp "[\n\r]") "\\n" (Bytes.to_string msg));
          print_string "\") _;";
       | EClose (caller, arg, res) ->
          print_string "EClose"; print_caller caller;
          print_int (Obj.magic arg);
          print_string " _;";
       | ESocket (caller, arg, res) ->
          print_string "ESocket _ _;"; print_caller caller;
          print_string "_ _;"
       | ESetsockopt (caller, arg, res) ->
          print_string "ESetsockopt"; print_caller caller;
          print_string "_ _;"
       | EBind (caller, arg, res) ->
          print_string "EBind"; print_caller caller;
          print_string "_ _;"
       | ESetNonblock (caller, arg, res) ->
          print_string "ESetNonBlock"; print_caller caller;
          print_string "_ _;"
       | EListen (caller, arg, res) ->
          print_string "EListen"; print_caller caller;
          print_string "_ _;"
       | EAccept (caller, arg, res) -> begin
          print_string "EAccept"; print_caller caller;
          let r : UnixTypes.file_descr resexn = Obj.magic res in 
          match r with
          | Inl fd -> 
            print_string "_ (Inl "; print_int (Obj.magic fd); print_string ");";
          | Inr err -> print_string "_ (Inr _);"
        end
       | ESelect (caller, arg, res) ->
          print_string ""
       | EAccess (caller, arg, res) ->
          print_string "EAccess"; print_caller caller;
          print_string "_ _;"
       | EStat (caller, arg, res) ->
          print_string "EStat"; print_caller caller;
          print_string "_ _;"

let rec print_trace0 (t:trace) : unit =
  match t with
  | e::tl -> print_event e; print_trace0 tl
  | [] -> ()


let print_trace (t:trace) : unit=
  print_string "[";
  print_trace0 (List.rev t);
  print_string"]\n";
  flush stdout


let ml_call (cmd:io_cmds) : Obj.t -> Obj.t =
  match cmd with
  | Openfile -> Obj.magic (Obj.repr Unix_Star.openfile)
  | Read -> Obj.magic (Obj.repr Unix_Star.read)
  | Write -> Obj.magic (Obj.repr Unix_Star.write)
  | Close -> Obj.magic (Obj.repr Unix_Star.close)
  | Socket -> Obj.magic (Obj.repr Unix_Star.socket)
  | Setsockopt ->
      Obj.magic (Obj.repr Unix_Star.setsockopt)
  | Bind -> Obj.magic (Obj.repr Unix_Star.bind)
  | SetNonblock ->
      Obj.magic (Obj.repr Unix_Star.setnonblock)
  | Listen -> Obj.magic (Obj.repr Unix_Star.listen)
  | Accept -> Obj.magic (Obj.repr Unix_Star.accept)
  | Select -> Obj.magic (Obj.repr Unix_Star.select)
  | Access -> Obj.magic (Obj.repr Unix_Star.access)
  | Stat -> Obj.magic (Obj.repr Unix_Star.stat)

let (io_call : bool -> io_cmds -> Obj.t -> (Obj.t resexn) mio) =
  fun caller -> fun cmd -> fun argz ->
  try
    let rez = ml_call cmd argz in
    Monitor.update_trace caller cmd argz (Obj.magic (Inl rez)); 
    mio_return (Inl rez)
  with err ->
    Monitor.update_trace caller cmd argz (Obj.magic (Inr err));
    mio_return (Inr err)


let (mio_call : bool -> cmds -> Obj.t -> unit mio) =
  fun caller -> fun cmd -> fun argz ->
  match cmd with
  | GetTrace -> 
    print_string "Accessing trace...\n";
    let h = Monitor.get_trace () in
    print_trace h;
    flush stdout;
    mio_return (Obj.magic h)
  | _ -> Obj.magic (io_call caller cmd argz)
