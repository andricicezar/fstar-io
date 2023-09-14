open Prims
open CommonUtils
open FStar_Pervasives
open Free
open MIO_Sig

let print_string2 str =
   print_string str; 
   flush stdout; true

let print_caller (caller:caller) : unit =
   match caller with
   | Prog -> print_string " Prog "
   | Ctx -> print_string " Ctx "

let print_call0 (caller:caller) (cmd:io_cmds) (arg:Obj.t) (res:Obj.t) : unit =
    match cmd with
    | Openfile -> begin
       print_string "EOpenfile"; print_caller caller;
       print_string "_ ";
       let r : Obj.t resexn = Obj.magic res in 
       match r with
       | Inl fd -> print_string "(Inl "; print_int (Obj.magic fd); print_string ");";
       | Inr err -> print_string "(Inr _);"
    end
    | Read -> begin
       print_string "ERead"; print_caller caller;
       let (fd,size) : UnixTypes.file_descr * int = Obj.magic arg in 
       print_string "(";
       print_int (Obj.magic fd);
       print_string ", ";
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
    | Write ->
       let (fd,msg) : UnixTypes.file_descr * bytes = Obj.magic arg in
       print_string "EWrite"; print_caller caller;
       print_string "(";
       print_int (Obj.magic fd);
       print_string ",\"";
       print_string (Str.global_replace (Str.regexp "[\n\r]") "\\n" (Bytes.to_string msg));
       print_string "\") _;";
    | Close -> begin
       print_string "EClose"; print_caller caller;
       print_int (Obj.magic arg);
       let r : Obj.t resexn = Obj.magic res in 
       match r with
       | Inl fd -> print_string " (Inl _);"
       | Inr err -> print_string " (Inr _);"
    end
    | Socket -> begin
       print_string "ESocket"; print_caller caller;
       print_string "_ ";
       let r : Obj.t resexn = Obj.magic res in 
       match r with
       | Inl fd -> print_string "(Inl _);"
       | Inr err -> print_string "(Inr _);"
    end
    | Setsockopt -> begin
       print_string "ESetsockopt"; print_caller caller;
       print_string "_ ";
       let r : Obj.t resexn = Obj.magic res in 
       match r with
       | Inl fd -> print_string "(Inl _);"
       | Inr err -> print_string "(Inr _);"
    end
    | Bind -> begin
       print_string "EBind"; print_caller caller;
       print_string "_ ";
       let r : Obj.t resexn = Obj.magic res in 
       match r with
       | Inl fd -> print_string "(Inl _);"
       | Inr err -> print_string "(Inr _);"
    end
    | SetNonblock -> begin
       print_string "ESetNonBlock"; print_caller caller;
       print_string "_ ";
       let r : Obj.t resexn = Obj.magic res in 
       match r with
       | Inl fd -> print_string "(Inl _);"
       | Inr err -> print_string "(Inr _);"
    end
    | Listen -> begin
       print_string "EListen"; print_caller caller;
       print_string "_ ";
       let r : Obj.t resexn = Obj.magic res in 
       match r with
       | Inl fd -> print_string "(Inl _);"
       | Inr err -> print_string "(Inr _);"
    end
    | Accept -> begin
       print_string "EAccept"; print_caller caller;
       let r : UnixTypes.file_descr resexn = Obj.magic res in 
       match r with
       | Inl fd -> 
         print_string "_ (Inl "; print_int (Obj.magic fd); print_string ");";
       | Inr err -> print_string "_ (Inr _);"
     end
    | Select ->
       print_string ""
    | Access -> begin
       print_string "EAccess"; print_caller caller;
       print_string "_ ";
       let r : Obj.t resexn = Obj.magic res in 
       match r with
       | Inl fd -> print_string "(Inl _);"
       | Inr err -> print_string "(Inr _);"
    end
    | Stat -> begin
       print_string "EStat"; print_caller caller;
       print_string "_ ";
       let r : Obj.t resexn = Obj.magic res in 
       match r with
       | Inl fd -> print_string "(Inl _);"
       | Inr err -> print_string "(Inr _);"
    end

let print_call (caller:caller) (cmd:io_cmds) (arg:Obj.t) (res:Obj.t) : unit =
   print_call0 caller cmd arg res;
   flush stdout

let print_event (e:event) : unit =
   let (caller, cmd, arg, res) : (caller * io_cmds * Obj.t * Obj.t) = Obj.magic (MIO_Sig.destruct_event e) in
   print_call0 caller cmd arg res

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

let (io_call : caller -> io_cmds -> Obj.t -> (unit, Obj.t resexn) mio) =
  fun caller -> fun cmd -> fun argz ->
    match ml_call cmd argz with
    | exception err ->
      (* error case: *)
      Monitor.update_state caller cmd argz (Obj.magic (Inr err));
      print_call caller cmd argz (Obj.magic (Inr err));
      mio_return () (Inr err)
    | rez ->
      (* success: *)
      Monitor.update_state caller cmd argz (Obj.magic (Inl rez));
      print_call caller cmd argz (Obj.magic (Inl rez));
      mio_return () (Inl rez)

(* old version: if for whatever reason print_call raises an exception
   in the successful case we will get two events logged.

  try
    let rez = ml_call cmd argz in
    Monitor.update_state caller cmd argz (Obj.magic (Inl rez)); 
    print_call caller cmd argz (Obj.magic (Inl rez));
    mio_return () (Inl rez)
  with err ->
    Monitor.update_state caller cmd argz (Obj.magic (Inr err));
    print_call caller cmd argz (Obj.magic (Inr err));
    mio_return () (Inr err)
*)

let (mio_call : unit -> caller -> cmds -> Obj.t -> (unit, unit) mio) =
  fun () -> fun caller -> fun cmd -> fun argz ->
  match cmd with
  | GetTrace -> mio_return () ()
  | GetST -> 
    let s0 = Monitor.get_state () in
    print_string "GetST;";
    flush stdout;
    mio_return () (Obj.magic s0)
  | _ -> Obj.magic (io_call caller cmd argz)
