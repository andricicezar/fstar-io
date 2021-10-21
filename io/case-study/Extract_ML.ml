open Common
open FStar_Pervasives
open Types
open Printf

let ml_openfile (file_name, flags, perm) : file_descr maybe =
  try
    let fd = Unix.openfile file_name flags (Z.to_int perm) in
    Inl fd ;
  with err -> print_string "here1"; print_newline (); raise err; Inr err ;;

let ml_read (fd, limit) : (FStar_Bytes.bytes * int) maybe =
  try
    let (_, limit) : (file_descr * int) = Obj.magic (fd, (Stdint.Int32.of_int (256))) in
    print_int limit;
    print_newline ();
    let buff = Bytes.make 256 '\000' in
    let c = Unix.read fd buff 0 limit in
    Inl ((Bytes.to_string buff), c) ;
  with err -> print_string "here2"; print_newline (); raise err; Inr err ;;

let ml_write (fd, message) : unit maybe =
  try 
    let byts = Bytes.of_string message in
    let _ = Unix.write fd byts 0 (Bytes.length byts) in
    Inl () ;
  with err -> print_string "here3"; print_newline (); raise err; Inr err ;;

let ml_close fd : unit maybe =
  try
    Unix.close fd;
    Inl () ;
  with err -> print_string "here4"; print_newline (); raise err; Inr err ;; 

let ml_socket () : file_descr maybe =
  try
    print_string "Socket created\n";
    print_newline ();
    Inl (Unix.socket Unix.PF_INET Unix.SOCK_STREAM 0) ;
  with err -> print_string "here5"; print_newline (); raise err; Inr err ;;

let ml_setsockopt (socket, opt, value) : unit maybe =
  try
    Unix.setsockopt socket opt value;
    Inl () ;
  with err -> print_string "here6"; print_newline (); raise err; Inr err ;;

let ml_bind (socket, address, port) : unit maybe =
  try
    let limit : int = Stdint.Int.of_int (256) in
    print_int limit;
    print_newline ();
    Unix.bind socket (Unix.ADDR_INET(Unix.inet_addr_of_string address, port));
    print_string "Binded ...\n";
    print_newline ();
    Inl () ;
  with err -> print_string "here7"; print_newline (); raise err; Inr err ;;

let ml_setnonblock fd : unit maybe = 
  try
    Unix.set_nonblock fd;
    Inl () ;
  with err -> print_string "here8"; print_newline (); raise err; Inr err ;;

let ml_listen (fd, limit) : unit maybe = 
  try
    print_string "Listening ...\n";
    print_newline ();
    Unix.listen fd limit;
    Inl () ;
  with err -> print_string "here9"; print_newline (); raise err; Inr err ;;

let ml_accept fd : Unix.file_descr maybe = 
  try
    let fd', _ = Unix.accept fd in
    Inl (fd') ;
  with err -> print_string "here10"; print_newline (); raise err; Inr err ;;

let ml_select (l1, l2, l3, t) : (lfds * lfds * lfds) maybe =
  try
    Inl (Unix.select l1 l2 l3 (100.0 /. 1000.0)) ;
  with err -> print_string "here11"; print_newline (); raise err; Inr err ;;

let ml_gettrace () : Free_IO.trace = []

let console_log s =
  print_string s;
  print_string "\n";
  print_newline ();
  ()
