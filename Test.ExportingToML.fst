module Test.ExportingToML

open FStar.All
open Common
open IOStHist
open MLInterop


noeq type io_library_interface = {
  openfile : args Openfile -> ML (res Openfile);
  read : args Read -> ML (res Read);
  close : args Close -> ML (res Close)
} 

let dynamic_io_api (pi:check_type) = {
  openfile = export (dynamic_cmd Openfile pi);
  read = export (dynamic_cmd Read pi);
  close = export (dynamic_cmd Close pi)
}

let somePi : check_type = fun _ _ -> true


// let create_server (io:io_library_interface) = 
//  let socket = io.create_socket () in
//  io.setsockopt socket SO_REUSEADDr true;
//  io.bind socket ip port;
//  io.listen socket limit;
//  io.set_nonblock socket;
//  socket

// let get_client () : IOStHist (option file_descr) = 

// let get_ready_clients clients : IOStHist clients =

// let sendHTTPResponse () : unit =
// let write () : unit = 
// let close () : unit =



let test1 (io:io_library_interface) : ML unit =
  let fd = io.openfile "../Makefile" in
  io.close fd;
  let msg = io.read fd in
  ()


let _ = 
  try_with
    (fun _ -> test1 ())
    (fun (err:exn) -> 
      match err with
      | Contract_failure -> 
          FStar.IO.print_any "\n\ntest1 failed successfully\n\n" 
      | err -> raise err)






// GIO = IOStHist + Invariant + PI + Flag for verifing dynamically
//                                   the default check

let test2 (pi:check_type) : GIO unit pi =
  let fd = mixed_cmd Openfile pi "../Makefile" in
  let msg = mixed_cmd Read pi fd in
  mixed_cmd Close pi fd

val ml_test2 : check_type -> ML unit
let ml_test2 = export test2
  
let pitrue : check_type = (fun _ _ -> true)

let _ = 
  try_with
    (fun _ -> 
      ml_test2 pitrue;
      FStar.IO.print_any "ml_test2 executed successfully with pitrue\n\n" )
    (fun (err:exn) -> raise err)

let test23 () : GIO unit pitrue =
  let fd = pi_static_cmd Openfile pitrue "../Makefile" in
  let msg = pi_static_cmd Read pitrue fd in
  pi_static_cmd Close pitrue fd

val ml_test23 : unit -> ML unit
let ml_test23 = export test23




let pi' : check_type = (fun s0 action -> 
  match action with
  | (| Openfile, fnm |) -> true
  | (| Read, fd |) -> false 
  | (| Close, fd |) -> true)

let _ = 
  try_with
    (fun _ -> ml_test2 pi')
    (fun (err:exn) -> 
      match err with
      | GIO_pi_check_failed -> 
          FStar.IO.print_any "ml_test2 failed successfully with p2\n\n" 
      | err -> raise err)






let test3 (pi:check_type) : GIO unit pi =
  let fd = dynamic_cmd Openfile pi "../Makefile" in
  dynamic_cmd Close pi fd;
  let msg = dynamic_cmd Read pi fd in
  ()

val ml_test3 : check_type -> ML unit
let ml_test3 = export test3

let _ = 
  try_with
    (fun _ -> ml_test3 pitrue)
    (fun (err:exn) -> 
      match err with
      | GIO_default_check_failed -> 
          FStar.IO.print_any "ml_test3 failed successfully with pitrue\n\n" 
      | err -> raise err)





let test4 (pi:check_type) : GIO unit pi =
  let fd = dynamic_cmd Openfile pi "../Makefile" in 
  let msg = mixed_cmd Read pi fd in
  mixed_cmd Close pi fd

val ml_test4 : check_type -> ML unit
let ml_test4 = export test4

let _ = 
  try_with
    (fun _ -> 
      ml_test4 pitrue;
      FStar.IO.print_any "ml_test4 executed successfully with pitrue\n\n" )
    (fun (err:exn) -> raise err)

let _ = 
  try_with
    (fun _ -> ml_test4 pi')
    (fun (err:exn) -> 
      match err with
      | GIO_pi_check_failed -> 
          FStar.IO.print_any "ml_test4 failed successfully with p2\n\n" 
      | err -> raise err)










let test5 (pi:check_type) : GIO unit pi =
  let fd = mixed_cmd Openfile pi "../Makefile" in
  let msg = mixed_cmd Close pi fd in
  dynamic_cmd Close pi fd

val ml_test5 : check_type -> ML unit
let ml_test5 = export test5

let _ = 
  try_with
    (fun _ -> ml_test5 pitrue)
    (fun (err:exn) -> 
      match err with
      | GIO_default_check_failed -> 
          FStar.IO.print_any "ml_test5 failed successfully with pitrue\n\n" 
      | err -> raise err)
