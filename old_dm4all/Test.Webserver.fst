module Test.Webserver

open MLInterop
open IOStHist
open FStar.All
open FStar.Tactics
open ExtraTactics


// Case 1. Verified web server tries to enforce pi on
//         plugin 

val allowed_file : string -> bool
let allowed_file fnm = match fnm with
  | "../Makefile" -> false
  | "Demos.fst" -> true
  | _ -> false

val allowed_fd : file_descr -> events_trace -> bool
let rec allowed_fd fd s0 =
  match s0 with
  | [] -> false
  | EOpenfile fnm (Inl fd') :: t -> if fd = fd' then allowed_file(fnm)
                                  else allowed_fd fd t
  | EClose fd' _  :: t -> if fd = fd' then false else allowed_fd fd t
  | _ :: t -> allowed_fd fd t

let pi : check_type = (fun s0 action -> 
  match action with
  | (| Openfile, fnm |) -> allowed_file(fnm)
  | (| Read, fd |) -> allowed_fd fd s0
  | (| Close, fd |) -> allowed_fd fd s0)

// the plugin will be written in GIO (should be ML?)
let plugin_type = (pi:check_type) -> file_descr -> GIO unit pi

// ex1. the webserver register a log for every run of a plugin
// ex2. given an URL, plugin only opens that URL
// ex3. The plugin will pass a file_Descr back to the webserver. What can the webserver assume?
// ex4. Pass a proof to the plugin that a file_descr is open.

let rev_append_rev_append () : Lemma (
  forall (s0 le1 le2:events_trace). ((List.rev le2) @ (List.rev le1) @ s0) ==
     ((List.rev (le1@le2)) @ s0)) =
  let aux (s0 le1 le2:events_trace) : Lemma (
    ((List.rev le2) @ (List.rev le1) @ s0) ==
       ((List.rev (le1@le2)) @ s0)) = begin
    List.rev_append le1 le2;
    List.append_assoc (List.rev le2) (List.rev le1) s0
  end in Classical.forall_intro_3 aux

// import plugin_type 
let webserver (plugin:plugin_type) : GIO unit pi =
  rev_append_rev_append ();
  let fd = pi_static_cmd Openfile pi "Demos.fst" in
  plugin pi fd

let plugin1 : plugin_type = fun pi fd ->
  dynamic_cmd Close pi fd
  
let plugin2 : plugin_type = fun pi fd ->
  let d = dynamic_cmd Read pi fd in
  ()

let plugin3 : plugin_type = fun pi fd ->
  let fd = dynamic_cmd Openfile pi "Demos.fst" in
  let d = dynamic_cmd Read pi fd in
  ()
  
// Q: is this instance mlish?
instance ml_plugin_type : ml plugin_type = { mldummy = () }

// Q: is the export the correct way to actually run webserver
//    or should we write an interpret in ocaml from IOStHist a -> a
val webserver' : plugin_type -> ML unit
let webserver' = export webserver

// an example of export, where we export to ml a library and can
// argue that respects some interesting global pi

let _ = 
  try_with
    (fun _ -> webserver' (plugin1))
    (fun (err:exn) -> 
      match err with
      | IOStHist.GIO_pi_check_failed -> 
          FStar.IO.print_any "plugin1 failed successfully\n\n" 
      | err -> raise err)

let _ = 
  try_with
    (fun _ -> webserver' (plugin2))
    (fun (err:exn) -> 
      match err with
      | IOStHist.GIO_pi_check_failed -> 
          FStar.IO.print_any "plugin2 failed successfully\n\n" 
      | err -> raise err)


let _ = 
  try_with
    (fun _ -> webserver' (plugin3);
      FStar.IO.print_any "plugin3 executed successfully\n\n" )
    (fun (err:exn) -> raise err)












// Case 2. Verified code wants to interact with a
//         verified library and wants to enforce extra pi


// Case 3. ML code wants to interact with verifed code and 
//         and wants to enforce extra pi. (similar with middleware?)
