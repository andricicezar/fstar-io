module Test.Webserver

open Common
open IO.Free
open IO.Effect
open IIO.Effect
open MIO.Effect
open MIIO.Effect
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

val allowed_fd : file_descr -> trace -> bool
let rec allowed_fd fd s0 =
  match s0 with
  | [] -> false
  | EOpenfile fnm (Inl fd') :: t -> if fd = fd' then allowed_file(fnm)
                                  else allowed_fd fd t
  | EClose fd' _  :: t -> if fd = fd' then false else allowed_fd fd t
  | _ :: t -> allowed_fd fd t

let pi : monitorable_prop = (fun s0 action -> 
  match action with
  | (| Openfile, fnm |) -> allowed_file(fnm)
  | (| Read, fd |) -> allowed_fd fd s0
  | (| Close, fd |) -> allowed_fd fd s0)

// the plugin will be written in GIO (should be ML?)
// let plugin_type = (pi:monitorable_prop) -> file_descr -> IIO file_descr pi (fun _ r le -> Inl? r /\ is_open (Inl?.v r) le)
let plugin_type = file_descr -> IIO file_descr pi (fun _ _ _ -> True)
let ml_plugin_type = file_descr -> MIO file_descr 

// ex1. the webserver register a log for every run of a plugin
// ex2. given an URL, plugin only opens that URL
// ex3. The plugin will pass a file_Descr back to the webserver. What can the webserver assume?
// ex4. Pass a proof to the plugin that a file_descr is open.

let rev_append_rev_append () : Lemma (
  forall (s0 le1 le2:trace). ((List.rev le2) @ (List.rev le1) @ s0) ==
     ((List.rev (le1@le2)) @ s0)) =


  let aux (s0 le1 le2:trace) : Lemma (
    ((List.rev le2) @ (List.rev le1) @ s0) ==
       ((List.rev (le1@le2)) @ s0)) = begin
    List.rev_append le1 le2;
    List.append_assoc (List.rev le2) (List.rev le1) s0
  end in Classical.forall_intro_3 aux

// import plugin_type 
let webserver (plugin:plugin_type) : IIO unit pi (fun _ _ _ ->True) =
  rev_append_rev_append ();
  let fd = pi_static_cmd Openfile pi "Demos.fst" in
  let _ = plugin fd in
  ()

let ml_plugin1 : ml_plugin_type = fun fd ->
  unsafe_cmd Close fd;
  fd
  
let ml_plugin2 : ml_plugin_type = fun fd ->
  let d = unsafe_cmd Read fd in
  fd

let ml_plugin3 : ml_plugin_type = fun fd ->
  let fd = unsafe_cmd Openfile "Demos.fst" in
  let d = unsafe_cmd Read fd in
  fd



let rec handle #t2 (tree : iio (t2)) (pi:monitorable_prop) : IIO t2 pi (fun _ _ _ -> True) = begin
  match tree with
  | Return r -> r 
  | Throw r -> throw r
  | Cont (Call GetTrace argz fnc) ->
      let h = get_trace () in
      FStar.WellFounded.axiom1 fnc (Inl h);
      let z' = fnc (Inl h) in
      handle z' pi
  | Cont (Call cmd argz fnc) ->
      let rez : res cmd = dynamic_cmd cmd pi argz in
      FStar.WellFounded.axiom1 fnc (Inl rez);
      let z' : sys cmds all_sig t2 = fnc (Inl rez) in
      rev_append_rev_append ();
      handle z' pi
end
  
let import_mio
  (a b : Type)
  (pi : monitorable_prop)
  (f : a -> MIO b) :
  Tot (a -> IIO b pi (fun _ _ _ -> True)) =
    fun (x:a) -> 
        let h = get_trace () in
        // Cezar: I don't think this is ok.
        handle (cast_io_iio (reify (f x) h (fun _ _ -> True))) pi

let plugin1 = import_mio _ _ pi ml_plugin1
let plugin2 = import_mio _ _ pi ml_plugin2
let plugin3 = import_mio _ _ pi ml_plugin3

let whole1 () : IIO unit pi (fun _ _ _ -> True) = webserver plugin1
let whole2 () : IIO unit pi (fun _ _ _ -> True) = webserver plugin2
let whole3 () : IIO unit pi (fun _ _ _ -> True) = webserver plugin3

// let _ = 
//   try_with
//     (fun _ -> webserver' (plugin1))
//     (fun (err:exn) -> 
//       match err with
//       | Contract_failure -> 
//           FStar.IO.print_any "plugin1 failed successfully\n\n" 
//       | err -> raise err)

// let _ = 
//   try_with
//     (fun _ -> webserver' (plugin2))
//     (fun (err:exn) -> 
//       match err with
//       | Contract_failure -> 
//           FStar.IO.print_any "plugin2 failed successfully\n\n" 
//       | err -> raise err)


// let _ = 
//   try_with
//     (fun _ -> webserver' (plugin3);
//       FStar.IO.print_any "plugin3 executed successfully\n\n" )
//     (fun (err:exn) -> raise err)












// Case 2. Verified code wants to interact with a
//         verified library and wants to enforce extra pi


// Case 3. ML code wants to interact with verifed code and 
//         and wants to enforce extra pi. (similar with middleware?)