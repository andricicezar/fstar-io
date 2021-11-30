module Tests

open FStar.List.Tot
open FStar.List.Tot.Properties
open FStar.Tactics // Also defines forall_intro so place before Classical
open FStar.Classical
open FStar.IndefiniteDescription
open FStar.Calc
open FStar.FunctionalExtensionality
open Util
open Stream
open Itree
open IODiv

let test_1 (s : string) : IODiv string (requires True) (ensures fun _ -> True) =
  let fd = open_file s in
  read fd

let test_1' (s : string) : IODiv string (requires True) (ensures fun _ -> True)
= let fd = open_file s in
  let fd' = open_file s in
  read fd

let test_2 (s : string) : IODiv file_descr (requires True) (ensures fun _ -> True) =
  let msg = test_1 s in
  open_file s

let test (s : string) : IODiv unit (requires True) (ensures fun _ -> True) =
  let fd = open_file s in
  let msg = read fd in
  close fd

let test_ (s : string) : IODiv unit (requires True) (ensures fun r -> terminates r /\ (exists fd msg. ret_trace r == [ EOpenfile s fd ; ERead fd msg ; EClose fd () ]))
= let fd = open_file s in
  let msg = read fd in
  close fd

let test'' (fd : file_descr) : IODiv unit (requires True) (ensures fun _ -> True) =
  let msg = read fd in
  ()

let test_more (fd : file_descr) : IODiv unit (requires True) (ensures fun _ -> True) =
  test'' fd ; test'' fd

let test_more' (fd : file_descr) : IODiv unit (requires True) (ensures fun _ -> True) =
  test'' fd ;
  test'' fd ;
  test'' fd

let test3 (fd : file_descr) : IODiv unit (requires True) (ensures fun _ -> True) =
  let msg = read fd in
  () ; () ; ()

let test' (s : string) : IODiv unit (requires True) (ensures fun _ -> True)
= let fd = open_file s in
  let msg = read fd in
  ()

let test'_ (s : string) : IODiv string (requires True) (ensures fun _ -> True) =
  let fd = open_file s in
  read fd

let open_close_test (s : string) : IODiv unit (requires True) (ensures fun r -> terminates r /\ (exists fd. ret_trace r == [ EOpenfile s fd ; EClose fd () ])) =
  let fd = open_file s in
  close fd

let many_open_test (s : string) : IODiv unit (requires True) (ensures fun r -> terminates r)
= let x = open_file s in
  let y = open_file s in
  ()

let many_open_test' (s : string) : IODiv file_descr (requires True) (ensures fun r -> terminates r) =
  let x = open_file s in
  open_file s

// Fails because it can't infer something (the w??)
// let repeat_open_close_test (s : string) : IODiv unit (requires True) (ensures fun _ -> True) =
//   repeat_inv (fun _ -> open_close_test s) (fun _ -> True)

// Similar problem it seems
// let repeat_pure (t : unit -> unit) : IODiv unit (requires True) (ensures fun r -> True) =
//   repeat_inv t (fun _ -> True)
