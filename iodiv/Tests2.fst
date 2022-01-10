module Tests2

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
open IODivHist

// assume val get_trace : unit -> IODiv trace (fun hist -> True) (ensures fun hist r -> terminates r /\ result r == hist)

let test_1 (s : string) : IODiv string (requires fun h -> True) (ensures fun _ _ -> True) =
  let fd = open_file s in
  read fd

let test_1' (s : string) : IODiv string (requires fun _ -> True) (ensures fun _ _ -> True)
= let fd = open_file s in
  let fd' = open_file s in
  read fd

let test_2 (s : string) : IODiv file_descr (requires fun _ -> True) (ensures fun _ _ -> True) =
  let msg = test_1 s in
  open_file s

let test (s : string) : IODiv unit (requires fun _ -> True) (ensures fun _ _ -> True) =
  let fd = open_file s in
  let msg = read fd in
  close fd

let test_ (s : string) : IODiv unit (requires fun _ -> True) (ensures fun hist r -> terminates r /\ (exists fd msg. ret_trace r == [ EOpenfile s fd ; ERead fd msg ; EClose fd () ]))
= let fd = open_file s in
  let msg = read fd in
  close fd

let test'' (fd : file_descr) : IODiv unit (requires fun hist -> is_open fd hist) (ensures fun _ _ -> True) =
  let msg = read fd in
  ()

// Don't know why these fail
// let test_more (fd : file_descr) : IODiv unit (requires fun hist -> is_open fd hist) (ensures fun _ _ -> True) =
//   test'' fd ; test'' fd

// let test_more' (fd : file_descr) : IODiv unit (requires fun hist -> is_open fd hist) (ensures fun _ _ -> True) =
//   test'' fd ;
//   test'' fd ;
//   test'' fd

let test3 (fd : file_descr) : IODiv unit (requires fun hist -> is_open fd hist) (ensures fun _ _ -> True) =
  let msg = read fd in
  () ; () ; ()

let test' (s : string) : IODiv unit (requires fun _ -> True) (ensures fun _ _ -> True)
= let fd = open_file s in
  let msg = read fd in
  ()

let test'_ (s : string) : IODiv string (requires fun _ -> True) (ensures fun _ _ -> True) =
  let fd = open_file s in
  read fd

let open_close_test (s : string) : IODiv unit (requires fun _ -> True) (ensures fun hist r -> terminates r /\ (exists fd. ret_trace r == [ EOpenfile s fd ; EClose fd () ])) =
  let fd = open_file s in
  close fd

let many_open_test (s : string) : IODiv unit (requires fun _ -> True) (ensures fun hist r -> terminates r)
= let x = open_file s in
  let y = open_file s in
  ()

let many_open_test' (s : string) : IODiv file_descr (requires fun _ -> True) (ensures fun hist r -> terminates r) =
  let x = open_file s in
  open_file s

// Fails because it can't infer something (the w??)
// let repeat_open_close_test (s : string) : IODiv unit (requires True) (ensures fun _ -> True) =
//   repeat_inv (fun _ -> open_close_test s) (fun _ -> True)

// Similar problem it seems
// let repeat_pure (t : unit -> unit) : IODiv unit (requires True) (ensures fun r -> True) =
//   repeat_inv t (fun _ -> True)

let test_using_assume (fd : file_descr) : IODiv string (requires fun _ -> True) (ensures fun hist r -> terminates r) =
  assume (forall hist. is_open fd hist) ;
  read fd


// A second test to make sure exfalso isn't used
let test_assume #a #pre (f : unit -> IODiv a (requires fun hist -> pre) (ensures fun hist r -> True)) : IODiv a (fun hist -> True) (fun hist r -> True) =
  assume pre ;
  f ()
