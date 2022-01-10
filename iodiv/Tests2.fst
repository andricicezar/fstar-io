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

unfold
let ret_trace #a (r : branch a) : Pure trace (requires terminates r) (ensures fun _ -> True) =
  match r with
  | Fin tr x -> tr

unfold
let result #a (r : branch a) : Pure a (requires terminates r) (ensures fun _ -> True) =
  match r with
  | Fin tr x -> x

let act_call (o : cmds) (x : io_args o) : IODiv (io_res o) (requires fun hist -> forall y. valid_event hist (choice_to_event (Call_choice o x y))) (ensures fun hist r -> terminates r /\ ret_trace r == [ choice_to_event (Call_choice o x (result r)) ]) =
  IODIV?.reflect (iodiv_call _ o x (fun y -> iodiv_ret _ y))

let open_file (s : string) : IODiv file_descr (requires fun hist -> True) (ensures fun hist r -> terminates r /\ ret_trace r == [ EOpenfile s (result r) ]) =
  act_call Openfile s

let read (fd : file_descr) : IODiv string (requires fun hist -> is_open fd hist) (ensures fun hist r -> terminates r /\ ret_trace r == [ ERead fd (result r) ]) =
  act_call Read fd

let close (fd : file_descr) : IODiv unit (requires fun hist -> is_open fd hist) (ensures fun hist r -> terminates r /\ ret_trace r == [ EClose fd (result r) ]) =
  act_call Close fd

// let repeat_inv #w (body : unit -> IODIV unit w) (inv : (trace -> Type0) { trace_invariant w inv }) : IODIV unit (pwrepeat_inv w inv) =
//   IODIV?.reflect (piodiv_repeat_with_inv (reify (body ())) inv)

assume val get_trace : unit -> IODiv trace (fun hist -> True) (ensures fun hist r -> terminates r /\ result r == hist)

// Have hist in reverse order to help F*
let test_1 (s : string) : IODiv string (requires fun h -> True) (ensures fun _ _ -> True)
by (
  explode () ;
  bump_nth 2 ;
  branch_on_match () ;
  explode () ;
  unfold_def (`is_open) ;
  norm [ iota ] ;
  dump "h"
)
=
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
