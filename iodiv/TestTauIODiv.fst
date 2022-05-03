module TestTauIODiv

open FStar.List.Tot
open FStar.List.Tot.Properties
open FStar.Tactics // Also defines forall_intro so place before Classical
open FStar.Classical
open FStar.IndefiniteDescription
open FStar.Calc
open FStar.FunctionalExtensionality

open Util
open Stream
open IIOSig
open IIOSigSpec
open TauIODiv
open DivFree
open DivFreeTauSpec
open DivFreeTauDM

let open_file (s : string) : IODiv file_descr (requires fun hist -> True) (ensures fun hist r -> terminates r /\ ret_trace r == [ EOpenfile s (result r) ]) =
  act_call Openfile s

let read (fd : file_descr) : IODiv string (requires fun hist -> is_open fd hist) (ensures fun hist r -> terminates r /\ ret_trace r == [ ERead fd (result r) ]) =
  act_call Read fd

let close (fd : file_descr) : IODiv unit (requires fun hist -> is_open fd hist) (ensures fun hist r -> terminates r /\ ret_trace r == [ EClose fd ]) =
  act_call Close fd

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
  let _ = read fd in
  close fd

let test_ (s : string) : IODiv unit (requires fun _ -> True) (ensures fun hist r -> terminates r /\ (exists fd msg. ret_trace r == [ EOpenfile s fd ; ERead fd msg ; EClose fd ])) =
  let fd = open_file s in
  let msg = read fd in
  close fd

let test'' (fd : file_descr) : IODiv unit (requires fun hist -> is_open fd hist) (ensures fun hist r -> terminates r /\ is_open fd (rev_acc (ret_trace r) hist)) =
  let msg = read fd in
  ()

let test_more (fd : file_descr) : IODiv unit (requires fun hist -> is_open fd hist) (ensures fun _ _ -> True) =
  test'' fd ; test'' fd

let test_more' (fd : file_descr) : IODiv unit (requires fun hist -> is_open fd hist) (ensures fun _ _ -> True) =
  test'' fd ;
  test'' fd ;
  test'' fd

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

let open_close_test (s : string) : IODiv unit (requires fun _ -> True) (ensures fun hist r -> terminates r /\ (exists fd. ret_trace r == [ EOpenFile s fd ; EClose fd ])) =
  let fd = open_file s in
  close fd

let many_open_test (s : string) : IODiv unit (requires fun _ -> True) (ensures fun hist r -> terminates r)
= let x = open_file s in
  let y = open_file s in
  ()

let many_open_test' (s : string) : IODiv file_descr (requires fun _ -> True) (ensures fun hist r -> terminates r) =
  let x = open_file s in
  open_file s

let repeat_open_close_test (s : string) : IODiv unit (requires fun _ -> True) (ensures fun _ _ -> True) =
  repeat_with_inv #(fun _ -> True) #(fun _ -> True) (fun _ -> open_close_test s)

let repeat_pure (t : unit -> unit) : IODiv unit (requires fun hist -> True) (ensures fun hist r -> True) =
  repeat_with_inv #(fun hist -> True) #(fun tr -> True) t

// Afterwards find an example with a real invariant
let repeat_more (fd : file_descr) : IODiv unit (requires fun hist -> is_open fd hist) (ensures fun hist r -> diverges r)
= repeat_with_inv #(fun hist -> is_open fd hist) #(fun tr -> True) (fun _ -> let s = read fd in ())

let test_using_assume (fd : file_descr) : IODiv string (requires fun _ -> True) (ensures fun hist r -> terminates r) =
  assume (forall hist. is_open fd hist) ;
  read fd

// A second test to make sure exfalso isn't used
let test_assume #a #pre (f : unit -> IODiv a (requires fun hist -> pre) (ensures fun hist r -> True)) : IODiv a (fun hist -> True) (fun hist r -> True) =
  assume pre ;
  f ()

let test_assert p : IODiv unit (requires fun hist -> p) (ensures fun hist r -> True) =
  assert p

let partial_match (l : list nat) : IODiv unit (requires fun hist -> l <> []) (ensures fun hist r -> True) =
  match l with
  | x :: r -> ()

let partial_match_io (l : list string) : IODiv file_descr (requires fun hist -> l <> []) (ensures fun hist r -> True) =
  match l with
  | s :: _ -> open_file s

let partial_match_pre (l : list nat) : IODiv nat (requires fun hist -> l <> []) (ensures fun hist r -> terminates r /\ result r == hd l) =
  match l with
  | x :: r -> x

// Cezar's tests

assume val p : prop
assume val p' : prop
assume val pure_lemma (_ : unit) : Lemma p
assume val some_f (_ : squash p) : IODiv unit (requires fun _ -> True) (ensures fun _ _ -> True)
assume val some_f' : unit -> IODiv unit (requires fun _ -> p) (ensures fun _ _ -> p')

let pure_lemma_test () : IODiv unit (requires fun _ -> True) (ensures fun _ _ -> True) =
  pure_lemma () ;
  some_f ()

let pure_lemma_test2 () : IODiv unit (requires fun _ -> True) (ensures fun _ _ -> True) =
  pure_lemma () ;
  some_f () ;
  some_f' () ;
  assert p'
