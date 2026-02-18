module RunningExample

open IO
open Metaprogram
open ExamplesIO

val validate : string -> string -> string -> bool
let validate olds ts news = true
 // news = olds ^ ts

let read_file (f : string) : io (resexn string) =
  let!@! fd = openfile f in
  read fd

val wrapper : string -> string -> (string -> string -> io unit) -> io (resexn unit)
let wrapper f task agent =
  let!@! contents = read_file f in
  let!@ () = agent f task in
  let!@! new_contents = read_file f in
  if validate contents task new_contents
  then io_return (Inl ())
  else io_return (Inr ())

%splice_t[tgt_wrapper] (meta_translation "tgt_wrapper" [`read_file;`wrapper])

val good_agent_aux : string -> string -> io (resexn unit)
let good_agent_aux fn task =
  let!@! fd = openfile fn in
  let!@! data = read fd in
  write (fd, data ^ task)

val good_agent : string -> string -> io unit
let good_agent fn task =
  let!@ r = good_agent_aux fn task in
  io_return ()

let test () =
  wrapper "bla" "st" good_agent

val simpler_test : unit -> io (resexn unit)
let simpler_test () =
  let!@! contents = read_file "todo" in
  io_return (Inl ())

let ignored_test () =
  let _ = simpler_test () in
  ()

let smol () =
  io_return ()

let open2_read_write () =
  let!@! fd1 = openfile "/tmp/input" in
  let!@! fd2 = openfile "/tmp/output" in
  let!@! data = read fd1 in
  write (fd2, data)

%splice_t[tgt_smol] (meta_translation "tgt_smol" [`smol])

%splice_t[tgt_test] (meta_translation "tgt_test" [`ignored_test])

%splice_t[tgt_simtest] (meta_translation "tgt_simtest" [`simpler_test])

%splice_t[tgt_readfile] (meta_translation "tgt_readfile" [`read_file])

%splice_t[tgt_open2_read_write] (meta_translation "tgt_open2_read_write" [`open2_read_write])

val simpler_test_inlined : unit -> io (resexn unit)
let simpler_test_inlined () =
  (* Inlining read_file *)
  let!@! fd = openfile "todo" in
  let!@! contents = read fd in
  io_return (Inl ())

%splice_t[tgt_simtest_inl] (meta_translation "tgt_simtest_inl" [`simpler_test_inlined])

val wrapper_inlined : string -> string -> (string -> string -> io unit) -> io (resexn unit)
let wrapper_inlined f task agent =
  let!@! fd = openfile f in
  let!@! contents = read fd in
  let!@ () = agent f task in
  let!@! new_fd = openfile f in
  let!@! new_contents = read new_fd in
  if validate contents task new_contents
  then io_return (Inl ())
  else io_return (Inr ())

// [@expect_failure]
//%splice_t[tgt_wrapper] (meta_translation "tgt_wrapper" [`wrapper])

// So slow it seems to slow down my laptop
// %splice_t[tgt_wrapper_inl] (meta_translation "tgt_wrapper_inl" [`wrapper_inlined])

// [@expect_failure]
// %splice_t[tgt_test] (meta_translation "tgt_test" [`test])
