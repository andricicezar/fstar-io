module Test.Mixing

open FStar.Tactics
open ExtraTactics
open IOStHist 

// GIO is an effect that enforces the 
// default invariant and the pi

// static_cmd <-- only static default_check
// pi_static_cmd <-- static default_check + pi_check
// mixed_cmd <-- static default_check and dynamic pi_check
// dynamic_cmd <-- dynamic default_check + pi_check

// static_cmd Openfile "../Makefile"


let somePi : check_type = (fun s0 action ->
  match action with
  | (| Read, _ |) -> false
  | _ -> true)

[@expect_failure]
let testStatic2 () : GIO unit somePi =
  let fd = pi_static_cmd Openfile somePi "../Makefile" in
  let msg = pi_static_cmd Read somePi fd in
  pi_static_cmd Close somePi fd

let testStatic1 () : GIO unit somePi =
  let fd = pi_static_cmd Openfile somePi "../Makefile" in
  let msg = mixed_cmd Read somePi fd in
  pi_static_cmd Close somePi fd

// mixed_cmd Openfile enforces the default precondition statically
// and the pi dynamically.
let testMixed1 (pi:check_type) : GIO unit pi =
  let fd = mixed_cmd Openfile pi "../Makefile" in
  let msg = mixed_cmd Read pi fd in
  mixed_cmd Close pi fd

[@expect_failure]
let testMixed2 (pi:check_type) : GIO unit pi =
  let fd = mixed_cmd Openfile pi "../Makefile" in
  mixed_cmd Close pi fd;
  let msg = mixed_cmd Read pi fd in
  ()

// dynamic_cmd Openfile enforces both default precondition
// and the pi dynamically.
let testDynMixed1 (pi:check_type) : GIO unit pi =
  let fd = dynamic_cmd Openfile pi "../Makefile" in // fd is fresh, is open
  let msg = mixed_cmd Read pi fd in
  mixed_cmd Close pi fd

let testMixed3 (pi:check_type) : GIO unit pi =
  let fd = mixed_cmd Openfile pi "../Makefile" in
  let msg = mixed_cmd Close pi fd in
  dynamic_cmd Close pi fd

[@expect_failure]
let testMixed4 (pi:check_type) : GIO unit pi =
  let fd = mixed_cmd Openfile pi "../Makefile" in
  dynamic_cmd Close pi fd;
  let msg = mixed_cmd Read pi fd in
  ()

// should verify succesfuly, but throw error at runtime
// because there is a Read fd after a Close.
let testDyn1 (pi:check_type) : GIO unit pi  =
  let fd = dynamic_cmd Openfile pi "../Makefile" in
  dynamic_cmd Close pi fd;
  let msg = dynamic_cmd Read pi fd in
  ()

let testDyn2 (pi:check_type) : GIO unit pi =
  let fd = dynamic_cmd Openfile pi "../Makefile" in
  let msg = dynamic_cmd Read pi fd in
  dynamic_cmd Close pi fd
