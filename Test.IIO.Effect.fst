module Test.IIO.Effect

open Common
open IO.Free
open IO.Effect
open IIO.Effect

let rec is_open (fd:file_descr) (h: trace) :
  Tot bool =
  match h with
  | [] -> false
  | h :: tail -> match h with
               | EOpenfile _ (Inl fd') ->
                   if fd = fd' then true
                   else is_open fd tail
               | EClose fd' _ ->
                    if fd = fd' then false
                    else is_open fd tail
               | _ -> is_open fd tail

let somePi : monitorable_prop = (fun s0 action ->
  match action with
  | (| Read, _ |) -> false
  | _ -> true)

// This fails because it tries to enforce `somePi` statically
// but `somePi` does not allow any readings, therefore it does
// not check.
[@expect_failure]
let testStatic2 () : IIO unit somePi (fun _ -> True) (fun _ _ _ -> True) =
  let fd = static_cmd Openfile somePi "../Makefile" in
  let msg = static_cmd somePi Read fd in
  static_cmd Close somePi fd

let testStatic1 () : IIO unit somePi (fun _ -> True) (fun _ _ _ -> True) =
  let fd = static_cmd somePi Openfile "../Makefile" in
  let msg = dynamic_cmd somePi Read fd in
  static_cmd somePi Close fd

// dynamic_cmd Openfile enforces the default precondition statically
// and the pi dynamically.
let testDynamic1 (pi:monitorable_prop) : IIO unit pi (fun _ -> True) (fun _ _ _ -> True) =
  let fd = dynamic_cmd pi Openfile "../Makefile" in
  let msg = dynamic_cmd pi Read fd in
  dynamic_cmd pi Close fd

let testDynamic2 (pi:monitorable_prop) : IIO unit pi (fun _ -> True) (fun _ _ _ -> True) =
  let fd = dynamic_cmd pi Openfile "../Makefile" in
  dynamic_cmd pi Close fd;
  let msg = dynamic_cmd pi Read fd in
  ()

let testDynamic3 (pi:monitorable_prop) : IIO unit pi (fun _ -> True) (fun _ _ _ -> True) =
  let fd = dynamic_cmd pi Openfile "../Makefile" in
  let msg = dynamic_cmd pi Close fd in
  dynamic_cmd pi Close fd

