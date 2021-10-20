module Test.DM.IIO

open Common
open DM
open DM.IIO.Primitives

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

let blockRead : monitorable_prop = (fun s0 action ->
  match action with
  | (| Read, _ |) -> false
  | _ -> true)

// This fails because it tries to enforce `blockRead` statically
// but `blockRead` does not allow any readings, therefore it does
// not check.
[@expect_failure]
let testStatic2 () : IIO unit blockRead (fun _ -> True) (fun _ _ _ -> True) =
  let fd = static_cmd Openfile blockRead "../Makefile" in
  if Inl? fd then (** test if Openfile was successful **)
    let msg = static_cmd Read blockRead (Inl?.v fd) in
    let _ = static_cmd Close blockRead (Inl?.v fd) in
    ()
  else ()

let testStatic1 () : IIO unit blockRead (fun _ -> True) (fun _ _ _ -> True) =
  let fd = static_cmd Openfile blockRead "../Makefile" in
  if Inl? fd then (** test if Openfile was successful **)
    let msg = dynamic_cmd Read blockRead (Inl?.v fd) in
    let _ = static_cmd Close blockRead (Inl?.v fd) in
    ()
  else ()

// dynamic_cmd Openfile enforces the default precondition statically
// and the pi dynamically.
let testDynamic1 (pi:monitorable_prop) : IIO unit pi (fun _ -> True) (fun _ _ _ -> True) =
  let fd = dynamic_cmd Openfile pi "../Makefile" in
  (** if the runtime check was successful, and if Openfile was successful **)
  if Inl? fd && Inl? (Inl?.v fd) then
    let msg = dynamic_cmd Read pi (Inl?.v (Inl?.v fd)) in
    let _ = dynamic_cmd Close pi (Inl?.v (Inl?.v fd)) in
    ()
  else ()

// pai daca Openfile merge, atunci se produce Read... ah, pai dynamic_cmd
// poate opri controlul. poate sa vada ca Read e fail si sa nu mai faca nimic
// atata timp cat pi permite asta, nu e o incalcare a lui pi.

let testDynamic2 (pi:monitorable_prop) : IIO unit pi (fun _ -> True) (fun _ _ _ -> True) =
  let fd = dynamic_cmd Openfile pi "../Makefile" in
  (** if the runtime check was successful, and if Openfile was successful **)
  if Inl? fd && Inl? (Inl?.v fd) then
    let _ = dynamic_cmd Close pi (Inl?.v (Inl?.v fd)) in
    let msg = dynamic_cmd Read pi (Inl?.v (Inl?.v fd)) in
    ()
  else ()

let testDynamic3 (pi:monitorable_prop) : IIO unit pi (fun _ -> True) (fun _ _ _ -> True) =
  let fd = dynamic_cmd Openfile pi "../Makefile" in
  (** if the runtime check was successful, and if Openfile was successful **)
  if Inl? fd && Inl? (Inl?.v fd) then
    let _ = dynamic_cmd Close pi (Inl?.v (Inl?.v fd)) in
    let _ = dynamic_cmd Close pi (Inl?.v (Inl?.v fd)) in
    ()
  else ()

