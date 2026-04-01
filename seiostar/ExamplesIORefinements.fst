module ExamplesIORefinements

open FStar.Tactics
open IOStar


let simple_erase_ref (x:bool{x == true}) : io (bool) =
  return x

let simple_ref_id (x:bool{x == true}) : io (x:bool{x == true}) =
  return x

let simple_reref_id (x:bool{x == true}) : io (x:bool{x == true \/ x == false}) =
  return x

let simple_ref_bind (x:bool{x == true}) : io (y:bool{y == true \/ y == false})
  by (dump "H") =
  let!@ _ = io_call OOpen "./string" in
  // F* does not support nested subtyping and if return infers the type 
  // from the argument instead of the return type, we need to annotate
  return #(y:bool{y == true \/ y == false}) x

let simple_ref_bind2 () : io (resexn nat) =
  let!@ fd = io_call OOpen "./string" in
  return #(resexn nat) (
    match fd with
    | Inl fd -> 
      if fd >= 0 
      then Inl fd
      else Inr ()
    | Inr _ -> Inr ())

[@expect_failure]
let connect_refs_to_specs () : io (resexn nat) by (dump "H") =
  let!@ fd : resexn file_descr = io_call OOpen "./string" in
  match fd with
  | Inl fd -> return (Inl (fd <: nat)) // CA: to prove this, one needs to use the postcondition of OOpen, which is not available
  | Inr _ -> return (Inr ())