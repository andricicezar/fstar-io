module ExamplesIORefinements

open FStar.Tactics
open IOStar

(** Example 1: Erase refinement in IO *)
let simple_erase_ref (x:bool{x == true}) : io (bool) =
  return x

(** Example 2: Preserve refinement in IO *)
let simple_ref_id (x:bool{x == true}) : io (x:bool{x == true}) =
  return x

(** Example 3: Weaken refinement in IO *)
let simple_reref_id (x:bool{x == true}) : io (x:bool{x == true \/ x == false}) =
  return x

(** Example 4: Bind with IO call, then return refined *)
let simple_ref_bind (x:bool{x == true}) : io (y:bool{y == true \/ y == false}) =
  let!@ _ = io_call OOpen "./string" in
  return #(y:bool{y == true \/ y == false}) x

(** Example 5: Bind with conditional returning resexn *)
let simple_ref_bind2 (x:int) : io (resexn nat) =
  let!@ fd = io_call OOpen "./string" in
  return #(resexn nat) (
    if x >= 0
    then Inl x
    else Inr ())

(** Example 6: Return refined true constant *)
let io_ret_ref_true () : io (x:bool{x == true}) =
  return true

(** Example 7: Return refined false constant *)
let io_ret_ref_false () : io (x:bool{x == false}) =
  return false

(** Example 8: Negate refined input in IO *)
let io_negate_ref (x:bool{x == true}) : io (y:bool{y == false}) =
  return (if x then false else true)

(** Example 9: If-then-else with both branches refined false *)
let io_if_both_false (x:bool) : io (y:bool{y == false}) =
  return (if x then false else false)

(** Example 10: Bind with unit, then return refined *)
let io_bind_ret_ref () : io (x:bool{x == true}) =
  let!@ _ = return () in
  return #(x:bool{x == true}) true

(** Example 11: IO call then return refined *)
let io_call_ret_ref () : io (y:bool{y == true}) =
  let!@ _ = io_call OOpen "./file" in
  return #(y:bool{y == true}) true

(** Example 12: Two IO calls then return refined *)
let io_two_calls_ref () : io (y:bool{y == true}) =
  let!@ _ = io_call OOpen "./a" in
  let!@ _ = io_call OOpen "./b" in
  return #(y:bool{y == true}) true

(** Example 13: Inject Inl with refined input in IO *)
let io_inl_ref (x:bool{x == true}) : io (resexn bool) =
  return #(resexn bool) (Inl x)

(** Example 14: Inject Inr (error) in IO *)
let io_inr_ref () : io (resexn bool) =
  return #(resexn bool) (Inr ())

(** Example 15: Return pair with refined input in IO *)
let io_pair_ref (x:bool{x == true}) : io (bool * unit) =
  return (x, ())

(** Example 16: Case analysis returning refined in IO *)
let io_case_ref (x: either bool unit) : io (y:bool{y == false}) =
  match x with
  | Inl _ -> return false
  | Inr _ -> return false

(** Example 17: if!@ with refined result *)
let io_ifbang_ref (x:bool) : io (y:bool{y == true}) =
  if!@ (return x) then return #(y:bool{y == true}) true
  else return #(y:bool{y == true}) true

(** Example 18: match!@ on IO call with refined result *)
let io_matchbang_ref () : io (y:bool{y == true \/ y == false}) =
  match!@ io_call OOpen "./file" with
  | Inl _ -> return #(y:bool{y == true \/ y == false}) true
  | Inr _ -> return #(y:bool{y == true \/ y == false}) false

(** Example 19: Ghost sequencing before IO return *)
assume val q_ref : Type0
let io_ghost_seq (f: (unit -> _:unit{q_ref})) : io (_:unit{q_ref}) =
  return ((f ()) ; ())

(** Example 20: Apply refined callback in IO *)
let io_apply_callback (f:(x:bool{x == true}) -> bool) : io bool =
  return (f true)

assume val valid : string -> Type0

let pure_validate (x:string) (f:(x:string -> y:bool{y ==> valid x})) : (resexn (x:string{valid x})) =
  if f x
  then Inl x
  else Inr ()

let io_validate_simp (x:string) (f:(x:string -> y:bool{y ==> valid x})) : io (resexn (x:string{valid x})) =
  return #(resexn (x:string{valid x})) (
    if f x
    then Inl x
    else Inr ())

let io_validate (f:(x:string -> y:bool{y ==> valid x})) : io (resexn (x:string{valid x})) =
  let!@! fd = io_call OOpen "./file" in
  let!@! data = io_call ORead fd in
  return #(resexn (x:string{valid x})) (
    if f data
    then Inl data
    else Inr ())
