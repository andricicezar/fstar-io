module TestUniverse

open FStar.Universe


#set-options "--print_universes"

assume type m : Type u#a -> Type u#(max 1 a)

type typ =
| TUnit : typ
| TArr : typ -> typ -> typ

let rec el (t:typ) : Type u#1 =
  match t with
  | TUnit -> raise_t unit
  | TArr t1 t2 -> (el t1 -> m (el t2))

open FStar.Tactics

(** I get this: **)
let _ =
  assert ((raise_t u#0 u#1 unit -> m (raise_t u#0 u#1 unit)) == el (TArr TUnit TUnit)) by (compute ())

(** but this is what I would like to get: **)
[@expect_failure] (* flag just to make the entire file check *)
let _ =
  assert ((unit -> m unit) == el (TArr TUnit TUnit)) by (compute ())
