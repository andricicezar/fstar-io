(* Based on file FStar/examples/metatheory/StlcStrongDbParSubst.fst *)

module STLC

open FStar.Tactics
open FStar.Tactics.Typeclasses
open FStar.List.Tot

type typ =
  | TArr  : typ -> typ -> typ
  | TUnit : typ

type var = nat

type exp =
  | EUnit : exp
  | ELam  : typ -> exp -> exp
  | EVar  : var -> exp
  | EApp  : exp -> exp -> exp

class compile_typ (s:Type0) = {
  [@@@no_method] t : typ
}

instance compile_typ_unit : compile_typ unit = { t = TUnit }
instance compile_typ_arrow s1 s2 {| c1:compile_typ s1 |} {| c2:compile_typ s2 |} : compile_typ (s1 -> s2) =
  { t = TArr c1.t c2.t }

// Some tests
let test0 : compile_typ (unit) = solve
let _ = assert (test0.t == TUnit)
let test1 : compile_typ (unit -> unit) = solve
let _ = assert (test1.t == (TArr TUnit TUnit))
let test2 : compile_typ ((unit -> unit) -> (unit -> unit)) = solve
let _ = assert (test2.t == TArr (TArr TUnit TUnit) (TArr TUnit TUnit))
// stress test
let test3 : compile_typ ((unit -> unit) -> (unit -> unit)-> (unit -> unit)-> (unit -> unit)-> (unit -> unit)-> (unit -> unit)-> (unit -> unit)-> (unit -> unit)-> (unit -> unit)-> (unit -> unit)-> (unit -> unit)-> (unit -> unit)-> (unit -> unit)-> (unit -> unit)-> (unit -> unit)) = solve

class compile_exp (#a:Type0) (s:a) (varn:nat) = {
  [@@@no_method] t : exp
}

assume val get_v : y:var -> a:Type0 -> a
(** CA: this is an abstraction that helps with dealing with
   variables **)

instance compile_exp_unit n : compile_exp () n = {
  t = EUnit
}

let test_unit : compile_exp () 0 = solve

instance compile_exp_var (#a:Type) n (i:nat{i <= n}) : compile_exp (get_v i a) n = {
    t = EVar (n-i)
  }

instance compile_exp_lambda
  (n:nat)
  (#a:Type) {| ca: compile_typ a |}
  (#b:Type)
  (f:a -> b) {| cf: (compile_exp (f (get_v (n+1) a)) (n+1)) |}
  : compile_exp (fun x -> f x) n = {
  t = ELam ca.t cf.t
}

let test1_exp : compile_exp #(unit -> unit) (fun x -> ()) 0 =
  solve
let _ = assert (test1_exp.t == ELam TUnit (EUnit))

let test2_exp : compile_exp #(unit -> unit) (fun x -> x) 0 =
  solve
let _ = assert (test2_exp.t == ELam TUnit (EVar 0))

let test3_exp : compile_exp #(unit -> unit -> unit) (fun x y -> x) 0 =
  solve
let _ = assert (test3_exp.t == ELam TUnit (ELam TUnit (EVar 1)))

let test4_exp : compile_exp #(unit -> unit -> unit) (fun x y -> y) 0 =
  solve
let _ = assert (test4_exp.t == ELam TUnit (ELam TUnit (EVar 0)))

instance compile_exp_app
  (n:nat)
  (#a:Type)
  (#b:Type)
  (f:a -> b) {| c1: compile_exp f n |}
  (x:a)     {| c2: compile_exp x n |}
  : compile_exp (f x) n = {
  t = EApp (c1.t) (c2.t)
}

let test0_fapp : compile_exp ((fun x y -> y) () ()) 0 =
  solve
let _ = assert (test0_fapp.t == EUnit)

(** How to deal with top level definitions? **)

val myf : unit -> unit
let myf () = ()

(* It seems that it just unfolds the definition of myf, which is pretty cool **)
let test1_topf : compile_exp (myf ()) 0 =
  solve
let _ = assert (test1_topf.t == EApp (ELam TUnit EUnit) EUnit)

val myf2 : unit -> unit -> unit
let myf2 x y = x

(* Also handles partial application. Pretty amazing! *)
let test2_topf : compile_exp (myf2 ()) 0 =
  solve
let _ = assert (test2_topf.t == EApp (ELam TUnit (ELam TUnit (EVar 1))) EUnit)

(**
To avoid unfolding top level definitions,
I suppose one could use tactics.
One would start with an empty environment and then compile definitons one by one,
and after each one the environment is extended
and a new instance is defined in the style of `compile_exp_f`.
**)

instance compile_exp_myf n : compile_exp myf n = {
  t = (EVar n) (** CA: `n` because I assume that `f` is the first in the environment **)
}

let test1_fapp : compile_exp (myf ()) 0 =
  solve
let _ = assert (test1_fapp.t == EApp (EVar 0) EUnit) by (compute(); dump "H")

assume val tt1 : unit
instance compile_exp_tt1 (n:nat{n >= 1}) : compile_exp tt1 n = { t = (EVar (n-1)) }

assume val tt2 : unit
instance compile_exp_tt2 (n:nat{n >= 2}) : compile_exp tt2 n = { t = (EVar (n-2)) }

assume val tt3 : unit
instance compile_exp_tt3 (n:nat{n >= 3}) : compile_exp tt3 n = { t = (EVar (n-3)) }


let test2_fapp : compile_exp (let x = tt1 in myf x) 3 =
  solve

let _ = assert (test2_fapp.t == EApp (EVar 3) (EVar 2)) by (compute (); dump "H")

(** CA: is this useful? F* seems to get rid of lets:
    Probably even this is interpreted as `f x` instead of the let.
instance compile_exp_let
  (n:nat)
  (#a:Type) {| ca: compile_typ a |}
  (#b:Type)
  (f:a -> b) {| cf: compile_exp (f (get_v (n+1) a)) (n+1) |}
  (x:a)     {| cx: compile_exp x n |}
  : compile_exp (let x' = x in f x') n = {
  t = EApp (ELam ca.t cf.t) cx.t
}

let test3_fapp : compile_exp (let x = tt1 in f x) 3 =
  solve
let _ = assert (test3_fapp.t == EApp (EVar 3) (EVar 2)) by (compute (); dump "H")
 **)
