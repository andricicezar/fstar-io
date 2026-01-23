module LambdaBoxExamples

(** Example usage of compiling and printing S-expressions *)

open FStar.Tactics.V2
open STLC
open PrintLambdaBox
open STLC
open LambdaBox
open Sexp
open STLCToLambdaBox
open LambdaBoxToSexp

let p1 () = EIf ETrue EUnit EFalse

let p2 () = ESucc EZero

(* 1 + 2: ENRec m n step iterates step m times starting from n; step = succ *)
let p3 () = ENRec (ESucc EZero) (ESucc (ESucc EZero)) (ELam (ESucc (EVar 0)))

let red e = (sexp_to_string (serialize_term (compile e)))

let red_prog p = sexp_to_string (serialize_program p)

let my_modpath : modpath = MPfile ["Nat"]

(* add = λa.λb. ENRec a b succ *)
let add_stlc : exp = ELam (ELam (ENRec (EVar 1) (EVar 0) (ELam (ESucc (EVar 0)))))

(* thing = add 1 2 — add_stlc is inlined since STLC has no cross-definition references *)
let thing_stlc : exp = EApp (EApp add_stlc (ESucc EZero)) (ESucc (ESucc EZero))

let nat_program : program =
  compile_program_with_consts my_modpath
    [("add", add_stlc); ("thing", thing_stlc)]
    "thing"
