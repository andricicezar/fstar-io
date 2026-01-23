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

let my_modpath : modpath = MPfile ["Nat"]

(* add = λa.λb. ENRec a b succ *)
let add_stlc : exp = ELam (ELam (ENRec (EVar 1) (EVar 0) (ELam (ESucc (EVar 0)))))

(* mult a b = ENRec a 0 (λacc. add b acc)
   Multiplication by repeated addition *)
let mult_stlc : exp =
  ELam (ELam
    (ENRec (EVar 1)
           EZero
           (ELam (EApp (EApp add_stlc (EVar 1)) (EVar 0)))))

(* thing = add 1 2 — add_stlc is inlined since STLC has no cross-definition references *)
let thing_stlc : exp = EApp (EApp add_stlc (ESucc EZero)) (ESucc (ESucc EZero))

(* factorial n = snd (ENRec n (EZero, ESucc EZero) step)
   where step = λp. (succ (fst p), mult (succ (fst p)) (snd p))
   Computes n! by tracking (counter, accumulator) *)
let fact_stlc : exp =
  ELam
    (ESnd
      (ENRec (EVar 0)
             (EPair EZero (ESucc EZero))  (* start: (0, 1) *)
             (ELam
               (EPair
                 (ESucc (EFst (EVar 0)))  (* counter + 1 *)
                 (EApp (EApp mult_stlc (ESucc (EFst (EVar 0)))) (ESnd (EVar 0)))))))  (* (counter+1) * acc *)

(* fact4 = factorial 4 = 24 *)
let fact4_stlc : exp =
  EApp fact_stlc (ESucc (ESucc (ESucc (ESucc EZero))))

(* fibonacci n = fst (ENRec n (EZero, ESucc EZero) step)
   where step = λp. (snd p, add (fst p) (snd p))
   Computes fib(n) by tracking (fib(i), fib(i+1)) *)
let fib_stlc : exp =
  ELam
    (EFst
      (ENRec (EVar 0)
             (EPair EZero (ESucc EZero))  (* start: (0, 1) *)
             (ELam
               (EPair
                 (ESnd (EVar 0))  (* next fib(i) = current fib(i+1) *)
                 (EApp (EApp add_stlc (EFst (EVar 0))) (ESnd (EVar 0)))))))  (* next fib(i+1) = fib(i) + fib(i+1) *)

(* fib6 = fibonacci 6 = 8 *)
let fib6_stlc : exp =
  EApp fib_stlc (ESucc (ESucc (ESucc (ESucc (ESucc (ESucc EZero))))))

let nat_program : program =
  compile_program_with_consts my_modpath
    [("add", add_stlc); ("thing", thing_stlc)]
    "thing"

let factorial_program : program =
  compile_program_with_consts my_modpath
    [("add", add_stlc);
     ("mult", mult_stlc);
     ("fact", fact_stlc);
     ("fact4", fact4_stlc)]
    "fact4"

let fibonacci_program : program =
  compile_program_with_consts my_modpath
    [("add", add_stlc);
     ("fib", fib_stlc);
     ("fib6", fib6_stlc)]
    "fib6"

(* Helper functions *)
let red e = (sexp_to_string (serialize_term (compile e)))

let red_prog p = sexp_to_string (serialize_program p)

(* Test examples *)
let p1 () = EIf ETrue EUnit EFalse

let p2 () = ESucc EZero

(* 1 + 2: ENRec m n step iterates step m times starting from n; step = succ *)
let p3 () = ENRec (ESucc EZero) (ESucc (ESucc EZero)) (ELam (ESucc (EVar 0)))

(* Test multiplication: 2 * 3 = 6 *)
let p4 () = EApp (EApp mult_stlc (ESucc (ESucc EZero))) (ESucc (ESucc (ESucc EZero)))

(* Test factorial: 3! = 6 *)
let p5 () = EApp fact_stlc (ESucc (ESucc (ESucc EZero)))

(* Test fibonacci: fib(6) = 8 *)
let p6 () = EApp fib_stlc (ESucc (ESucc (ESucc (ESucc (ESucc (ESucc EZero))))))
