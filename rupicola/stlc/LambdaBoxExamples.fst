module LambdaBoxExamples

(** Example usage of compiling and printing S-expressions *)

open FStar.Tactics.V2
open STLC
open LambdaBox
open STLCToLambdaBox
open LambdaBoxToSexp
open LambdaBoxMeta

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

(* io_program: prints fact(4) = 24. main = λ_:unit. fact 4 *)
let io_program : program =
  compile_io_program my_modpath
    [("main", ELam (EApp fact_stlc (ESucc (ESucc (ESucc (ESucc EZero))))))]
    "main"

(** Serialise io_program to io_program.ast at compile time.
    Triggered by: fstar.exe --unsafe_tactic_exec LambdaBoxExamples.fst *)
let _ =
  assert True
    by (write_term_to_file "io_program.ast" (`red_prog io_program); trivial ())
