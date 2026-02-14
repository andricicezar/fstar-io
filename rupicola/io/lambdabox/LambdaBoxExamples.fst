module LambdaBoxExamples

(** Example IO programs compiled to LambdaBox.
    These use the IO-extended STLC (with ERead, EWrite, EOpen, EClose, EFileDescr). *)

open FStar.Tactics.V2
open STLC
open LambdaBox
open STLCToLambdaBox
open LambdaBoxToSexp
open LambdaBoxMeta

let my_modpath : modpath = MPfile ["IO"]

(** echo: reads a bool from fd 0, writes it to fd 1.
    Type: unit -> resexn unit
    If the read succeeds (Inl b), write b to fd 1.
    If the read fails (Inr _), return unit. *)
let echo_stlc : exp =
  ELam  (* () *)
    (ECase (ERead (EFileDescr 0))
      (ELam (EWrite (EFileDescr 1) (EVar 0)))  (* Inl b => write b to fd 1 *)
      (ELam EUnit))                            (* Inr _ => unit *)

(** write_true: writes 'true' to fd 1 unconditionally.
    Type: unit -> resexn unit *)
let write_true_stlc : exp =
  ELam (EWrite (EFileDescr 1) ETrue)

(** open_and_read: opens a file (using bool filename), reads a bool from it,
    writes the value to fd 1, then closes the file.
    Type: unit -> resexn unit
    Uses monad-erased sequencing: EApp (ELam continuation) operation.

    De Bruijn stack at each binding (0 = innermost):
      outer ELam:              [unit_arg]
      Inl fd branch ELam:      [fd, unit_arg]
      Inl b  branch ELam:      [b, fd, unit_arg]
      after-write ELam:        [write_result, b, fd, unit_arg]  fd = EVar 2
      Inr-of-read ELam:        [err, fd, unit_arg]             fd = EVar 1 *)
let open_and_read_stlc : exp =
  ELam  (* () *)
    (* EOpen EFalse : resexn file_descr *)
    (ECase (EOpen EFalse)
      (* Inl fd => read from fd, write to stdout, close fd *)
      (ELam
        (* fd = EVar 0 *)
        (ECase (ERead (EVar 0))
          (* Inl b => write b to fd 1, then close fd *)
          (ELam
            (* b = EVar 0; fd = EVar 1 *)
            (EApp
              (* after write: close fd; fd = EVar 2 inside this lambda *)
              (ELam (EClose (EVar 2)))
              (EWrite (EFileDescr 1) (EVar 0))))
          (* Inr _ => close fd; fd = EVar 1 *)
          (ELam (EClose (EVar 1)))))
      (* Inr _ => unit (open failed) *)
      (ELam EUnit))

(** io_program: the echo program.
    main : unit -> resexn unit = echo_stlc *)
let io_program : program =
  compile_io_program my_modpath
    [("main", echo_stlc)]
    "main"

(** Serialise io_program to io_program.ast at compile time.
    Triggered by: fstar.exe --unsafe_tactic_exec LambdaBoxExamples.fst *)
let _ =
  assert True
    by (write_term_to_file "io_program.ast" (`red_prog io_program); trivial ())
