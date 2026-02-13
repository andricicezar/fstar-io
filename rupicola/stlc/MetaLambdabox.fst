module MetaLambdabox

(**

  Tactic utilities for writing F* values to files at type-checking time.

  Why not FStar.IO?
  -----------------
  FStar.IO functions (open_write_file, write_string, close_write_file) carry
  `ML` effect.  The `Tac` effect is based on `DIV`, below `ML` in the effect
  lattice, with no automatic sub-effect lift.  The two practical alternatives:

  1. `launch_process` (used here): a built-in tactic that spawns a shell.
     Requires `--unsafe_tactic_exec` on the fstar.exe command line.

  2. Native tactics (`[@@plugin]`): compile the module to OCaml first, then
     load with `--load MetaLambdabox`.  In a native plugin the OCaml effect
     system is erased so FStar.IO is freely callable.

*)

open FStar.Tactics.V2

(** Write [content] to [filename] at tactic (compile) time.
    Content is passed via stdin to avoid shell-quoting issues with arbitrary
    strings.  Requires --unsafe_tactic_exec. *)
let write_file (filename : string) (content : string) : Tac unit =
  let _ = launch_process "sh" ["-c"; "cat > '" ^ filename ^ "'"] content in
  ()

(** Normalise the term [t] fully, expect a string constant, and write that
    string to [filename].  Use this to serialise an F* value to a file at
    compile time.

    Example (in a module that imports MetaLambdabox and STLCToLambdaBox):
      let _ = assert True by
        (write_term_to_file "out.ast" (`red_prog my_program); trivial ()) *)
let write_term_to_file (filename : string) (t : term) : Tac unit =
  let g = top_env () in
  let t' = norm_term_env g [delta; iota; zeta_full; primops; unascribe] t in
  match inspect t' with
  | Tv_Const (C_String s) -> write_file filename s
  | _ -> fail "write_term_to_file: term did not reduce to a string constant"
