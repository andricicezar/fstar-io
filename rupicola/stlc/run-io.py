#!/usr/bin/env python3
"""
Compile and run an STLC IO program end-to-end.

Step 1 uses an F* tactic (write_term_to_file in MetaLambdabox.fst) to
serialise the LambdaBox AST to a file during type-checking.  The remaining
steps compile and run the result with Peregrine/malfunction.

Usage:
    ./run-io.py [--lax] [--z3version=X.Y.Z] <file.fst> <io_program_term>

Examples:
    ./run-io.py --lax LambdaBoxExamples.fst io_program
"""

import os
import subprocess
import sys


def run(cmd):
    print(f"  $ {' '.join(cmd)}", flush=True)
    subprocess.run(cmd, check=True)


def main():
    args = sys.argv[1:]
    lax = True  # default: skip Z3 (needed for recursive let)
    z3version = "4.15.2"

    while args and args[0].startswith("--"):
        if args[0] == "--lax":
            lax = True
        elif args[0] == "--strict":
            lax = False
        elif args[0].startswith("--z3version="):
            z3version = args[0].split("=", 1)[1]
        else:
            print(f"Unknown flag: {args[0]}", file=sys.stderr)
            sys.exit(1)
        args = args[1:]

    if len(args) < 2:
        print(f"Usage: {sys.argv[0]} [--lax|--strict] [--z3version=X.Y.Z] <file.fst> <term>")
        sys.exit(1)

    filename, term_name = args[0], args[1]

    script_dir = os.path.dirname(os.path.abspath(__file__))
    os.chdir(script_dir)

    ast_file = f"{term_name}.ast"
    mlf_file = f"{term_name}_raw.mlf"
    cmx_file = f"{term_name}_raw.cmx"
    exe_file = f"{term_name}_exe"

    step = lambda n, msg: print(f"=== Step {n}: {msg} ===", flush=True)

    # Step 1: F* → LambdaBox AST
    # The write_term_to_file tactic in MetaLambdabox.fst evaluates
    # `red_prog io_program` at type-checking time and writes the result
    # directly to io_program.ast via launch_process.
    step(1, "F* → LambdaBox AST")
    fstar_cmd = ["fstar.exe", "--unsafe_tactic_exec", "--z3version", z3version, filename]
    run(fstar_cmd)
    print(f"  Written {ast_file}", flush=True)

    # Step 2: Peregrine → Malfunction
    step(2, "Peregrine → Malfunction")
    run(["peregrine", "ocaml", ast_file, "-o", mlf_file])

    # Step 3: Compile axioms module
    step(3, "Compile axioms.ml")
    run(["ocamlfind", "ocamlopt", "-c", "axioms.ml"])

    # Step 4: Compile generated malfunction
    step(4, f"Compile {mlf_file}")
    run(["malfunction", "cmx", mlf_file])

    # Step 5: Link
    step(5, f"Link → {exe_file}")
    run(["ocamlfind", "ocamlopt", "-linkpkg", "axioms.cmx", cmx_file, "-o", exe_file])

    # Step 6: Run
    step(6, "Run")
    subprocess.run([f"./{exe_file}"], check=True)


if __name__ == "__main__":
    main()
