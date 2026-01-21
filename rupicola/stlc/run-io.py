#!/usr/bin/env python3
"""
Compile and run an STLC IO program end-to-end.

Uses F* --ide to evaluate `red_prog <term>`, then compiles with
Peregrine/malfunction, links with axioms.ml, and runs the result.

Usage:
    ./run-io.py [--lax] [--z3version=X.Y.Z] <file.fst> <io_program_term>

Examples:
    ./run-io.py --lax LambdaBoxExamples.fst io_program
"""

import json
import os
import subprocess
import sys


def fstar_eval(filename, term, lax=True, z3version="4.15.2"):
    """Evaluate an F* term via the IDE protocol. Returns the result string."""
    with open(filename) as f:
        code = f.read()

    fstar_args = ["fstar.exe", filename, "--ide", "--z3version", z3version]
    if lax:
        fstar_args.append("--lax")

    push_query = json.dumps({
        "query-id": "1",
        "query": "push",
        "args": {"kind": "lax" if lax else "full", "code": code, "line": 1, "column": 0},
    })
    compute_query = json.dumps({
        "query-id": "2",
        "query": "compute",
        "args": {"term": term, "rules": ["beta", "delta", "iota", "zeta"]},
    })

    proc = subprocess.Popen(
        fstar_args,
        stdin=subprocess.PIPE,
        stdout=subprocess.PIPE,
        stderr=subprocess.PIPE,
        text=True,
    )
    proc.stdin.write(push_query + "\n")
    proc.stdin.write(compute_query + "\n")
    proc.stdin.close()

    errors, result = [], None
    for line in proc.stdout:
        try:
            resp = json.loads(line)
            if resp.get("kind") == "message" and resp.get("query-id") == "2" \
                    and resp.get("level") == "error":
                errors.append(resp.get("contents", ""))
            if resp.get("kind") == "response" and resp.get("query-id") == "2":
                if resp.get("status") == "success":
                    result = resp.get("response")
                break
        except json.JSONDecodeError:
            pass
    proc.terminate()

    if result is None:
        if errors:
            print("F* error:", file=sys.stderr)
            for e in errors:
                print(e, file=sys.stderr)
        else:
            print("No response from F*", file=sys.stderr)
        sys.exit(1)

    return result


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
    step(1, "F* → LambdaBox AST")
    raw = fstar_eval(filename, f"red_prog {term_name}", lax=lax, z3version=z3version)
    ast_str = raw.strip('"').replace('\\"', '"')
    with open(ast_file, "w") as f:
        f.write(ast_str)
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
