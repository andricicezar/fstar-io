#!/usr/bin/env python3
"""
Evaluate F* expressions using the IDE protocol (like C-c C-s C-e in fstar-mode.el).

Usage:
    ./fstar-eval.py <file.fst> "<expression>"
    ./fstar-eval.py --lax <file.fst> "<expression>"   # skip Z3 verification
"""

import subprocess
import json
import sys


def main():
    args = sys.argv[1:]
    lax = False
    z3version = "4.15.2"  # override default Z3 version check

    while args and args[0].startswith("--"):
        if args[0] == "--lax":
            lax = True
            args = args[1:]
        elif args[0].startswith("--z3version="):
            z3version = args[0].split("=", 1)[1]
            args = args[1:]
        else:
            break

    if len(args) < 2:
        print(f"Usage: {sys.argv[0]} [--lax] [--z3version=X.Y.Z] <file.fst> <expression> [rules]")
        print("  --lax: skip Z3 verification (useful for recursive let)")
        print("  --z3version: override Z3 version check (default: 4.15.2)")
        print("  rules: comma-separated (default: beta,delta,iota,zeta)")
        sys.exit(1)

    filename = args[0]
    term = args[1]
    rules = args[2].split(",") if len(args) > 2 else ["beta", "delta", "iota", "zeta"]

    # Read file content
    with open(filename) as f:
        code = f.read()

    fstar = "fstar.exe"
    fstar_args = [fstar, filename, "--ide", "--z3version", z3version]
    if lax:
        fstar_args.append("--lax")

    # Push the file content first (use 'lax' kind if --lax flag)
    push_kind = "lax" if lax else "full"
    push_query = json.dumps({
        "query-id": "1",
        "query": "push",
        "args": {"kind": push_kind, "code": code, "line": 1, "column": 0}
    })

    # Then compute the term
    compute_query = json.dumps({
        "query-id": "2",
        "query": "compute",
        "args": {"term": term, "rules": rules}
    })

    proc = subprocess.Popen(
        fstar_args,
        stdin=subprocess.PIPE,
        stdout=subprocess.PIPE,
        stderr=subprocess.PIPE,
        text=True
    )

    # Send both queries
    proc.stdin.write(push_query + "\n")
    proc.stdin.write(compute_query + "\n")
    proc.stdin.close()

    # Read responses
    errors = []
    result = None
    for line in proc.stdout:
        try:
            resp = json.loads(line)
            kind = resp.get("kind")
            qid = resp.get("query-id")

            # Collect error messages for our compute query
            if kind == "message" and qid == "2" and resp.get("level") == "error":
                errors.append(resp.get("contents", ""))

            # Final response for compute query
            if kind == "response" and qid == "2":
                if resp.get("status") == "success":
                    result = resp.get("response")
                break
        except json.JSONDecodeError:
            pass

    proc.terminate()

    # Output
    if result is not None:
        print(f"{term}  ↓  {result}")
    elif errors:
        print("Error:", file=sys.stderr)
        for e in errors:
            print(e, file=sys.stderr)
        sys.exit(1)
    else:
        print("No response from F*", file=sys.stderr)
        sys.exit(1)


if __name__ == "__main__":
    main()
