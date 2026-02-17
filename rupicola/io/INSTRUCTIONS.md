To build io_program_exe
-----------------------

Overview
--------
Two opam switches are used:
- `only-fstar`    — default; used for F* checking, `malfunction`, and `ocamlfind` steps
- `only-peregrine`— used only for the Peregrine extraction step via
                    `opam exec --switch=only-peregrine` (already wired in Makefile)

1. Create the only-fstar switch:

$ opam switch import only-fstar.export --switch only-fstar

2. Create the only-peregrine switch (Peregrine + Rocq stack):

$ opam repo add coq-released   https://coq.inria.fr/opam/released      --on-switch only-peregrine
$ opam repo add rocq-released  https://rocq-prover.org/opam/released   --on-switch only-peregrine
$ opam repo add rocq-core-dev  https://rocq-prover.org/opam/core-dev   --on-switch only-peregrine
$ opam repo add rocq-extra-dev https://rocq-prover.org/opam/extra-dev  --on-switch only-peregrine
$ opam switch import only-peregrine.export --switch only-peregrine

Note: all pinned packages (MetaRocq, CertiCoq, CompCert, coq-ceres, …) are
embedded in the export file. First build takes a while.

3. Build (activate only-fstar first):

$ opam switch only-fstar && eval $(opam env)
rupicola/io$ make io_program_exe

The Peregrine step (`io_program_raw.mlf`) runs automatically under
`opam exec --switch=only-peregrine` — no manual switch needed for that step.

4. Test the echo program:

$ echo "hello" | ./io_program_exe
hello
