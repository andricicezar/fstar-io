To build io_program_exe
-----------------------

Overview
--------
Two opam switches are used:
- `only-fstar`     -- default; used for F* checking, `malfunction`, and `ocamlfind` steps
- `only-peregrine` -- used only for the Peregrine extraction step via
                      `opam exec --switch=only-peregrine` (already wired in Makefile)

1. Create the only-fstar switch:

$ opam switch import only-fstar.export --switch only-fstar

2. Create the only-peregrine switch (Peregrine + Rocq stack):

$ opam switch create only-peregrine ocaml-base-compiler.4.14.2
$ opam repo add coq-released   https://coq.inria.fr/opam/released      --on-switch only-peregrine
$ opam repo add rocq-released  https://rocq-prover.org/opam/released   --on-switch only-peregrine
$ opam repo add rocq-core-dev  https://rocq-prover.org/opam/core-dev   --on-switch only-peregrine
$ opam repo add rocq-extra-dev https://rocq-prover.org/opam/extra-dev  --on-switch only-peregrine
$ opam switch import only-peregrine.export --switch only-peregrine

Note: all pinned packages (MetaRocq, CertiCoq, CompCert, coq-ceres, …) are
embedded in the export file. First build takes a while.

3. Build (activate only-fstar first):

$ opam switch only-fstar && eval $(opam env)
$ make io_program_exe

The Peregrine step (`io_program_raw.mlf`) runs automatically under
`opam exec --switch=only-peregrine`, no manual switch needed for that step.

4. Test io_program_exe:

rupicola/io$ echo "foo" > temp
rupicola/io$ ./io_program_exe
true
rupicola/io$ cat temp
overwrite

5. Test other agents:

To test other agents, modify the file `lambdabox/LambdaBoxExamples.fst`:

```
let _ =
  assert True
    by (write_term_to_file "io_program.ast" (`(red_prog (io_program pt_main write_agent))); trivial ())
```

Replace there `write_agent` by other agents. Compile `io_program_exe`.
