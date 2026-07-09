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

        $ opam switch import only-peregrine.export --switch only-peregrine

Note: First build takes a while.

3. Build (activate only-fstar first):

        $ opam switch only-fstar && eval $(opam env)
        $ make io_program

The Peregrine step (`io_program_raw.mlf`) runs automatically under
`opam exec --switch=only-peregrine`, no manual switch needed for that step.

4. Test io_program_exe:

        $ echo "foo" > .build/temp
        $ .build/io_program_exe
        true
        $ cat .build/temp
        overwrite

5. Test other agents:

To test other agents, modify the file `lambdabox/LambdaBoxExamples.fst`:

```
let _ =
  assert True
    by (write_term_to_file "io_program.ast" (`(string_of_prog (io_program pt_main write_agent))); trivial ())
```

Replace there `write_agent` by other agents. Compile `io_program_exe`.
