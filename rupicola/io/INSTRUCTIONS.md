To build io_program_exe
-----------------------

1. Add extra repositories as default:

```
$ opam repo add coq-released https://coq.inria.fr/opam/released --set-default
$ opam repo add rocq-extra-dev https://rocq-prover.org/opam/extra-dev --set-default
$ opam repo add rocq-core-dev https://rocq-prover.org/opam/core-dev --set-default
$ opam repo add rocq-released https://rocq-prover.org/opam/released --set-default
```

2. Import switch:
```
$ opam switch import fstar-and-peregrine.export --switch fstar-and-peregrine
```

3. Switch, eval:
```
$ opam switch fstar-and-peregrine
$ eval $(opam env)
```

4. Make and exec:
```
rupicola/io$ make io_program_exe
rupicola/io$ printf '\x02' | ./io_program_exe | xxd
00000000: 01
rupicola/io$ printf '\x00' | ./io_program_exe | xxd
00000000: 00
```
