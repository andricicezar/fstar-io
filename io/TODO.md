# TODO:

## Admits
X. `IIO.fst` - assumption in the definition of `dm_giio_bind`.
   should be proved using induction on `v`.

X. `IIO.fst` - admit in definition of `dm_giio_subcomp`

4. `Hist.fst` - admitted lemma `lemma_hist_bind_associativity` (used in `DMFree.fst`)

5. `CommonUtils.fst` - a few admits (not sure if used anymore)

6. `IIO.Behavior.fst` - reify is assumed as a ghost function

7. [Wait for refactoring] `Compiler.IIO.To.ILang.fst` - assumption in definition of `make_rcs_eff`.
   proof by induction on `rcs`?

8. admit in `RunningExample.fst`


## Unfinished extensions
1. Examples - file `Compiler.Examples.fst`

   File broken right now since I made the target context pi-polymorphic.
   I suspect F* has problems in proving automatically that the definitions
   of target contexts are correct because `pi` is ghost.

   The examples are hard to read.

   Not sure if we are satisfied with the examples from the file.

2. **WebServer** - files in `old/case-studies`

   The webserver case study is not on the latest version of the project.
   Tasks:
   - [ ] update & reverify the WebServer in the new IIO effect
   - [ ] define the web server as a source partial program
   - [ ] define request handlers as target contexts
   - [ ] link them together
   Additional tasks:
   - [ ] extract target web server to OCaml

3. **Extraction to OCaml** - extraction to OCaml was not kept updated.

   Not sure if still necessary since it is not part of our secure compilation chain.
   It may be nice for the case study, because then one can run the web server.

   This has two components.
   Tasks:
   - [ ] there is a step that reifies the monad (old code in `old/Compile.MLang.To.Tot.fst`)
   - [ ] F* extraction of F* to OCaml

4. Proving Relation (Hyperproperties) about a source partial program

   File `Hyperproperties.fst`. It is very hard to do and it may be
   a lot of effort in proving one thing about a very small source partial program.

   Challanges:
   - [ ] reasoning about the partial program using reification
   - [ ] reasoning about all the source contexts

5. Noninterference theorems about the context

   The hope is that we can state and prove some noninterference theorems about the context by exploiting the flag-polymorphism / parametricity.

   I stated a non-interference theorem in `Hyperproperties.fst` lemma `ni`.
   TODO:
   - [ ] is it the theorem we want?
   - [ ] can we write it in a more simple way to be easier to prove in F*?
   - [ ] prove


6. Refactoring - file `Compiler.IIO.To.TLang.fst`

   The biggest complaint of the actual implementation is that the solution proposed by me
   to convert the additional logical assumptions (beyond pi) into runtime checks is too
   hard to understand (with which I agree).
   - [ ] Catalin suggested to specialized the `tree` data structure I am using to our problem,
   such that is more obvious how it is used
   - [ ] One has to manually instantiate the `tree` data structure when defining an interface,
   and it was proposed to look into if we can automatize the process by using type classes.

