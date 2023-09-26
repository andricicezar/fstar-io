# TODO

The case study was finished the night before, so there can be a few improvements.

- [ ] Eliminate admits / assumptions (please search for admit/assume).

- [ ] What the deal with the `--compat_pre_core 1` flag? Can we get rid of it?

- [x] Eliminate the idealized check

- [ ] The Monitor.fst file depends on the mymst definition that is in Utils.fst (a file with definitions relevant only for the web server, where mymst is the state used for running the web server). I think that the Monitor.fst should be a standalone file that is parametric in the definitions, and somehow the compiler should pass these to it.

- [ ] Fix extraction of `Webserver.fst`. The `eff_rc fd` line is extracted as `eff_rc ()`. https://github.com/FStarLang/FStar/issues/2912

- [ ] Fix extraction of `WebServer.fst`. The `help_import` extracts badly

- [ ] Fix extraction of `Compiler.MIO.To.Interm.fst`, F* does not add Obj.magic in some places when extracting this file, thus I had to manually add them and then replace the extracted file with my version (Compiler_MIO_To_Interm.ml).

- [x] Fix extraction of `Execute.fst`. This file uses `reify` which is not implemented, but this could be easily defined as the identity function during extraction.

- [x] Add more console logging in `MIO_Sig_Call.ml`, right now there is only a comment about when
`GetTrace` is called, but more information should be logged such that we have a clear picture that the mechanism works as expected. CA: I added logs for each IO operations, but it is not clear how to log in a non-invasive way what contracts are enforced and if they succeed or fail. However, the logs of the IO operations give enough information to be confident that things work as expected.

- [ ] Move MIO.Sig from this folder to the main folder.

~~- [ ] The file descriptors in OCaml are abstract compared to C++ where they are int. We should make the file_descr type abstract in our code too. CA: obsolete~~