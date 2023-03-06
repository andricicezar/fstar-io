# TODO

The case study was finished the night before, so there can be a few improvements.

1. Fix extraction of `Compiler.MIO.To.Weak.fst`, F* does not add Obj.magic in some places when extracting this file, thus I had to manually add them and then replace the extracted file with my version (Compiler_MIO_To_Weak.ml).

2. Fix extraction of `Execute.fst`. This file uses `reify` which is not implemented, but this could be easily defined as the identity function during extraction.

3. Add more console logging in `MIO_Sig_Call.ml`, right now there is only a comment about when
`GetTrace` is called, but more information should be logged such that we have a clear picture that the mechanism works as expected.

4. Move MIO.Sig from this folder to the main folder.

5. The file descriptors in OCaml are abstract compared to C++ where they are int. We should make the file_descr type abstract in our code too.