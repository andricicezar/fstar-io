Supplementary materials for "Securely Compiling Verified F\* Programs with IO"
==============================================================================

To verify these files a recent F\* version is needed. Pre-release
2023.02.01 is known to work. The easiest way to get started is
clone the sources of F\*, at the tag v2023.02.01 (commit hash
`0eeac0892f95756eec45d343a9c62ea44560848e`) and run `opam install .` in
the root. That will take care of compiling and installing F\* into OPAM.

Once installed, if `fstar.exe` is in your $PATH, then running `make`
will verify all modules in this directory. Otherwise, edit the `FSTAR`
variable in the Makefile to point to your F\* binary. You can use `-j`
to run several jobs in parallel.

Compiling the webserver
=======================

The sources for the webserver and plugins are in the `case-study`
subdirectory. To compile the webserver, first verify all the modules
by running `make` in that directory. After that, run `make extract` to
generate the OCaml files. Now you can compile three variants of the
server with the following rules:

  - make compile_cs1: A version of the server linked with a malicious
    handler that attempt to thwart the specification. The webserver will
    detect the situation and recover. Choose between `main1`-`main5` in
    `AdversarialHandlers.fst` to test different variants.

  - make compile_cs2: The webserver linked with a "good" handler that
    prints a message.

  - make compile_cs3: The webserver linked with a "good" handler that
    simply echoes back the HTTP request to the user.

The executables are named `out/CS1.exe`, `out/CS2.exe` and `out/CS3.exe`.

The webserver will listen on port 81, so open http://localhost:81/ on your
browser to see the result. Note: since 81 is a privileged port, you
need to run the server as root (or change the port).
