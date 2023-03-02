Supplementary materials for "Securely Compiling Verified F\* Programs with IO"
==============================================================================

To verify these files a recent F\* version is needed. Pre-release
2023.02.01 is known to work. It can be downloaded from here:

    https://github.com/FStarLang/FStar/releases/tag/v2023.02.01

If `fstar.exe` is in your $PATH, then running `make` will verify all
modules in this directory. Otherwise, edit the `FSTAR` variable in the
Makefile to point to your F\* binary. You can use `-j` to run several
jobs in parallel.

Install via OPAM?


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

The webserver will listen on port 81, so open http://localhost:81/ on your
browser to see the result.
