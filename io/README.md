# Artifact for "Securing Verified IO Programs Against Unverified Code in F*"

This repo is the artifact associated with the POPL 24 submission with the same name.
The artifact is packaged as a docker image using a Dockerfile.

## Table of Contents

## List of Claims

## Download and Installation

### Hardware Requirements

To use this artifact, you will need a x86-64 machine capable of running Docker.
If your machine is not x86-64, use a x86-64 Virtual Machine with Docker.

### Download and Installation using Docker

To use this artifact, you will need to install Docker on your machine.
See
[https://docs.docker.com/get-docker/](https://docs.docker.com/get-docker/)
for the installation instructions.

Building the image takes 10 minutes.
```bash
# Build the image
$ docker build -t sciostar .

# Run Image
$ docker run --rm -it --name sciostar sciostar
```

### Download and Installation without Docker

You can clone the [sources of F\*](https://github.com/FStarLang/FStar),
at the tag v2023.09.03 (commit hash `7363057dc7dceb13e39d5afb2b1dd46161314f25`)
and run `opam install .` in the root.
That will take care of compiling and installing F\* into OPAM.

Once installed, if `fstar.exe` is in your $PATH, then running `make`
will verify all modules in this directory. Otherwise, edit the `FSTAR`
variable in the Makefile to point to your F\* binary. You can use `-j`
to run several jobs in parallel.

See more details about [how to install F\* here](https://github.com/FStarLang/FStar/blob/master/INSTALL.md).

## Evaluation Instructions

### Verify SCIO\* 
**Expected time:** around 4 minutes

**Script for this step:**

```bash
~/sciostar$ make verify
```

This command verifies everything in the root folder and the files in
the `case-studies` folder, except the web server.

**Expected outbout** should be a long list of files verified by F\*. A
  few blue warnings appear which can be ignored.

```
fstar.exe --record_hints --use_hints --hint_dir hints --cache_checked_modules --cache_dir .cache  --dep full --warn_error -321 Compiler.Model1.fst Compiler.Model2.fst Compiler.ModelStlc.fst case-studies/Compiler.Model1.Examples.fst case-studies/Compiler.Model2.Examples.fst case-studies/IOLogging.fst case-studies/Zip.fst case-studies/NoState.fst >.depend.mk
fstar.exe --record_hints --use_hints --hint_dir hints --cache_checked_modules --cache_dir .cache  Hist.fst
Verified module: Hist
All verification conditions discharged successfully
...
(Warning 333) Unable to open hints file: hints/NoState.fst.hints; ran without hints
Verified module: NoState
All verification conditions discharged successfully
```

### Verify the Web Server

**Expected time:** around 2 minutes

**Script for this step:**

```bash
~/sciostar/case-studies/webserver$ make verify
```

The sources for the web server and the handlers are in the `case-studies/webserver`
subdirectory. This command verifies the web server and all the handlers.

**Expected outbout** should be a long list of files verified by F\*. A
  few blue warnings appear which can be ignored.

```bash
fstar.exe --include ../.. --record_hints --use_hints --hint_dir hints --cache_checked_modules --cache_dir .cache  MIO.Sig.fst
FStar.Bytes.fsti(0,0-0,0): (Warning 241) Unable to load /home/opam/.opam/4.12/bin/../lib/fstar/.cache/FStar.Bytes.fsti.checked since checked file /home/opam/.opam/4.12/bin/../lib/fstar/.cache/FStar.Bytes.fsti.checked is stale (digest mismatch for FStar.Bytes.fsti); will recheck FStar.Bytes.fsti (suppressing this warning for further modules)
...
StlcHandlers.fst(0,0-0,0): (Warning 247) .cache/StlcHandlers.fst.checked was not written since checked file .cache/Compiler.Languages.fst.checked does not exist
Verified module: StlcHandlers
All verification conditions discharged successfully
```

### Compiling the Web Server

**Expected time:** less than 1 minute

**Script for this step:**

```bash
~/sciostar/case-studies/webserver$ make build
```

By running the previous command in the `case-studies/webserver` subdirectory,
three executables are produced. Each executable is a different variant of the
web server:

  - `out/ws_adversarial.exe` A version of the server linked with a adversarial
    handler that attempt to thwart the specification. The webserver will
    detect the situation and recover. Choose between `main1`-`main5` in
    `AdversarialHandlers.fst` to test different variants.

  - `out/ws_serve_file.exe`: The webserver linked with a "good" handler that
    prints a message.

  - `out/ws_echo.exe`: The webserver linked with a "good" handler that
    simply echoes back the HTTP request to the user.

**Expected outbout** should look like this. Code produced by F\*
  native extraction produces many Warnings which can be ignored.

```bash
fstar.exe --include ../.. --record_hints --use_hints --hint_dir hints --cache_checked_modules --cache_dir .cache  --dep full --warn_error -321 Monitor.fst WebServer.fst AdversarialHandlers.fst GoodHandler1.fst GoodHandler2.fst StlcHandlers.fst >.depend.mk
make extract;
make[1]: Entering directory '/home/opam/sciostar/case-studies/webserver'
fstar.exe --include ../.. --record_hints --use_hints --hint_dir hints --cache_checked_modules --cache_dir .cache  --lax --odir out --codegen OCaml Monitor.fst AdversarialHandlers.fst GoodHandler1.fst GoodHandler2.fst
Extracted module FStar.Pervasives.Native
Extracted module FStar.Preorder
Extracted module FStar.Heap
Extracted module FStar.StrongExcludedMiddle
Extracted module FStar.List.Tot.Base
Extracted module FStar.List.Tot.Properties
Extracted module FStar.List.Tot
...
make[2]: Leaving directory '/home/opam/sciostar/case-studies/webserver'
mv out/CS.exe out/ws_echo.exe
make[1]: Leaving directory '/home/opam/sciostar/case-studies/webserver'
===============================
Successfully built the binaries out/ws_adversarial.exe, out/ws_serve_file.exe and out/ws_echo.exe
```

### Run the Echo variant

In this variant, the web server writes back the message got from the client. To start the web
server, run:
```bash
sciostar/case-studies/webserver$ ./out/ws_echo.exe
```

To connect to the web server, in a different terminal run the following command.
One can open 5 different connections at the same time.
```bash
$ docker exec -it sciostar telnet localhost 81
```

You can write any text and when pressing `Enter`, you should get the message back.
Like this:
```bash
Trying 127.0.0.1...
Connected to localhost.
Escape character is '^]'.
Echo!
Echo!
Connection closed by foreign host.
```

### Run the File Serving example

In this variant, the web server responds to GET HTTP Requests. To start the web
server, run:
```bash
sciostar/case-studies/webserver$ ./out/ws_serve_file.exe
```

To connect to the web server, in a different terminal run the following command.
One can open 5 different connections at the same time.
```bash
$ docker exec -it sciostar curl http://localhost:81/
<h1>Hello!</h1>

$ docker exec -it sciostar curl -I http://localhost:81/etc/passwd
HTTP/1.1 401

$ docker exec -it sciostar curl --output - http://localhost:81/home/opam/sciostar/MIO.Sig.fst

<the contents of the file>
```

This web server should be able to serve files excepts when asked for `/etc/passwd`
because the access control policy prevents opening that file.

### Run the Adversarial example

In this variant, the web server writes always back `HTTP/1.1 400` because it is linked
against an adversarial handler that tries to break the specification. To start the web
server, run:
```bash
sciostar/case-studies/webserver$ ./out/ws_adversarial.exe
```

To connect to the web server, in a different terminal run the following command.
```bash
$ docker exec -it sciostar telnet localhost 81
```

You can write any text and when pressing `Enter`, you should get `HTTP/1.1 400` back.
Like this:
```bash
Trying 127.0.0.1...
Connected to localhost.
Escape character is '^]'.
Echo!
HTTP/1.1 400
Connection closed by foreign host.
```
