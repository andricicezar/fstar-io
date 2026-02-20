# Artifact for "Misquoted No More: Securely Extracting F\* Programs with IO"

This contains the artifact associated with the ICFP 2026 submission with the name:
"[Misquoted No More: Securely Extracting F\* Programs with IO](...)".

The artifact contains an (almost) full formalization of the paper.
In file `RunningExample.fst`, we implement the running example from section 2,
and we use the metaprogram to find the derivation, and then we instantiate the
compilation model from section 6, which shows that it is secure to link the
extracted running example with unverified agents.

The artifact is not fully formalized because of two reasons:
1. We did not manage to finish the proof that the running example
   satisfies the spec presented in section 2.3. We just ran out of time,
   and we think the proof is going to be finished soon.
2. There is an assumption in the metaprogram that generates derivations.
   When testing that the derivation has the expected type,
   we end up testing for equality between types by 
   manually creating a statement of form `t1 == t2`.
   Since we build this statement manually, F* does not register it as
   an equality between types, which prevents us from retyping the derivation.
   Therefore,
   we assume that the successful checking of the statement
   gives us equality between types. (Extraction will fail if the types are not equal)
   We think this it is a situation where
   we did not figure out in time how to use Meta-F* to avoid the assumption.
   We are in contact with the developers of F* to figure out how to get rid of the assumption.

## Table of Contents
* [Setup](#setup)
* [List of Claims](#list-of-claims)
* [Download and Installation](#download-and-installation)
* [Evaluation Instructions](#evaluation-instructions)
* [Reusability](#reusability)
* [License](#license)

## List of Claims

The artifact contains:
* a formalization of the contributions from the paper;
* the mechanized proof of RrHP;
* the running example, and other examples

We list where the definitions and theorems of the paper are.

| From the paper | In the artifact |
| -------------- | --------------- |
| **Section 3** - Relational quotation | |
| **Section 4** - Relating trace-producing semantics  | |
| **Section 5** - Proof of RrHP | |
| **Section 6** - Running SEIO* | |
| **More examples** | The other files named as `Examples.*.fst` |

## Directory layout

The directory layout is as follows:
- `misc/`: dune configuration files for examples

- `extraction/`: The extraction plugin for SecRef★. Run `make` inside
  here to build it. It will also be built automatically by the `build-%`
  rule, but *not* rebuilt, so do it manually if you've changed anything
  here or if F* has changed.

## Installing F* locally

You need F* version 2025.12.15 (or higher) to run this artifact. The easy way to
get set up is:

```bash
opam update
opam install fstar
```

After a while, a built F* should be available in your PATH, via OPAM. If not, make
sure to run `eval $(opam env)`. You can run
```
fstar.exe --version
```
to check that F* is present.

You also need Z3 version 4.13.3 in your PATH, named z3-4.13.3 so F* can find it.
The script in `FStar/.scripts/get_fstar_z3.sh` can be used to automatically set
it up.  The following command:

```
./FStar/.scripts/get_fstar_z3.sh ~/bin
```

Should install z3-4.13.3 into your ~/bin (and Z3 4.8.5, though we do not use
it).  If `~/bin` is not in your $PATH, you can add it, or instead install into a
directory like `/usr/local/bin` (but you will need root privileges).

Once installed, if `fstar.exe` is in your $PATH, then running `make` will verify
all modules in this directory.  You can use `-j` to run several jobs in
parallel.

If you have F* installed somewhere outside of your PATH, you can set the 
environment variable `FSTAR` to its location to use it.

See more details about [how to install F\* here](https://github.com/FStarLang/FStar/blob/master/INSTALL.md).

## Evaluation Instructions

Running `make` succesfully indicates that all files have been verified.
Some warnings are expected, they are benign.

### Verify SEIO\*

**Expected time.**
Around 4 minutes (if running just one job). 

**Script for this step.**
After setting up F*, running `make` in this repository should verify all the F*
files in it, including our formalization and examples. You can pass `-j` to run
more jobs in parallel. You can also inspect the files interactively in VS Code
by installing the fstar-vscode-assistant extension.

```bash
~/seiostar$ make verify
```

**Expected output.**
Should be a long list of files verified by F\*. A few warnings appear, 
they are benign and can be ignored.

**Opening the files interactively.**
If you installed F* in your system, you should be able just open VS Code in the
`seiostar/` directory and start verifying files interactively. You should have
the [fstar-vscode-assistant](https://github.com/FStarLang/fstar-vscode-assistant/)
extension installed. Make sure `fstar.exe` is in your PATH, or edit the
`fstar_exe` field in the `.fst.config.json` file to the full path of the F*
executable.

If you are using the VM, you can SSH into it from VS Code (F1 -> "Remote-SSH:
Connect to Host") and have the same experience. You will have to install the
extension into the VM by going into the VS Code menus.

**Checking for lack of axioms.**
To check that we use no axioms or admit any proofs, you can clean the already
built F* modules (by `make clean`) and then run `make validate`. This will run
the build passing the `--report_assumes error` flag to F*. If any unsafe feature
is used, you should see a hard error.

### Running the examples

The examples can be built by using the extraction plugin to extract them into
native OCaml, and then building them with dune. This is process is a bit
complicated so there is a rule in the Makefile to automate it.  Simply run `make
build-Examples.Intro` to verify, extract, build, and run `Examples.Intro.fst`.
Other files can be run by replacing `Examples.Intro` for something else.  The
target `build-all` will build and run a suite of examples.

## License
This work is licensed under a
[Creative Commons Attribution 4.0 International License][cc-by].

[![CC BY 4.0][cc-by-image]][cc-by]

[cc-by]: http://creativecommons.org/licenses/by/4.0/
[cc-by-image]: https://i.creativecommons.org/l/by/4.0/88x31.png
