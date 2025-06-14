# Artifact for "SecRef\*: Securely Sharing Mutable References Between Verified and Unverified Code in F\*"

This subdirectory contains the artifact associated with the ICFP 2025 submission with the name:
"[SecRef\*: Securely Sharing Mutable References Between Verified and Unverified Code in F\*](___)".

## Table of Contents
* [List of Claims](#list-of-claims)
* [Download and Installation](#download-and-installation)
* [Evaluation Instructions](#evaluation-instructions)
* [Reusability](#reusability)
* [License](#license)

## List of Claims

The artifact contains:
* a formalization of the contributions from the paper;
* the mechanized proofs of soundness and of RrHP;
* the verified examples: autograder and PRGN;
* the case study: cooperative multi-threading scheduler
* other examples.

We list where the definitions and theorems of the paper are.

| From the paper | In the artifact |
| -------------- | --------------- |
| **Introduction**  | |
| The intro example. | [Examples.Intro.fst](./Examples.Intro.fst) |
| **Section 2**  | |
| The autograder example. Figure 1. Definitions: `student_hw`, `autograder`, `grade_preorder`, `poly_student_hw`, `unverified_student_hw` | [Examples.Autograder.fst](./Examples.Autograder.fst). Definitions from the paper   |
| The pseudo-number generator example. Figure 4. | [Examples.PRNG.fst](./Examples.PRNG.fst) |
| **Section 3** -  Monotonic State | |
| Definitions from 3.2 | `MST.Repr.fst` and `MST.Tot.fst` |
| Definitions from 3.3 | `MST.Soundness.fst` |
| **Section 4** - Labeled References | |
| Definitions from 4.1 and 4.3 | `LabeledReferences.fsti` |
| Definitions from 4.2. Full ground types | `FullGroundType.fst` |
| **Section 5** | |
| Polymorphic Interfaces. Figure 6. | [PolyIface.fst](./PolyIface.fst) |
| The `exportable` and `importable` type classes, together with instances for importing and exporting functions | `HigherOrderContracts.fst` |
| **Section 6** - Secure Compilation Framework | |
| Compilation Model from Figure 7. Soundness and RrHP Theorems. | `comp1` in `Compiler.fst` |
| Syntactic Equality Law | `syntactic_equality1` in `Compiler.fst` |
| Soundness Theorem | `soundness1` in `Compiler.fst` |
| Robust Relational Hyperproperty Preservation (RrHP) Theorem | The theorem is defined in `BeyondCriteria.fst` as `rrhc` and then it is proved in `Compiler.fst` as `comp1_rrhc` |
| Dual Setting, together with the Soundness-Dual Theorem | Definitions that end with '2' in `Compiler.fst` |
| Syntactic representation of target contexts | `Compiler.STLC.fst` |
| **Section 7. Case study - cooperative multi-threding scheduler** | |
| Implementation of the case study | `CooperativeMultiThreadingWithIndexT.fst` |
| Instantiating SecRef* with the case study | `Examples.CooperativeMultiThreadingWithIndexT.fst` |
| **More examples** | The other files named as `Examples.*.fst` |

## Directory layout

This directory contains the artifact for SecRef★. The layout is as
follows:
- MST.Repr: Free monad representation
- MST.Tot: MST Effect definition
- Examples.*: Various examples
- misc/: dune configuration files for examples

- extraction/: The extraction plugin for SecRef★. Run `make` inside
  here to build it. It will also be built automatically by the `build-%`
  rule, but *not* rebuilt, so do it manually if you've changed anything
  here or if F* has changed.

## Using the provided VM

F* is already configured and set up, you can jump directly
to the [Evaluation Instructions](#evaluation-instructions).

## Download and Installation

You need F* version 2025.06.13 to run this artifact. The easy way to get set up
is:

```bash
git clone https://github.com/FStarLang/FStar
cd FStar
git checkout v2025.06.13
opam install .
```

After a while, a built F* should be avaiable in your PATH, via OPAM. If not, make
sure to run `eval $(opam env)`. You can run
```
fstar.exe --version
```
to check that F* is present.

You also need Z3 version 4.13.3 in your PATH, named z3-4.13.3 so F* can find it.
The script in `FStar/.scripts/get_fstar_z3.sh` can be used to automatically set it up.
The following command:

```
./FStar/.scripts/get_fstar_z3.sh ~/bin
```

Should install z3-4.13.3 into your ~/bin (and Z3 4.8.5, though we do not use it).

Once installed, if `fstar.exe` is in your $PATH, then running `make`
will verify all modules in this directory.
You can use `-j` to run several jobs in parallel.

If you have F* installed somewhere outside of your PATH, you can set the 
environment variable `FSTAR` to its location to use it.

See more details about [how to install F\* here](https://github.com/FStarLang/FStar/blob/master/INSTALL.md).

## Evaluation Instructions

Running `make` succesfully indicates that all files have been verified.
Some warnings about typeclass instantation are expected, they are benign.


### Verify SecRef\*

**Expected time.**
Around 4 minutes (if running just one job). This may
be slower when using QEMU's TCG due to the cost of emulation.

**Script for this step.**
After setting up F*, running `make` in this repository should verify all the F*
files in it, including our formalization and examples. You can pass `-j` to run
more jobs in parallel. You can also inspect the files interactively in VS Code
by installing the fstar-vscode-assistant extension.

```bash
~/secrefstar$ make verify
```

**Expected output.**
Should be a long list of files verified by F\*. A few warnings about typeclass
instantion appear, they are benign and can be ignored.

**Opening the files interactively.**
If you installed F* in your system, you should be able just open VS Code in the
`secrefstar/` directory and start verifying files interactively. You should have
the [fstar-vscode-assistant](https://github.com/FStarLang/fstar-vscode-assistant/)
extension installed.

If you are using the VM, you can SSH into it from VS Code (F1 -> "Remote-SSH: Connect
to Host") and have the same experience. You will have to install the extension
into the VM by going into the VS Code menus.

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
