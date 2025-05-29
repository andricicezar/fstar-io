# Artifact for "SecRef*: Securely Sharing Mutable References Between Verified and Unverified Code in F*"

This subdirectory contains the artifact associated with the ____ 2025 submission with the name:
"[SecRef*: Securely Sharing Mutable References Between Verified and Unverified Code in F*](https://arxiv.org/abs/2303.01350)".
TODO: The artifact is packaged using [Docker](https://www.docker.com/) and a VM ....

## Table of Contents
* [List of Claims](#list-of-claims)
* [Download and Installation](#download-and-installation)
   * [Hardware Requirements](#hardware-requirements)
   * [Download and Installation using Docker](#download-and-installation-using-docker)
   * [Download and Installation without Docker](#download-and-installation-without-docker)
* [Evaluation Instructions](#evaluation-instructions)
   * [Verify SCIO\*](#verify-scio)
   * [Verify the Web Server](#verify-the-web-server)
   * [Compiling the Web Server](#compiling-the-web-server)
   * [Run the Echo variant](#run-the-echo-variant)
   * [Run the File Serving variant](#run-the-file-serving-variant)
   * [Run the Adversarial variant](#run-the-adversarial-variant)
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
| --------- | --------------- |
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
|  Robust Relational Hyperproperty Preservation (RrHP) Theorem | The theorem is defined in `BeyondCriteria.fst` as `rrhc` and then it is proved in `Compiler.fst` as `comp1_rrhc` |
| Dual Setting, together with the Soundness-Dual Theorem | Definitions that end with '2' in `Compiler.fst` |
| Syntactic representation of target contexts | `Compiler.STLC.fst` |
| **Section 7. Case study - cooperative multi-threding scheduler** | |
| Implementation of the case study | `CooperativeMultiThreadingWithIndexT.fst` |
| Instantiating SecRef* with the case study | `Examples.CooperativeMultiThreadingWithIndexT.fst` |
| **More examples** | The other files named as `Examples.*.fst` |

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

This directory contains the artifact for SecRef★. The layout is as
follows:
- MST.Repr: Free monad representation
- MST.Tot: MST Effect definition
- Examples.*: Various examples
- misc/: dune configuration files for examples

- fstar-patches/: a set of patches needed for F*, to enable primitive
  extraction of reifiable effects (and fix two bugs).

- extraction/: The extraction plugin for SecRef★. Run `make` inside
  here to build it. It will also be built automatically by the `build-%`
  rule, but *not* rebuilt, so do it manually if you've changed anything
  here or if F* has changed.

You need F* version 2025.02.17 **with the patches** to run this artifact.
A way to get set up is:

  git clone https://github.com/FStarLang/FStar
  cd FStar
  git checkout v2025.02.17
  git am /path/to/artifact/fstar-patches/*.patch
  opam install --deps-only .
  make -j$(nproc) ADMIT=1

After a while, a built F* should be avaiable under in `FStar/bin/fstar.exe`. Add
this directory to your PATH and then run the Makefile here.

You also need Z3 version 4.13.3 in your PATH, named z3-4.13.3 so F* can find it.
The script in `FStar/.scripts/get_fstar_z3.sh` can be used to automatically set it up

  ./FStar/.scripts/get_fstar_z3.sh ~/bin

Should install z3-4.13.3 into your ~/bin (and Z3 4.8.5, though we do not use it).
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

### Verify SecRef\*

**Expected time:** around 4 minutes

**Script for this step:**

After setting up F*, running `make` in this repository should verify
all the F* files in it, including our formalization and examples. You
can also inspect the files interactively in VS Code by installing the
fstar-vscode-assistant extension.

```bash
~/secrefstar$ make verify
```

**Expected outbout** should be a long list of files verified by F\*. A
  few blue warnings appear which can be ignored.

### Running the examples

The examples can be built by using the extraction plugin to extract them
into native OCaml, and then building them with dune. This is process
is a bit complicated so there is a rule in the Makefile to automate it.
Simply run `make build-Examples.Intro` to verify, extract, build, and run
`Examples.Intro.fst`. Other files can be run by replacing `Examples.Intro` for something else.

## Reusability

One can use this artifact in many ways:
* to verify and compile a program by taking advantage of SMT automation;

## License
This work is licensed under a
[Creative Commons Attribution 4.0 International License][cc-by].

[![CC BY 4.0][cc-by-image]][cc-by]

[cc-by]: http://creativecommons.org/licenses/by/4.0/
[cc-by-image]: https://i.creativecommons.org/l/by/4.0/88x31.png
