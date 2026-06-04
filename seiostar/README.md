# Artifact for "Misquoted No More: Securely Extracting F\* Programs with IO"

This contains the artifact associated with the ICFP 2026 submission with the name:
"[Misquoted No More: Securely Extracting F\* Programs with IO]()".

To see how we implemented refinements check the following files:
1. In `QTypes.fst` to see how we added refinements to the supported types
2. In `RQ.TypingRelation.fst` to see how we updated the typing relation:
  a) The typing relation is now indexed by a pre-condition.
  b) The typing rule `QRef` that changes the refinement of a value.
3. In `ExamplesRefs.fst` and `ExamplesIORefinements.fst` to see what
  kind of examples we can do, and `RQ.TypingRelation.Tests.fst` to see
  how the manually written derivations look like.

The extension is still ongoing.
After extending IO\* with refinements, we managed to update compilation and
backtranslation and reprove that SEIO* satisfies RrHP.
The proof of RrHP contains one admitted compatibility lemma that we did not
have time to finish, but should be provable. 

The artifact is admit free.

## Table of Contents
* [List of Claims](#list-of-claims)
* [Installing F* locally](#installing-f-locally)
* [Evaluation Instructions](#evaluation-instructions)
* [License](#license)

## List of Claims

The artifact contains:
* a formalization of the contributions from the paper;
* the mechanized proof of RrHP;
* the running example verifying and compiling, and other examples.

We list where the definitions and theorems of the paper are.

| From the paper | In the artifact |
| -------------- | --------------- |
| **Section 2/3** - Relational quotation | |
| Typing relations for values and computations | `RQ.TypingRelation.fst` as the type constructors `typing` and `typing_io` |
| Events | `Trace.fst` as the type constructor `event` |
| Traces | `Trace.fst` |
| Metaprogram | `RQ.Metaprogram.fst` as function `generate_derivation` |
| **Section 4** - Relating trace-producing semantics | |
| Syntax and semantics of $\lambda_{io}$ | `LambdaIO.fst` as type constructors `exp`, `step`, and `steps` |
| Behaviors of $\lambda_{io}$ expressions | `LogRel.Semantics.fst` as `e_beh` |
| Syntax of $IO^{\star}$ | `IOStar.fst` as type constructor `io` |
| Functor part of predicate transformer monad | `Hist.fst` |
| Semantics of $IO^{\star}$ | `IOStar.fst` as functions `op_wp` and `theta` |
| Behaviors of $IO^{\star}$ computations | `LogRel.Semantics.fst` as `fs_beh` |
| Predicate on types for logical relation | `QTypes.fst` as type constructor `type_quotation` |
| Target-to-source logical relation | `LogRelTargetSource.fst` |
| Source-to-target logical relation | `LogRelSourceTarget.fst` |
| Target-to-source compatibility lemmas | `LogRelTargetSource.CompatibilityLemmas.fst` |
| Source-to-target compatibility lemmas | `LogRelSourceTarget.CompatibilityLemmas.fst` |
| **Section 5** - Proof of RrHP | |
| Compilation model | `RrHP.fst` |
| Theorem 5.2 (compiler correctness) | `RrHP.fst` as `compiler_correctness` (statement) and `proof_compiler_correctness` (proof) |
| Theorem 5.3 (RrHP) | `RrHP.fst` as `rrhp` (statement) and `proof_rrhp` (proof) |
| Backtranslation | `Backtranslation.fst` |
| **Section 7** - Running SEIO* | |
| Compiling from $\lambda_{io}$ to $\lambda_{\square}$ | `lambdabox/LambdaIOToLambdaBox.fst` |
| Compiling running example | `lambdabox/LambdaBoxExamples.fst` |
| Runtime with implementing primitives | `lambdabox/axioms.ml` |
| **More examples** | The other files named as `Examples*.fst` |

## Installing F* locally

The simplest way for OPAM users is to create the `only-fstar` switch:

$ opam switch import only-fstar.export --switch only-fstar

If you want to install F* manually,
you need **exactly** F* version 2026.03.24 to run this artifact — other
versions (older or newer) are not guaranteed to work.
See more details about [how to install F\* here](https://github.com/FStarLang/FStar/blob/master/INSTALL.md).

## Evaluation Instructions

Running `make` succesfully indicates that all files have been verified.
Some warnings are expected, they are benign.

### Verify SEIO\*

**Expected time and memory.**
Around 7 minutes (if running 8 jobs in parallel with `make verify -j 8`).
Requires 4GB of RAM.

**Script for this step.**
After setting up F*, running `make` in this repository should verify the core
formalization. You can pass `-j` to run more jobs in parallel. You can also
inspect the files interactively in VS Code by installing the
fstar-vscode-assistant extension.

```bash
~/seiostar$ make verify
```

Note: `make verify` does **not** verify any of the examples (the
`Examples*.fst`, `RQ.*.Tests*.fst`, and `RunningExample.fst` files) — see
[Verify the examples](#verify-the-examples) below.

**Expected output.**
Should be a long list of files verified by F\*. A few warnings appear
that the name of our `IO` module conflicts with F*'s module,
they are benign and can be ignored.

### Verify the examples

The examples (including `RunningExample.fst`) are verified separately:

```bash
~/seiostar$ make verify-examples
```

**Expected time.**
Around 23 minutes when running a single job (no `-j`).

`RunningExample.fst` is part of this target and requires significantly more
resources than the rest: **32GB of RAM is required** to verify it.

**Checking for lack of axioms.**
To check that we use no axioms or admit any proofs, you can clean the already
built F* modules (by `make clean`) and then run `make validate`. This will run
the build passing the `--report_assumes error` flag to F*. If any unsafe feature
is used, you should see a hard error.

**Opening the files interactively.**
If you installed F* in your system, you should be able just open VS Code in the
`seiostar/` directory and start verifying files interactively. You should have
the [fstar-vscode-assistant](https://github.com/FStarLang/fstar-vscode-assistant/)
extension installed. Make sure `fstar.exe` is in your PATH, or edit the
`fstar_exe` field in the `.fst.config.json` file to the full path of the F*
executable.

### Running the example

The examples can be built by extracting them to Malfunction.
Look in file [RUNNING.md](./RUNNING.md) for instructions on how to do that.

## License
This work is licensed under a
[Creative Commons Attribution 4.0 International License][cc-by].

[![CC BY 4.0][cc-by-image]][cc-by]

[cc-by]: http://creativecommons.org/licenses/by/4.0/
[cc-by-image]: https://i.creativecommons.org/l/by/4.0/88x31.png
