# Artifact for "Misquoted No More: Securely Extracting F\* Programs with IO"

This contains the artifact associated with the ICFP 2026 submission with the name:
"[Misquoted No More: Securely Extracting F\* Programs with IO](...)".

The artifact contains an (almost) full formalization of the paper.
SEIO* is fully formalized, including the proof that SEIO* is secure (that it satisfies RrHP).
In file `RunningExample.fst`, we implement the running example from section 2,
and we use the metaprogram to find the derivation, and then we instantiate the
compilation model from section 6, which shows that it is secure to link the
extracted running example with unverified agents.

The artifact contains two assumptions that are not relevant to the formalization of SEIO*:
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
| **Section 2/3** - Relational quotation | |
| Typing relations for values and computations | `QExp.fst` as the type constructors `oval_quotation` and `oprod_quotation` |
| Events | `IO.fst` as the type constructor `event` |
| Local traces | `IO.fst` |
| Metaprogram | `Metaprogram.fst` as function `generate_derivation` |
| **Section 4** - Relating trace-producing semantics | |
| Syntax and semantics of $\lambda_{io}$ | `STLC.fst` as type constructors `exp`, `step`, and `steps` |
| Behaviors of $\lambda_{io}$ expressions | `QTyp.fst` as `e_beh` |
| Syntax of $IO^{\star}$ | `IO.fst` as type constructor `io` |
| Functor part of predicate transformer monad | `Hist.fst` |
| Semantics of $IO^{\star}$ | `IO.fst` as functions `op_wp` and `theta` |
| Behaviors of $IO^{\star}$ computations | `QTyp.fst` as `fs_beh` |
| Predicate on types for logical relation | `QTyp.fst` as type constructor `type_quotation` |
| Target-to-source logical relation | `LogRelTargetSource.fst` |
| Source-to-target logical relation | `LogRelSourceTarget.fst` |
| Target-to-source compatibility lemmas | `LogRelTargetSource.CompatibilityLemmas.fst` |
| Source-to-target compatibility lemmas | `LogRelSourceTarget.CompatibilityLemmas.fst` |
| **Section 5** - Proof of RrHP | |
| Compilation model | `RrHP.fst` |
| RrHP | `RrHP.fst` |
| Backtranslation | `Backtranslation.fst` |
| **Section 6** - Running SEIO* | |
| Compiling from $\lambda_{io}$ to $\lambda_{\square}$ | `lambdabox/STLCToLambdaBox.fst` |
| Compiling running example | `lambdabox/LambdaBoxExamples.fst` |
| Runtime with implementing primitives | `lambdabox/axioms.ml` |
| **More examples** | The other files named as `Examples.*.fst` |

## Installing F* locally

Two opam switches are used:
- `only-fstar`     -- default; used for F* checking, `malfunction`, and `ocamlfind` steps

1. Create the only-fstar switch:

$ opam switch import only-fstar.export --switch only-fstar

If you want to install F* manually,
You need F* version 2025.12.15 (or higher) to run this artifact.
See more details about [how to install F\* here](https://github.com/FStarLang/FStar/blob/master/INSTALL.md).

## Evaluation Instructions

Running `make` succesfully indicates that all files have been verified.
Some warnings are expected, they are benign.

### Verify SEIO\*

**Expected time.**
Around 10 minutes (if running 8 jobs in parallel). 

**Script for this step.**
After setting up F*, running `make` in this repository should verify all the F*
files in it, including our formalization and examples. You can pass `-j` to run
more jobs in parallel. You can also inspect the files interactively in VS Code
by installing the fstar-vscode-assistant extension.

```bash
~/seiostar$ make verify
```

**Expected output.**
Should be a long list of files verified by F\*. A few warnings appear
that the name of our `IO` module conflicts with F*'s module,
they are benign and can be ignored.
Also logs from the metaprogram appear.

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

### Running the example

The examples can be built by extracting them to Malfunction.
Look in file [RUNNING.md](./RUNNING.md) for instructions on how to do that.

## License
This work is licensed under a
[Creative Commons Attribution 4.0 International License][cc-by].

[![CC BY 4.0][cc-by-image]][cc-by]

[cc-by]: http://creativecommons.org/licenses/by/4.0/
[cc-by-image]: https://i.creativecommons.org/l/by/4.0/88x31.png
