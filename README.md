This repository bundles the artifacts accompanying the papers and extended abstracts
behind Cezar-Constantin Andrici's PhD thesis, *"Securing Verified Monadic F\* Programs
against Linked Unverified Code"* (Ruhr-Universität Bochum, 2026).

The developments are written in F\* (and one in Rocq/Coq). They concern verifying
programs with side effects using Dijkstra monads, and securely linking such verified
programs with unverified code.

Each project has its own README with the list of claims, build instructions, and a map
from the paper to the code. Please start there.

| Folder | Contents |
| ------ | -------- |
| [`sciostar/`](./sciostar/README.md) | SCIO\* — [Securing Verified IO Programs Against Unverified Code in F\*](https://doi.org/10.1145/3632916), POPL 2024 ([arXiv](https://arxiv.org/abs/2303.01350)) |
| [`secrefstar/`](./secrefstar/README.md) | SecRef\* — [Securely Sharing Mutable References between Verified and Unverified Code in F\*](https://doi.org/10.1145/3747522), ICFP 2025 |
| [`seiostar/`](./seiostar/README.md) | SEIO\* — [Misquoted No More: Securely Extracting F\* Programs with IO](https://doi.org/10.1145/3828689), ICFP 2026 ([arXiv](https://arxiv.org/abs/2602.19973)) |
| [`pdm4all/`](./pdm4all/README.md) | [Partial Dijkstra Monads for All](https://types22.inria.fr/files/2022/06/TYPES_2022_paper_18.pdf), TYPES 2022; in Rocq/Coq, a [submodule](https://github.com/TheoWinterhalter/pdm4all) |
| [`iodiv/`](./iodiv/README.md) | [Verifying non-terminating programs with IO in F\*](https://theowinterhalter.github.io/res/iodiv-hope.pdf), HOPE 2022 |

Two further directories are supporting material: `lib/`, a small shared F\* library of
free monads, Dijkstra monads over them, and histories; and `experiments/`, unpolished
side explorations kept for the record.

## Building

The F\* artifacts depend on F\* **v2026.03.24**; later versions have changed F\*'s theory,
so pin that version if something fails to verify. `pdm4all/` builds with Coq 8.14–8.19
and Equations 1.3.

Because `pdm4all/` is a submodule, clone with `--recurse-submodules`, or run
`git submodule update --init` in an existing clone.

## Contact

Cezar-Constantin Andrici — <https://cezarandrici.com>
