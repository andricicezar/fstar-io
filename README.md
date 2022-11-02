## Secure Compilation of F★ Programs with IO Against Linked Weakly-Typed Code

## Prerequisites

The code in this repo has been tested on F* - 2022.08.10 version.

##  Inventory of the artifact

**The IIO Dijkstra Monad** and the **source language** are defined in file **IIO.fst**.

**The target language** is defined in file **Compile.MLang.fst**.

**The compilation** is done in multiple stages and can be found in the files: **Compile.IIO.To.ILang.fst**, **Compile.ILang.To.RILang.fst** and **Compile.RILang.To.MLang.fst**.

The criterias are defined in file **Criteria.RILang.To.MLang.fst**.