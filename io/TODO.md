# TODO:

## Admits
1. `Compiler.Model.fst` - there is an assumption in `inst_io_cmds` about `pi`
   implying the intrinsic specification of the IO actions (Cezar)

2. `IIO.fst` - assumption in the definition of `dm_giio_bind`.
   should be proved using induction on `v`.

3. `IIO.fst` - admit in definition of `dm_giio_subcomp`

4. `Hist.fst` - admitted lemma `lemma_hist_bind_associativity` (used in `DMFree.fst`)

5. `Common.fst` - a few admits (not sure if used anymore)

6. `IIO.Behavior.fst` - reify is assumed as a ghost function

7. `Compiler.IIO.To.ILang.fst` - assumption in definition of `make_rcs_eff`.
   proof by induction on `rcs`?


## Unfinished extensions
1. Compilation

2. WebServer

3. Examples

4. Proving Relation (Hyperproperties) about a source partial program

5. Theorems about the context