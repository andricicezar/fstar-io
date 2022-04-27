# export PATH := ../z3/bin:$(PATH);
# export PATH := ../FStar/bin:$(PATH);

verify:
	fstar.exe --include .. Types.fst Common.fst Free.fst Hist.fst DMFree.fst ExtraTactics.fst TC.Checkable.fst TC.Export.fst TC.ML.fst TC.Trivialize.fst TC.Weaken.fst