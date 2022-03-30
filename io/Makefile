# export PATH := ../z3/bin:$(PATH);
# export PATH := ../FStar/bin:$(PATH);

verify:
	fstar.exe --include .. IO.Sig.fst DM.IO.fst DM.IIO.fst DM.IIO.Primitives.fst  TC.Instrumentable.IIOwp.fst TC.Monitorable.Hist.fst TC.Trivialize.IIOwp.fst TC.Weaken.IIOwp.fst Monitor.fst TC.MLify.IIOwp.fst DM.fst

