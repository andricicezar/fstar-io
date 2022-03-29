# export PATH := ../z3/bin:$(PATH);
# export PATH := ../FStar/bin:$(PATH);

verify:
	fstar.exe --include ../../.. --include ../.. --include .. WebServer.Compiled.fst 

extract: out
	fstar.exe --include ../../.. --include ../.. --include .. --odir out --codegen OCaml IO.Sig.fst Monitor.fst WebServer.Compiled.fst IUnix.fst

compile: out
	rm -f *.cmx *.cmi *.o out/*.cmx out/*.cmi out/*.o
	cp Linker.* out/.
	cp Plugin.* out/.
	cp ../../../Types.* out/.
	cp ../../../TC_Export.* out/.
	cp ../IO_Sig_Call.* out/.
	cp ../Unix_Star.* out/.
	ocamlfind opt -package fstarlib -linkpkg -g -I out out/Types.ml out/Common.ml out/Unix_Star.ml out/Free.ml out/Hist.ml out/IO_Sig.ml out/Monitor.ml out/IO_Sig_Call.ml out/TC_Checkable.ml out/DMFree.ml out/DM_IO.ml out/DM_IIO.ml out/TC_Export.ml out/TC_Trivialize.ml out/TC_Trivialize_IIOwp.ml out/TC_Weaken.ml out/TC_Weaken_IIOwp.ml out/DM_IIO_Primitives.ml out/TC_MLify.ml out/TC_Monitorable.ml out/TC_Instrumentable.ml out/TC_Instrumentable_IIOwp.ml out/TC_MLify_IIOwp.ml out/DM.ml out/Shared.ml out/Utils.ml out/IUnix.ml out/Plugin.ml out/WebServer.ml out/WebServer_Compiled.ml out/Linker.ml -o out/Linker.exe
