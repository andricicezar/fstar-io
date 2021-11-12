# export PATH := ../z3/bin:$(PATH);
# export PATH := ../FStar/bin:$(PATH);


verify:
	fstar.exe --include ../../.. --include ../.. --include .. Plugin.fst Linker.fst

extract: out
	fstar.exe --include ../../.. --include ../.. --include .. --odir out --codegen OCaml Free.IO.fst Linker.fst

compile: out
	rm -f *.cmx *.cmi *.o out/*.cmx out/*.cmi out/*.o
	cp ../../../Types.* out/.
	cp ../../../TC_Export.* out/.
	cp ../Free_IO_Call.* out/.
	cp ../Unix_Star.* out/.
	ocamlfind opt -package fstarlib -linkpkg -g -I out out/Types.ml out/Common.ml out/Unix_Star.ml out/Free.ml out/Free_IO.ml out/Free_IO_Call.ml out/TC_Checkable.ml out/DM_IO.ml out/DM_IIO.ml out/TC_Export.ml out/TC_Trivialize.ml out/TC_Trivialize_IIOwp.ml out/TC_Trivialize_MIIO.ml out/TC_Weaken.ml out/TC_Weaken_MIIO.ml out/DM_IIO_Primitives.ml out/DM_MIIO.ml out/DM_MIO.ml out/DM.ml out/Hist.ml out/Instrument.ml out/TC_Monitorable.ml out/Model.ml out/Shared.ml out/Plugin.ml out/WebServer.ml out/TC_MLify.ml out/TC_MLify_MIIO.ml out/Linker.ml -o out/Linker.exe
