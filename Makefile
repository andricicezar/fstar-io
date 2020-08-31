FSTAR_HOME=../../..
include ../../Makefile.include

UsageTests: out Demos.fst
	$(FSTAR) $(FSTAR_DEFAULT_ARGS) --include .. --odir out --codegen OCaml Demos.fst
	$(OCAMLOPT) -I out out/Common.ml out/Sys_Free.ml out/IO_Free.ml IO_ML.ml out/IOHist.ml out/IOStHist.ml out/GIO.ml out/MLInterop.ml out/Demos.ml -o out/Demos.exe

include $(FSTAR_HOME)/ulib/ml/Makefile.include
