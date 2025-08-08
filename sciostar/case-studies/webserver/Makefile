# export PATH := ../z3/bin:$(PATH);
# export PATH := ../FStar/bin:$(PATH);

FSTAR_EXE ?= fstar.exe

# No need to have so many, I just kept the existing list.
# Compiler.Model and Compiler.Examples sounds like a sensible list.
ROOTS := Monitor.fst WebServer.fst AdversarialHandlers.fst GoodHandler1.fst GoodHandler2.fst StlcHandlers.fst

CACHEDIR := .cache
FLAGS += --include ../..
FLAGS += --cache_checked_modules --cache_dir $(CACHEDIR)
FLAGS += $(OTHERFLAGS)

all: verify

%.checked:
	$(IDE_HACK) $(FSTAR_EXE) $(FLAGS) $<
	@$(if $(IDE_HACK),false) # Make it stop the build

include .depend.mk

.depend.mk: $(ROOTS)
	$(FSTAR_EXE) $(FLAGS) --dep full --extract '*' --warn_error -321 $^ -o $@

verify: $(ALL_CHECKED_FILES)

# Make a dependency graph of the modules.
dep.graph:
	$(FSTAR_EXE) $(FLAGS) --dep graph --warn_error -321 $(ROOTS)
	@# Ignore F* library modules:
	sed -i '/-> "fstar_/d' $@
	sed -i '/-> "prims"/d' $@
.PHONY: dep.graph

dep.pdf: dep.graph
	dot -Tpdf $< > $@

# This would be more incremental than the call monolitic call below, but doesn't work
# for some reason.
# extract: $(ALL_ML_FILES)
# %.ml:
#         $(FSTAR_EXE) $(FLAGS) --codegen OCaml $< -o $@

extract:
	$(FSTAR_EXE) $(FLAGS) --lax --odir out --codegen OCaml --extract '*' Monitor.fst AdversarialHandlers.fst GoodHandler1.fst GoodHandler2.fst

_prepare_compilation:
	rm -f *.cmx *.cmi *.o out/*.cmx out/*.cmi out/*.o
	cp ../../UnixTypes.* out/.
	cp Unix_Star.* out/.
	@# Replacing the calling of monad constructors with calls to the Unix library
	cp MIO_Sig_Call.* out/.
	@# Workarounds for F* extraction bugs: https://github.com/FStarLang/FStar/issues/2912
	find out/Compiler_MIO_To_Interm.ml -type f -exec sed -i 's/= fun fl -> fun pi -> fun mst -> fun dcs -> fun d ->/= fun fl -> fun pi -> fun mst -> fun dcs -> fun d -> Obj.magic/g' {} \;
	find out/WebServer.ml -type f -exec sed -i 's/eff_dc ()/eff_dc client/g' {} \;
	find out/WebServer.ml -type f -exec sed -i 's/uu___2 uu___1 uu___/uu___2 (Obj.magic uu___1) uu___/g' {} \;
	find out/WebServer.ml -type f -exec sed -i 's/ fun client ->/ Obj.magic (fun client ->/g' {} \;
	find out/WebServer.ml -type f -exec sed -i 's/CommonUtils.Contract_failure)))))))))$$/CommonUtils.Contract_failure))))))))))/g' {} \;



_compile1:
	$(FSTAR_EXE) --ocamlopt -I out out/UnixTypes.ml out/CommonUtils.ml out/Unix_Star.ml out/Free.ml out/Hist.ml out/MIO_Sig.ml out/TC_Checkable.ml out/DMFree.ml out/MonitorParam.ml out/Monitor.ml out/MIO_Sig_Call.ml out/MIO.ml out/BeyondCriteria.ml out/MIO_Behavior.ml out/Compiler_Languages.ml out/Utils.ml out/Compiler_MIO_To_Interm.ml out/Compiler_Model1.ml out/WebServer.ml out/Execute.ml out/AdversarialHandlers.ml -o out/CS.exe

_compile2:
	$(FSTAR_EXE) --ocamlopt -I out out/UnixTypes.ml out/CommonUtils.ml out/Unix_Star.ml out/Free.ml out/Hist.ml out/MIO_Sig.ml out/TC_Checkable.ml out/DMFree.ml out/MonitorParam.ml out/Monitor.ml out/MIO_Sig_Call.ml out/MIO.ml out/BeyondCriteria.ml out/MIO_Behavior.ml out/Compiler_Languages.ml out/Utils.ml out/Compiler_MIO_To_Interm.ml out/Compiler_Model1.ml out/WebServer.ml out/Execute.ml out/GoodHandler1.ml -o out/CS.exe

_compile3:
	$(FSTAR_EXE) --ocamlopt -I out out/UnixTypes.ml out/CommonUtils.ml out/Unix_Star.ml out/Free.ml out/Hist.ml out/MIO_Sig.ml out/TC_Checkable.ml out/DMFree.ml out/MonitorParam.ml out/Monitor.ml out/MIO_Sig_Call.ml out/MIO.ml out/BeyondCriteria.ml out/MIO_Behavior.ml out/Compiler_Languages.ml out/Utils.ml out/Compiler_MIO_To_Interm.ml out/Compiler_Model1.ml out/WebServer.ml out/Execute.ml out/GoodHandler2.ml -o out/CS.exe

compile_cs1:
	make _prepare_compilation;
	make _compile1;
	mv out/CS.exe out/ws_adversarial.exe

compile_cs2:
	make _prepare_compilation;
	make _compile2;
	mv out/CS.exe out/ws_serve_file.exe

compile_cs3:
	make _prepare_compilation;
	make _compile3;
	mv out/CS.exe out/ws_echo.exe

build:
	make extract;
	make compile_cs1;
	make compile_cs2;
	make compile_cs3;
	@echo "===============================";
	@echo "Successfully built the binaries out/ws_adversarial.exe, out/ws_serve_file.exe and out/ws_echo.exe"
