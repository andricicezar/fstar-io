# export PATH := ../z3/bin:$(PATH);
# export PATH := ../FStar/bin:$(PATH);

FSTAR_EXE ?= fstar.exe

# No need to have so many, I just kept the existing list.
# Compiler.Model and Compiler.Examples sounds like a sensible list.
ROOTS := Monitor.fst WebServer.fst AdversarialHandlers.fst GoodHandler1.fst GoodHandler2.fst StlcHandlers.fst

CACHEDIR := .cache
FLAGS += --include ../..
FLAGS += --include ../../../lib
FLAGS += --cache_checked_modules --cache_dir $(CACHEDIR)
FLAGS += $(OTHERFLAGS)

all: verify

%.checked:
	$(IDE_HACK) $(FSTAR_EXE) $(FLAGS) $<
	@touch -c $@ # update timestamp
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

FSTAR_ULIB := $(shell $(FSTAR_EXE) --locate)/../lib/fstar/ulib

extract: verify
	$(FSTAR_EXE) $(FLAGS) --odir out --codegen OCaml --extract '*,-FStar' Monitor.fst AdversarialHandlers.fst GoodHandler1.fst GoodHandler2.fst
	@# Library modules needed at link time that are not part of F*'s app runtime
	$(FSTAR_EXE) --odir out --codegen OCaml --extract 'FStar.Pervasives' $(FSTAR_ULIB)/FStar.Pervasives.fst
	$(FSTAR_EXE) --odir out --codegen OCaml --extract 'FStar.FunctionalExtensionality' $(FSTAR_ULIB)/FStar.FunctionalExtensionality.fst

# The extracted code is linked against F*'s "app" runtime (shipped with F*
# under lib/fstar/lib/app) instead of the full fstar.lib findlib package,
# whose dependency `batteries` may not be available. The app runtime's
# FStar_Char/FStar_String need batteries too, so we use the ASCII-only
# versions from runtime/. zarith and stdint must be visible to ocamlfind
# (set OCAMLPATH if they are not).
FSTAR_APP := $(shell $(FSTAR_EXE) --locate)/../lib/fstar/lib/app

RUNTIME_ML := out/BatList.ml out/BatInt.ml \
	out/Prims.ml out/FStar_Pervasives_Native.ml out/FStar_Pervasives.ml \
	out/FStar_UInt8.ml out/FStar_UInt16.ml out/FStar_UInt32.ml \
	out/FStar_Char.ml out/FStar_String.ml out/FStar_Exn.ml \
	out/FStar_List_Tot_Base.ml \
	out/FStar_Bytes.ml out/FStar_FunctionalExtensionality.ml \
	out/FStar_Monotonic_Heap.ml out/FStar_Heap.ml out/FStar_CommonST.ml out/FStar_ST.ml

# Bytecode: this environment has no assembler/C toolchain for ocamlopt.
# The stublib dirs of zarith/stdint are needed at link time (via
# CAML_LD_LIBRARY_PATH) and at run time (embedded via -dllpath).
STUBLIBS := $(shell ocamlfind query zarith)/../stublibs:$(shell ocamlfind query stdint)/../stublibs
export CAML_LD_LIBRARY_PATH := $(STUBLIBS):$(CAML_LD_LIBRARY_PATH)
DLLPATHS := -dllpath $(shell ocamlfind query zarith)/../stublibs -dllpath $(shell ocamlfind query stdint)/../stublibs
OCAMLOPT := ocamlfind ocamlc -package zarith,stdint,str,unix -linkpkg -w -a -I out $(DLLPATHS)

_prepare_compilation:
	rm -f *.cmx *.cmi *.o out/*.cmx out/*.cmi out/*.o
	cp ../../UnixTypes.* out/
	cp Unix_Star.* out/
	cp Unsafe_Bytes.ml out/
	@# Replacing the calling of monad constructors with calls to the Unix library
	cp MIO_Sig_Call.* out/
	@# The parts of F*'s app runtime that the web server needs
	cp -f --no-preserve=mode $(FSTAR_APP)/FStar_Pervasives_Native.ml \
	   $(FSTAR_APP)/FStar_Exn.ml $(FSTAR_APP)/FStar_List_Tot_Base.ml \
	   $(FSTAR_APP)/FStar_UInt8.ml $(FSTAR_APP)/ints/FStar_UInt16.ml \
	   $(FSTAR_APP)/ints/FStar_UInt32.ml $(FSTAR_APP)/FStar_Bytes.ml \
	   $(FSTAR_APP)/FStar_Monotonic_Heap.ml $(FSTAR_APP)/FStar_Heap.ml \
	   $(FSTAR_APP)/FStar_CommonST.ml $(FSTAR_APP)/FStar_ST.ml out/
	@# Prims.ml: drop the int_to_yojson/int_of_yojson block, which needs the
	@# (unavailable) ppx_deriving_yojson preprocessor; nothing we link uses it
	awk '/^type tmp = string/,/\| Error x -> Error x/ {next} {print}' $(FSTAR_APP)/Prims.ml > out/Prims.ml
	@# ASCII-only replacements for the batteries-based runtime modules
	cp runtime/FStar_Char.ml runtime/FStar_String.ml out/
	@# Minimal stand-ins for the batteries modules the app runtime uses
	cp runtime/BatList.ml runtime/BatInt.ml out/



PROJECT_ML := out/Unsafe_Bytes.ml out/UnixTypes.ml out/CommonUtils.ml out/Unix_Star.ml out/Free.ml out/Hist.ml out/DMFree.ml out/GuardedDMFree.ml out/MIO_Sig.ml out/TC_Checkable.ml out/MonitorParam.ml out/Monitor.ml out/MIO_Sig_Call.ml out/MIO.ml out/BeyondCriteria.ml out/MIO_Behavior.ml out/Compiler_Languages.ml out/Utils.ml out/Compiler_MIO_To_Interm.ml out/Compiler_Model1.ml out/WebServer.ml out/Execute.ml

_compile1:
	$(OCAMLOPT) $(RUNTIME_ML) $(PROJECT_ML) out/AdversarialHandlers.ml -o out/CS.exe

_compile2:
	$(OCAMLOPT) $(RUNTIME_ML) $(PROJECT_ML) out/GoodHandler1.ml -o out/CS.exe

_compile3:
	$(OCAMLOPT) $(RUNTIME_ML) $(PROJECT_ML) out/GoodHandler2.ml -o out/CS.exe

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
