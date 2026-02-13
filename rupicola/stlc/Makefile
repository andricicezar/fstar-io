FSTAR_EXE ?= fstar.exe
FSTAR := $(FSTAR_EXE)

ROOTS := Metaprogram.fst RrHP.fst STLCToLambdaBox.fst LambdaBoxToSexp.fst

CACHEDIR := .cache
ODIR := $(CACHEDIR)
FLAGS  = --z3version 4.15.2
FLAGS += --cache_checked_modules --cache_dir $(CACHEDIR)
FLAGS += --odir $(ODIR)
FLAGS += $(OTHERFLAGS)

all: verify

.cache/%.fst.checked: %.fst
	$(FSTAR) $(FLAGS) $<
	@touch -c $@ # update timestamp

.cache/%.fsti.checked: %.fsti
	$(FSTAR) $(FLAGS) $<
	@touch -c $@ # update timestamp

# Run your fst file in emacs with the same context as the batch mode.
%.fst.emacs: %.fst
	emacs -f fstar-debug-invocation $(FSTAR) $(FLAGS) $<

# Run your fsti file in emacs with the same context as the batch mode.
%.fsti.emacs: %.fsti
	emacs -f fstar-debug-invocation $(FSTAR) $(FLAGS) $<

# If we're building a package, we don't need to run the dep analysis.
ifneq ($(MAKECMDGOALS),package)
include .depend.mk
endif

verify: $(ALL_CHECKED_FILES)

.depend.mk: $(ROOTS)
	$(FSTAR) $(FLAGS) --dep full $(ROOTS) --extract '*' --output_deps_to $@
depend: .depend.mk

# Make a dependency graph of the modules.
dep.graph:
	$(FSTAR) $(FLAGS) --dep graph $(ROOTS)
	@# Ignore F* library modules:
	sed -i '/-> "fstar_/d' $@
	sed -i '/-> "prims"/d' $@
.PHONY: dep.graph

dep.pdf: dep.graph
	dot -Tpdf $< > $@

# Package this directory (from Git). Note: git archive apparently
# already removes user and host names (good!)
.PHONY: package
package:
	git archive --prefix rupicola/ -o artifact.tar.gz HEAD .

validate:
	@# Run depend first without the flag, as otherwise it will
	@# warn about every module in the standard library that does
	@# not have an implementation.
	$(MAKE) depend
	$(MAKE) OTHERFLAGS='--report_assumes error'

IOFLAGS := --unsafe_tactic_exec $(FLAGS)

io_program.ast: LambdaBoxExamples.fst LambdaBoxMeta.fst \
                STLCToLambdaBox.fst LambdaBoxToSexp.fst \
                LambdaBox.fst Sexp.fst STLC.fst
	$(FSTAR) $(IOFLAGS) LambdaBoxExamples.fst

io_program_raw.mlf: io_program.ast
	peregrine ocaml $< -o $@

axioms.cmx: axioms.ml
	ocamlfind ocamlopt -c $<

io_program_raw.cmx: io_program_raw.mlf
	malfunction cmx $<

io_program_exe: axioms.cmx io_program_raw.cmx
	ocamlfind ocamlopt -linkpkg $^ -o $@

.PHONY: io_program
io_program: io_program_exe

clean:
	rm -rf $(CACHEDIR) $(ODIR)
	rm -f io_program.ast io_program_raw.mlf io_program_raw.cmi \
	      io_program_raw.cmx io_program_raw.o io_program_exe \
	      axioms.cmi axioms.cmx axioms.o
