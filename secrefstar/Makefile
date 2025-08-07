FSTAR_EXE ?= fstar.exe
FSTAR := $(FSTAR_EXE)

ROOTS := Compiler.fst Compiler.STLC.fst $(wildcard Examples.*.fst Examples.*.fsti)

CACHEDIR := .cache
ODIR := $(CACHEDIR)
FLAGS  = --z3version 4.13.3
FLAGS += --cache_checked_modules --cache_dir $(CACHEDIR)
FLAGS += --odir $(ODIR)
FLAGS += $(OTHERFLAGS)
FLAGS += --warn_error -242 # inner let-rec not encoded, expected
FLAGS += --warn_error -272 # top-level effects, we use them
FLAGS += --warn_error -274 # namespace shadowing warning, benign
FLAGS += --warn_error -321 # unexpected checked files present, completely spurious warning

all: verify

.cache/%.fst.checked: %.fst
	$(FSTAR) $(FLAGS) $<
	@touch -c $@ # update timestamp

.cache/%.fsti.checked: %.fsti
	$(FSTAR) $(FLAGS) $<
	@touch -c $@ # update timestamp

PLUG=extraction/lib/secref_extr/secref_extr

$(PLUG).cmxs:
	$(MAKE) -C extraction

.PHONY: plugin
plugin: $(PLUG).cmxs

# Run `make build-Examples.Intro` to build and run the Examples.Intro module,
# and etc.
build-%: M=$*
build-%: D=$*.bld
build-%: .cache/%.fst.checked | plugin
	mkdir -p $(D)
	@# Must extract LabeledRefs.fst explicitly here since it has an interface.
	$(FSTAR) $(FLAGS) --load_cmxs $(PLUG) \
		--codegen OCaml --extract '*,-Prims,-FStar' \
		--odir $(D) \
		LabeledRefs.fst
	$(FSTAR) $(FLAGS) --load_cmxs $(PLUG) \
		--codegen OCaml --extract '*,-Prims,-FStar' \
		--odir $(D) \
		$<
	cp misc/dune $D/
	cp misc/dune-project $D/
	cp Test_$M.ml $D/main.ml
	$(FSTAR) --ocamlenv dune build --root=$D
	$(FSTAR) --ocamlenv dune install --root=$D --prefix=.
	./$D/bin/main

build-all: build-Examples.Intro build-Examples.Autograder build-Examples.PRNG build-Examples.CooperativeMultiThreadingWithIndexT

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
	git archive --prefix secrefstar/ -o artifact.tar.gz HEAD .

validate:
	@# Run depend first without the flag, as otherwise it will
	@# warn about every module in the standard library that does
	@# not have an implementation.
	$(MAKE) depend
	$(MAKE) OTHERFLAGS='--report_assumes error'

clean:
	rm -rf $(CACHEDIR) $(ODIR)
