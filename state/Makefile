FSTAR := fstar.exe

ROOTS := Compiler.fst Compiler.STLC.fst $(wildcard Examples.*.fst Examples.*.fsti)

CACHEDIR := .cache
ODIR := $(CACHEDIR)
FLAGS  = --z3version 4.14.1
FLAGS += --cache_checked_modules --cache_dir $(CACHEDIR)
FLAGS += --odir $(ODIR)
FLAGS += $(OTHERFLAGS)

verify: $(patsubst %,$(CACHEDIR)/%.checked,$(ROOTS))

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

# Run your fst file in emacs with the same context as the batch mode.
%.fst.emacs: %.fst
	emacs -f fstar-debug-invocation $(FSTAR) $(FLAGS) $<

# Run your fsti file in emacs with the same context as the batch mode.
%.fsti.emacs: %.fsti
	emacs -f fstar-debug-invocation $(FSTAR) $(FLAGS) $<

include .depend.mk

.depend.mk: $(ROOTS)
	$(FSTAR) $(FLAGS) --dep full --warn_error -321 $^ --output_deps_to $@

# Make a dependency graph of the modules.
dep.graph:
	$(FSTAR) $(FLAGS) --dep graph --warn_error -321 $(ROOTS)
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
	git archive --prefix secref-artifact/ -o artifact.tar HEAD .
	gzip -f -9 artifact.tar
