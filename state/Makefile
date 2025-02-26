# export PATH := ../z3/bin:$(PATH);
# export PATH := ../FStar/bin:$(PATH);

FSTAR := fstar.exe

ROOTS := Compiler.fst Compiler.STLC.fst $(wildcard Examples.*.fst Examples.*.fsti)

CACHEDIR := .cache
ODIR := $(CACHEDIR)
FLAGS  = --z3version 4.13.3
FLAGS += --cache_checked_modules --cache_dir $(CACHEDIR)
FLAGS += --odir $(ODIR)
FLAGS += $(OTHERFLAGS)

verify: $(patsubst %,$(CACHEDIR)/%.checked,$(ROOTS))

# A hack! After a run of `make` failed in a given file, run `make ide`
# to open that exact file in the interactive with the exact same flags.
# Make sure the first file that make attempts to verify actually fails,
# and do NOT use -j.
ide:
	+$(MAKE) IDE_HACK="emacs -f fstar-debug-invocation" verify

# work around F* bug
hints:
	mkdir $@

.cache/%.fst.checked: %.fst | hints
	$(IDE_HACK) $(FSTAR) $(FLAGS) $<
	@touch -c $@ # update timestamp
	@$(if $(IDE_HACK),false) # Make it stop the build

.cache/%.fsti.checked: %.fsti | hints
	$(IDE_HACK) $(FSTAR) $(FLAGS) $<
	@touch -c $@ # update timestamp
	@$(if $(IDE_HACK),false) # Make it stop the build

PLUG=extraction/dune/_build/install/default/lib/secref_extr/secref_extr

$(PLUG).cmxs:
	$(MAKE) -C extraction

.PHONY: plugin
plugin: $(PLUG).cmxs

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
	$(FSTAR) $(FLAGS) --dep full --warn_error -321 $^ -o $@

# Make a dependency graph of the modules.
dep.graph:
	$(FSTAR) $(FLAGS) --dep graph --warn_error -321 $(ROOTS)
	@# Ignore F* library modules:
	sed -i '/-> "fstar_/d' $@
	sed -i '/-> "prims"/d' $@
.PHONY: dep.graph

dep.pdf: dep.graph
	dot -Tpdf $< > $@
