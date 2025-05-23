# export PATH := ../z3/bin:$(PATH);
# export PATH := ../FStar/bin:$(PATH);

FSTAR := fstar.exe

ROOTS := FreeParam.fst

CACHEDIR := .cache
FLAGS  = --record_hints --use_hints --hint_dir hints
FLAGS += --cache_checked_modules --cache_dir $(CACHEDIR)
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

# Run your file in emacs with the same context as the batch mode.
%.fst.emacs: %.fst
	emacs -f fstar-debug-invocation $(FSTAR) $(FLAGS) $<

include .depend.mk

.depend.mk: $(ROOTS)
	$(FSTAR) $(FLAGS) --dep full --warn_error -321 $^ >$@

# Make a dependency graph of the modules.
dep.graph:
	$(FSTAR) $(FLAGS) --dep graph --warn_error -321 $(ROOTS)
	@# Ignore F* library modules:
	sed -i '/-> "fstar_/d' $@
	sed -i '/-> "prims"/d' $@
.PHONY: dep.graph

dep.pdf: dep.graph
	dot -Tpdf $< > $@
