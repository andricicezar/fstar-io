# export PATH := ../z2/bin:$(PATH);
# export PATH := ../FStar/bin:$(PATH);

FSTAR_EXE ?= fstar.exe
FSTAR := $(FSTAR_EXE)

ROOTS :=
ROOTS += Compiler.Model1.fst Compiler.Model2.fst Compiler.ModelStlc.fst
ROOTS += Compiler.MIO.To.Interm.fst
ROOTS += case-studies/Compiler.Model1.Examples.fst case-studies/Compiler.Model2.Examples.fst case-studies/IOLogging.fst case-studies/Zip.fst case-studies/NoState.fst

CACHEDIR := .cache
FLAGS += --cache_checked_modules --cache_dir $(CACHEDIR)
FLAGS += $(OTHERFLAGS)
FLAGS += --include case-studies

all: verify

# A hack! After a run of `make` failed in a given file, run `make ide`
# to open that exact file in the interactive with the exact same flags.
# Make sure the first file that make attempts to verify actually fails,
# and do NOT use -j.
ide:
	+$(MAKE) IDE_HACK="emacs -f fstar-debug-invocation" verify

%.checked:
	$(IDE_HACK) $(FSTAR) $(FLAGS) $<
	@touch -c $@ # update timestamp
	@$(if $(IDE_HACK),false) # Make it stop the build

# Run your file in emacs with the same context as the batch mode.
%.fst.emacs: %.fst
	emacs -f fstar-debug-invocation $(FSTAR) $(FLAGS) $<

.depend.mk: $(ROOTS)
	$(FSTAR) $(FLAGS) --dep full --warn_error -321 $^ >$@

include .depend.mk

verify: $(ALL_CHECKED_FILES)

# Make a dependency graph of the modules.
dep.graph:
	$(FSTAR) $(FLAGS) --dep graph --warn_error -321 $(ROOTS)
	@# Ignore F* library modules:
	sed -i '/-> "fstar_/d' $@
	sed -i '/-> "prims"/d' $@
.PHONY: dep.graph

dep.pdf: dep.graph
	dot -Tpdf $< > $@
