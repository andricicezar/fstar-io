BUILD_DIR ?= .build
FSTAR_EXE ?= fstar.exe
FSTAR := $(FSTAR_EXE)


LAMBDABOX_DIR := lambdabox
ROOTS := RQ.Metaprogram.Tests.fst \
	     RunningExample.fst \
         $(LAMBDABOX_DIR)/LambdaIOToLambdaBox.fst \
         $(LAMBDABOX_DIR)/LambdaBoxToSexp.fst

CACHEDIR := $(BUILD_DIR)/cache
ODIR := $(BUILD_DIR)/odir
FLAGS  = --z3version 4.15.2
FLAGS += --cache_checked_modules --cache_dir $(CACHEDIR)
FLAGS += --odir $(ODIR)
FLAGS += --include $(LAMBDABOX_DIR)
FLAGS += $(OTHERFLAGS)

$(BUILD_DIR) $(CACHEDIR) $(ODIR):
	mkdir -p $@

all: verify

$(CACHEDIR)/%.fst.checked: %.fst | $(CACHEDIR) $(ODIR)
	$(FSTAR) $(FLAGS) $<
	@touch -c $@ # update timestamp

$(CACHEDIR)/%.fst.checked: $(LAMBDABOX_DIR)/%.fst | $(CACHEDIR) $(ODIR)
	$(FSTAR) $(FLAGS) $<
	@touch -c $@ # update timestamp

$(CACHEDIR)/%.fsti.checked: %.fsti | $(CACHEDIR) $(ODIR)
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
include $(BUILD_DIR)/depend.mk
endif

verify: $(ALL_CHECKED_FILES)

$(BUILD_DIR)/depend.mk: $(ROOTS) | $(BUILD_DIR) $(CACHEDIR) $(ODIR)
	$(FSTAR) $(FLAGS) --dep full $(ROOTS) --extract '*' --output_deps_to $@
depend: $(BUILD_DIR)/depend.mk

# Make a dependency graph of the modules.
$(BUILD_DIR)/dep.graph: | $(BUILD_DIR) $(CACHEDIR) $(ODIR)
	$(FSTAR) $(FLAGS) --dep graph $(ROOTS)
	@# Ignore F* library modules:
	sed -i '/-> "fstar_/d' $@
	sed -i '/-> "prims"/d' $@
.PHONY: $(BUILD_DIR)/dep.graph

$(BUILD_DIR)/dep.pdf: $(BUILD_DIR)/dep.graph
	dot -Tpdf $< > $@

# Package this directory (from Git). Note: git archive apparently
# already removes user and host names (good!)
.PHONY: package
package:
	git archive --prefix seiostar/ -o artifact.tar.gz HEAD .

validate:
	@# Run depend first without the flag, as otherwise it will
	@# warn about every module in the standard library that does
	@# not have an implementation.
	$(MAKE) depend
	$(MAKE) OTHERFLAGS='--report_assumes error'

IOFLAGS := --unsafe_tactic_exec $(FLAGS)

$(BUILD_DIR)/io_program.ast: $(LAMBDABOX_DIR)/LambdaBoxExamples.fst \
                $(LAMBDABOX_DIR)/LambdaIOToLambdaBox.fst $(LAMBDABOX_DIR)/LambdaBoxToSexp.fst \
                $(LAMBDABOX_DIR)/LambdaBox.fst $(LAMBDABOX_DIR)/Sexp.fst LambdaIO.fst | $(BUILD_DIR) $(CACHEDIR) $(ODIR)
	$(FSTAR) $(IOFLAGS) $(LAMBDABOX_DIR)/LambdaBoxExamples.fst

$(BUILD_DIR)/io_program_raw.mlf: $(BUILD_DIR)/io_program.ast | $(BUILD_DIR)
	opam exec --switch=only-peregrine -- peregrine ocaml $< -o $@

$(BUILD_DIR)/axioms.cmx: $(LAMBDABOX_DIR)/axioms.ml | $(BUILD_DIR)
	ocamlfind ocamlopt -package unix -c -o $@ $<

$(BUILD_DIR)/io_program_raw.cmx: $(BUILD_DIR)/io_program_raw.mlf | $(BUILD_DIR)
	malfunction cmx $<

$(BUILD_DIR)/io_program_exe: $(BUILD_DIR)/axioms.cmx $(BUILD_DIR)/io_program_raw.cmx | $(BUILD_DIR)
	ocamlfind ocamlopt -package unix -linkpkg $^ -o $@

.PHONY: $(BUILD_DIR)/io_program
io_program: $(BUILD_DIR)/io_program_exe

clean:
	rm -rf $(BUILD_DIR)
