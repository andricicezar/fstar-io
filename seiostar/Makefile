BUILD_DIR ?= .build
FSTAR_EXE ?= fstar.exe
FSTAR := $(FSTAR_EXE)

LAMBDABOX_DIR := lambdabox
ROOTS := RrHP.Tests.fst \
         RQ.TypingRelation.Tests.fst \
         RQ.Metaprogram.Tests.fst
# RunningExample.fst \
# $(LAMBDABOX_DIR)/LambdaIOToLambdaBox.fst \
# $(LAMBDABOX_DIR)/LambdaBoxToSexp.fst

CACHEDIR := $(BUILD_DIR)/cache
ODIR := $(BUILD_DIR)/odir
ABS_CACHEDIR := $(abspath $(CACHEDIR))

FLAGS = --cache_checked_modules --cache_dir $(abspath $(CACHEDIR))
FLAGS += --record_hints --use_hints --hint_dir $(abspath $(BUILD_DIR)/hints)
FLAGS += --odir $(abspath $(ODIR))
FLAGS += --include $(abspath $(LAMBDABOX_DIR))
FLAGS += --warn_error -241-247-274-288-321-333
FLAGS += $(OTHERFLAGS)

all: verify

$(BUILD_DIR) $(CACHEDIR) $(ODIR):
	mkdir -p $@

$(CACHEDIR)/%.fst.checked: %.fst | $(CACHEDIR) $(ODIR)
	$(FSTAR) $(FLAGS) $<
	@touch -c $@ # update timestamp

$(ABS_CACHEDIR)/%.fst.checked: %.fst | $(CACHEDIR) $(ODIR)
	$(FSTAR) $(FLAGS) $<
	@touch -c $@ # update timestamp

$(CACHEDIR)/%.fst.checked: $(LAMBDABOX_DIR)/%.fst | $(CACHEDIR) $(ODIR)
	$(FSTAR) $(FLAGS) $<
	@touch -c $@ # update timestamp

$(ABS_CACHEDIR)/%.fst.checked: $(LAMBDABOX_DIR)/%.fst | $(CACHEDIR) $(ODIR)
	$(FSTAR) $(FLAGS) $<
	@touch -c $@ # update timestamp

$(CACHEDIR)/%.fsti.checked: %.fsti | $(CACHEDIR) $(ODIR)
	$(FSTAR) $(FLAGS) $<
	@touch -c $@ # update timestamp

$(ABS_CACHEDIR)/%.fsti.checked: %.fsti | $(CACHEDIR) $(ODIR)
	$(FSTAR) $(FLAGS) $<
	@touch -c $@ # update timestamp

# Run your fst file in emacs with the same context as the batch mode.
%.fst.emacs: %.fst
	emacs -nw -f fstar-debug-invocation $(FSTAR) $(FLAGS) --use_hint_hashes $<

# Run your fsti file in emacs with the same context as the batch mode.
%.fsti.emacs: %.fsti
	emacs -nw -f fstar-debug-invocation $(FSTAR) $(FLAGS) --use_hint_hashes $<

# Support `make verify <file>.fst` and `make validate <file>.fst`
ifeq (verify,$(firstword $(MAKECMDGOALS)))
  _SINGLE_FILE := $(wordlist 2,$(words $(MAKECMDGOALS)),$(MAKECMDGOALS))
  ifneq ($(_SINGLE_FILE),)
    $(eval $(_SINGLE_FILE):;@:)
  endif
endif
ifeq (validate,$(firstword $(MAKECMDGOALS)))
  _SINGLE_FILE := $(wordlist 2,$(words $(MAKECMDGOALS)),$(MAKECMDGOALS))
  ifneq ($(_SINGLE_FILE),)
    $(eval $(_SINGLE_FILE):;@:)
  endif
endif

# If we're building a package, running MCP, or a single file, we don't need to run dep analysis.
ifeq ($(filter package mcp,$(MAKECMDGOALS)),)
ifeq ($(_SINGLE_FILE),)
include $(BUILD_DIR)/depend.mk
endif
endif

ifdef _SINGLE_FILE
verify: | $(CACHEDIR) $(ODIR)
	$(FSTAR) $(FLAGS) $(_SINGLE_FILE)
else
verify: $(ALL_CHECKED_FILES)
endif

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
.PHONY: package mcp
package:
	git archive --prefix seiostar/ -o artifact.tar.gz HEAD .


FSTAR_LSP_MCP_MAIN ?= $(HOME)/.copilot/fstar-lsp-mcp/main.js
mcp: | $(BUILD_DIR) $(CACHEDIR) $(ODIR)
	@test -f "$(FSTAR_LSP_MCP_MAIN)" || (echo "Missing MCP server entrypoint: $(FSTAR_LSP_MCP_MAIN)" 1>&2; exit 1)
	@ARGS_FILE="$(abspath $(BUILD_DIR)/fstar-lsp.args)"; \
    printf '%s\n' $(FLAGS) > "$$ARGS_FILE"; \
	FSTAR_WORKSPACE_ROOT="$(CURDIR)" FSTAR_LSP_ARGS_FILE="$$ARGS_FILE" exec node "$(FSTAR_LSP_MCP_MAIN)"

ifdef _SINGLE_FILE
validate: | $(CACHEDIR) $(ODIR)
	$(FSTAR) $(FLAGS) --report_assumes error $(_SINGLE_FILE)
else
validate:
	@# Run depend first without the flag, as otherwise it will
	@# warn about every module in the standard library that does
	@# not have an implementation.
	$(MAKE) depend
	$(MAKE) OTHERFLAGS='--report_assumes error'
endif

IOFLAGS := --unsafe_tactic_exec $(FLAGS)

$(BUILD_DIR)/io_program.ast: $(LAMBDABOX_DIR)/LambdaBoxExamples.fst \
                $(LAMBDABOX_DIR)/LambdaIOToLambdaBox.fst $(LAMBDABOX_DIR)/LambdaBoxToSexp.fst \
                $(LAMBDABOX_DIR)/LambdaBox.fst $(LAMBDABOX_DIR)/Sexp.fst LambdaIO.fst | $(BUILD_DIR) $(CACHEDIR) $(ODIR)
	$(FSTAR) $(IOFLAGS) $(LAMBDABOX_DIR)/LambdaBoxExamples.fst

$(BUILD_DIR)/io_program_raw.mlf: $(BUILD_DIR)/io_program.ast | $(BUILD_DIR)
	opam exec --switch=only-peregrine -- peregrine ocaml $< -o $@

$(BUILD_DIR)/axioms.cmx: $(LAMBDABOX_DIR)/axioms.ml | $(BUILD_DIR)
	ocamlfind ocamlopt -package unix -c -o $@ $<

$(BUILD_DIR)/io_program_raw.cmx: $(BUILD_DIR)/io_program_raw.mlf $(BUILD_DIR)/axioms.cmx | $(BUILD_DIR)
	cd $(BUILD_DIR) && malfunction cmx $(notdir $<)

$(BUILD_DIR)/io_program_exe: $(BUILD_DIR)/axioms.cmx $(BUILD_DIR)/io_program_raw.cmx | $(BUILD_DIR)
	ocamlfind ocamlopt -package unix -linkpkg $^ -o $@

.PHONY: io_program
io_program: $(BUILD_DIR)/io_program_exe


clean:
	rm -rf $(CACHEDIR)
	rm -rf $(BUILD_DIR)/hints
