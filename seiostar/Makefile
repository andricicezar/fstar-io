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
FLAGS  = --z3version 4.15.3
FLAGS += --cache_checked_modules --cache_dir $(CACHEDIR)
FLAGS += --record_hints --use_hints --hint_dir $(BUILD_DIR)/hints
FLAGS += --odir $(ODIR)
FLAGS += --include $(LAMBDABOX_DIR)
FLAGS += --warn_error -241-247-274-321-333
FLAGS += --silent
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

# If we're building a package or a single file, we don't need to run the dep analysis.
ifneq ($(MAKECMDGOALS),package)
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
.PHONY: package
package:
	git archive --prefix seiostar/ -o artifact.tar.gz HEAD .

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

$(BUILD_DIR)/io_program_raw.cmx: $(BUILD_DIR)/io_program_raw.mlf | $(BUILD_DIR)
	malfunction cmx $<

$(BUILD_DIR)/io_program_exe: $(BUILD_DIR)/axioms.cmx $(BUILD_DIR)/io_program_raw.cmx | $(BUILD_DIR)
	ocamlfind ocamlopt -package unix -linkpkg $^ -o $@

.PHONY: $(BUILD_DIR)/io_program
$(BUILD_DIR)/io_program: $(BUILD_DIR)/io_program_exe


clean:
	rm -rf $(CACHEDIR)
	rm -rf $(BUILD_DIR)/hints


## Commands for agents

IMAGE_TAG ?= latest
SESSION_NAME ?= current
IMAGE_FILE ?= $(BUILD_DIR)/image_$(IMAGE_TAG)
IMAGE_NAME ?= seiostar:$(IMAGE_TAG)
CONTAINER_NAME ?= seiostar_$(SESSION_NAME)

$(IMAGE_FILE): | $(BUILD_DIR)
	IMAGE_TAG=$(IMAGE_TAG) nix-build sandbox.nix -o $(IMAGE_FILE)
	docker image load -i $(IMAGE_FILE)

create_image: $(IMAGE_FILE)

delete_image:
	rm -f $(IMAGE_FILE)
	docker image rm -f $(IMAGE_NAME)

recreate_image: delete_image create_image

new_temp_session: $(IMAGE_FILE)
	docker run \
		--rm \
 		-v ~/agentstemp/claude:/home/agent/.claude \
 		-v ~/agentstemp/claude.json:/home/agent/.claude.json \
		-v ~/agentstemp/copilot:/home/agent/.copilot \
		-it \
		$(IMAGE_NAME) /bin/bash

new_session: $(IMAGE_FILE)
	docker run \
		--name $(CONTAINER_NAME) \
 		-v ~/agentstemp/claude:/home/agent/.claude \
 		-v ~/agentstemp/claude.json:/home/agent/.claude.json \
		-v ~/agentstemp/copilot:/home/agent/.copilot \
		-it $(IMAGE_NAME) \
		/bin/bash

attach_session: 
	docker attach $(CONTAINER_NAME)

load_session: 
	docker start -ai $(CONTAINER_NAME)

SYNC_FROM ?= $(shell git rev-parse HEAD)

sync_commits_from_session:
	docker exec $(CONTAINER_NAME) /bin/bash -c "cd /workspace && git format-patch $(SYNC_FROM)..HEAD --stdout" > $(BUILD_DIR)/$(SESSION_NAME).patch
	cat $(BUILD_DIR)/$(SESSION_NAME).patch
	git am < $(BUILD_DIR)/$(SESSION_NAME).patch
	rm $(BUILD_DIR)/$(SESSION_NAME).patch

delete_session:
	docker rm $(CONTAINER_NAME)