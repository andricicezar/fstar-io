BUILD_DIR ?= .build
FSTAR_EXE ?= fstar.exe
FSTAR := $(FSTAR_EXE)

ROOTS := MIO.Sig.fst \
	     MST.Repr.fst 
CACHEDIR := $(BUILD_DIR)/cache
ODIR := $(BUILD_DIR)/odir
FLAGS  = --z3version 4.15.3
FLAGS += --cache_checked_modules --cache_dir $(CACHEDIR)
FLAGS += --record_hints --use_hints --hint_dir $(BUILD_DIR)/hints
FLAGS += --odir $(ODIR)
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

clean:
	rm -rf $(CACHEDIR)
	rm -rf $(BUILD_DIR)/hints
