# This makefile is not great and will repeat some work by checking ulib modules.

FSTAR_EXE ?= fstar.exe

TAG := extraction
SRC := .
CACHE_DIR := _cache
OUTPUT_DIR := dune/generated
CODEGEN := PluginNoLib
ROOTS := $(shell find $(SRC) -name '*.fst' -o -name '*.fsti')
FSTAR_OPTIONS += --with_fstarc
EXTRACT += --extract '-*,+ExtractSST'
FSTAR_OPTIONS += --lax --MLish --MLish_effect FStarC.Effect

OTHERFLAGS += --already_cached 'Prims,FStarC'

# This makefile is included from several other makefiles in the tree.
#
# (this comment is old)

# It enables configurably 'silent' rules, that do not
# print output unless V=1 is set. When writing a rule, you can do as
# follows (taken from src/Makefile.boot):
#
# ocaml-output/%.ml:
# 	$(call msg, "EXTRACT", $(notdir $@))
# 	$(Q)$(BENCHMARK_PRE) $(FSTAR_C) $(SIL) $(notdir $(subst .checked.lax,,$<)) \
#                   --codegen OCaml \
#                   --extract_module $(basename $(notdir $(subst .checked.lax,,$<)))
#
# This unconditionally prints a message like '[EXTRACT FStar_Syntax_Subst.ml]'
# (`notdir` is used to omit the directory of the target) and then
# proceeds to execute the F* invocation silently (since $(Q) expands to
# "@"). However, calling the same rule with `make V=1` will still print
# the message and then print the F* invocation before executing.
#
# Besides that, when not using V=1, F* receives the --silent flag to
# reduce non-critical output.

# It also defines some other utilities for resource monitoring and
# paths manipulation for cygwin

MAKEFLAGS += --no-builtin-rules
Q?=@
SIL?=--silent
RUNLIM=
ifneq ($(V),)
	Q=
	SIL=
else
	MAKEFLAGS += -s
endif

define NO_RUNLIM_ERR
runlim not found:
  To use RESOURCEMONITOR=1, the `runlim` tool must be installed and in your $$PATH.
  It must also be a recent version supporting the `-p` option.
  You can get it from: [https://github.com/arminbiere/runlim]
endef

define msg =
@printf "   %-14s  %s\n" $(1) $(2)
endef
define bold_msg =
@#-tput bold 2>/dev/null
@printf -- "  %-15s" $(1)
@#-tput sgr0 2>/dev/null
@printf "  %s\n" $(2)
endef

# Passing RESOURCEMONITOR=1 will create .runlim files through the source tree with
# information about the time and space taken by each F* invocation.
ifneq ($(RESOURCEMONITOR),)
	ifeq ($(shell which runlim),)
		_ := $(error $(NO_RUNLIM_ERR)))
	endif
	ifneq ($(MONID),)
		MONPREFIX=$(MONID).
	endif
	RUNLIM=runlim -p -o $@.$(MONPREFIX)runlim
endif

# Can be called as $(call maybe_cygwin_path,...)
#   where ... is the argument

maybe_cygwin_path=$(if $(findstring $(OS),Windows_NT),$(shell cygpath -m $(1)),$(1))

# Ensure that any failing rule will not create its target file.
# In other words, make `make` less insane.
.DELETE_ON_ERROR:

.DEFAULT_GOAL:=__undef
.PHONY: __undef
__undef:
	$(error "This makefile does not have a default goal")

# Check that a variable is defined. If not, abort with an (optional) error message.
need =												\
  $(if $(value $(strip $1)),,									\
    $(error Need a value for $(strip $1)$(if $2, ("$(strip $2)"))))

# Check that a variable is defined and pointing to an executable.
# Is there no negation in make...?
# Wew! this was interesting to write. Especially the override part.
need_exe =											\
  $(if $(value $(strip $1)),									\
    $(if $(wildcard $(value $(strip $1))),							\
      $(if $(shell test -x $(value $(strip $1)) && echo 1),					\
        $(eval override $(strip $1):=$(abspath $(value $(strip $1)))),				\
        $(error $(strip $1) ("$(value $(strip $1))") is not executable)),			\
      $(if $(shell which $(value $(strip $1))),							\
        $(eval override $(strip $1):=$(shell which $(value $(strip $1)))),			\
        $(error $(strip $1) ("$(value $(strip $1))") does not exist and is not in PATH (cwd = $(CURDIR))))),	\
    $(error Need an executable for $(strip $1)$(if $2, ("$(strip $2)"))))			\

need_file =											\
  $(if $(value $(strip $1)),									\
    $(if $(wildcard $(value $(strip $1))),							\
      $(if $(shell test -f $(value $(strip $1)) && echo 1),					\
        $(eval override $(strip $1):=$(abspath $(value $(strip $1)))),				\
        $(error $(strip $1) ("$(value $(strip $1))") is not executable)),			\
      $(error $(strip $1) ("$(value $(strip $1))") does not exist (cwd = $(CURDIR)))),		\
    $(error Need a file path for $(strip $1)$(if $2, ("$(strip $2)"))))				\

need_dir =											\
  $(if $(value $(strip $1)),									\
    $(if $(wildcard $(value $(strip $1))),							\
      $(if $(shell test -d $(value $(strip $1)) && echo 1),					\
        $(eval override $(strip $1):=$(abspath $(value $(strip $1)))),				\
        $(error $(strip $1) ("$(value $(strip $1))") is not executable)),			\
      $(error $(strip $1) ("$(value $(strip $1))") is not a directory (cwd = $(CURDIR)))),	\
    $(error Need an *existing* directory path for $(strip $1)$(if $2, ("$(strip $2)"))))	\

need_dir_mk =											\
  $(if $(value $(strip $1)),									\
    $(if $(shell mkdir -p $(value $(strip $1)) && echo 1),					\
      $(eval override $(strip $1):=$(abspath $(value $(strip $1)))),				\
      $(error $(strip $1) ("$(value $(strip $1))") is not a directory (mkdir failed, cwd = $(CURDIR)))),	\
    $(error Need a directory path for $(strip $1)$(if $2, ("$(strip $2)"))))			\

# common.mk must be included before this file.

FSTAR_EXE ?= fstar.exe
$(call need_exe, FSTAR_EXE)

PULSE_ROOT := $(abspath $(PULSE_ROOT))

# Define the Pulse root directory. We need to fix it to use the Windows path convention on Windows+Cygwin.
ifeq ($(OS),Windows_NT)
  PULSE_HOME := $(shell cygpath -m $(PULSE_ROOT))
else
  PULSE_HOME := $(PULSE_ROOT)
endif
export PULSE_HOME

.DEFAULT_GOAL := ocaml
$(call need_exe, FSTAR_EXE, fstar.exe to be used)
$(call need_dir_mk, CACHE_DIR, directory for checked files)
$(call need_dir_mk, OUTPUT_DIR, directory for extracted OCaml files)
$(call need, CODEGEN, backend (OCaml / Plugin))
$(call need_dir, SRC, source directory)
$(call need, TAG, a tag for the .depend; to prevent clashes. Sorry.)
$(call need, ROOTS, a list of roots for the dependency analysis)
# Optional: EXTRACT, DEPFLAGS

# This is to support both --lax and non --lax clients.
EXTENSION := $(if $(findstring --lax,$(FSTAR_OPTIONS)),.checked.lax,.checked)
MSG := $(if $(findstring --lax,$(FSTAR_OPTIONS)),LAXCHECK,CHECK)

.PHONY: clean
clean:
	rm -rf $(CACHE_DIR)
	rm -rf $(OUTPUT_DIR)

.PHONY: __all
__all: verify ocaml

.PHONY: ocaml
ifdef NO_OCAML
ocaml:
else
ocaml: all-ml
endif

.PHONY: verify
verify: all-checked

FSTAR_OPTIONS += $(OTHERFLAGS)
FSTAR_OPTIONS += --odir "$(OUTPUT_DIR)"
FSTAR_OPTIONS += --cache_dir "$(CACHE_DIR)"
FSTAR_OPTIONS += --include "$(SRC)"
FSTAR_OPTIONS += --cache_checked_modules
FSTAR_OPTIONS += --warn_error -321
FSTAR_OPTIONS += $(addprefix --include , $(INCLUDE_PATHS))
FSTAR_OPTIONS += --ext context_pruning
FSTAR_OPTIONS += --z3version 4.13.3

ifeq ($(ADMIT),1)
FSTAR_OPTIONS += --admit_smt_queries true
endif

FSTAR = $(FSTAR_EXE) $(SIL) $(FSTAR_OPTIONS)

%$(EXTENSION): FF=$(notdir $(subst $(EXTENSION),,$@))
%$(EXTENSION):
	$(call msg, $(MSG), $(FF))
	$(FSTAR) --already_cached ',*' $<
	touch -c $@

%.ml: LBL=$(notdir $@)
%.ml:
	$(call msg, "EXTRACT", $(LBL))
	$(FSTAR) $< --already_cached '*,' --codegen $(CODEGEN)
	touch -c $@

%.krml: FF=$(notdir $(subst $(EXTENSION),,$<))
%.krml: MM=$(basename $(FF))
%.krml: LBL=$(notdir $@)
%.krml:
	$(call msg, "EXTRACT", $(LBL))
	$(FSTAR) $< --already_cached ',*' --codegen krml --extract_module $(MM)
	touch -c $@

$(CACHE_DIR)/.depend$(TAG):
	$(call msg, "DEPEND", $(SRC))
	$(FSTAR) --dep full $(ROOTS) $(EXTRACT) $(FSTAR_OPTIONS) $(DEPFLAGS) --output_deps_to $@
	mkdir -p $(CACHE_DIR)

depend: $(CACHE_DIR)/.depend$(TAG)
include $(CACHE_DIR)/.depend$(TAG)

all-ml: $(ALL_ML_FILES)
all-checked: $(ALL_CHECKED_FILES)

.DEFAULT_GOAL := all
all: build

extract: $(ALL_ML_FILES)

build: extract
	$(FSTAR_EXE) --ocamlenv dune build --root=dune
	dune install --root=dune --prefix=$(CURDIR)
