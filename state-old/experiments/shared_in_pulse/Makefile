PULSE_HOME ?= /home/cezar/.opam/default
PULSE_SHARE = $(PULSE_HOME)/share/pulse

SRC_DIRS = .
INCLUDE_PATHS += $(PULSE_HOME)/lib/pulse/c
OUTPUT_DIRECTORY=_output
CACHE_DIRECTORY=$(OUTPUT_DIRECTORY)/cache

.PHONY: all
all: verify test 

include $(PULSE_SHARE)/Makefile.include

