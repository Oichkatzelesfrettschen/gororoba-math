# Working-tree builds of gororoba-math. The admission gate (ci/check.sh,
# ci/check_rocq.sh) builds an export of HEAD; these targets build the files
# as they stand, edits included, and leave the source directories of rocq/
# without build products.
#
#   make lean           lake build --wfail in lean/ (the Lake tree is lean/.lake)
#   make rocq-open      rocq/open: make all, in $(BUILD_DIR)/rocq/open
#   make rocq-quantum   rocq/open, then rocq/quantum with -w @all; a warning
#                       line in the build log fails the target
#   make rocq           both Rocq trees
#   make gate           ci/check.sh and ci/check_rocq.sh on HEAD
#   make clean          remove the Rocq build tree $(BUILD_DIR)/rocq
#
# BUILD_DIR    build directory, default build (ignored by git). On a host
#              that keeps build trees outside checkouts, build is a symbolic
#              link to such a directory, or BUILD_DIR names one.
# ROCQ_SWITCH  opam switch of ci/install_rocq.sh, default rocq-9.3.
# ROCQ_JOBS    parallel Rocq compilations, default the online processor
#              count; rocq/open peaks near 2 GB a job (ci/check_rocq.sh).
#
# The compiler options are the option lines of each tree's _RocqProject
# (-w +default in rocq/open, -w @all in rocq/quantum); this file adds none.

BUILD_DIR ?= build
ROCQ_SWITCH ?= rocq-9.3
ROCQ_JOBS ?= $(shell getconf _NPROCESSORS_ONLN)

ifeq ($(strip $(BUILD_DIR)),)
$(error BUILD_DIR is empty)
endif

ROCQ_TREE := $(BUILD_DIR)/rocq
OPAM := opam exec --switch=$(ROCQ_SWITCH) --
# rsync keeps a receiver file that an exclude pattern matches, so a sync
# leaves the compiled objects and generated makefiles of the build tree in
# place, and make recompiles only the sources whose times changed.
ROCQ_PRODUCTS := '*.vo' '*.vok' '*.vos' '*.glob' '*.aux' '.*.cache' \
	'Makefile.rocq' 'Makefile.rocq.*' '.Makefile.rocq*.d' \
	'/open/html/' '/open/metrics/' '/quantum-build.log'

.PHONY: help lean rocq rocq-sync rocq-open rocq-quantum gate clean

help:
	@sed -n '1,/^$$/p' Makefile

lean:
	cd lean && lake build --wfail

rocq-sync:
	mkdir -p "$(ROCQ_TREE)"
	rsync -a --delete $(foreach pattern,$(ROCQ_PRODUCTS),--exclude=$(pattern)) rocq/ "$(ROCQ_TREE)/"

rocq-open: rocq-sync
	$(OPAM) make -C "$(ROCQ_TREE)/open" --jobs=$(ROCQ_JOBS) all

# Under -w @all rocq prints a warning and exits 0 (ci/check_rocq.sh), so the
# search of the log is the check that fails the target.
rocq-quantum: rocq-open
	cd "$(ROCQ_TREE)/quantum" && $(OPAM) rocq makefile --no-rocq-package-warning -f _RocqProject -o Makefile.rocq
	$(OPAM) make -C "$(ROCQ_TREE)/quantum" -f Makefile.rocq --jobs=$(ROCQ_JOBS) >"$(ROCQ_TREE)/quantum-build.log" 2>&1 || \
		{ tail -n 60 "$(ROCQ_TREE)/quantum-build.log" >&2; exit 1; }
	@if grep -n '[Ww]arning' "$(ROCQ_TREE)/quantum-build.log" >&2; then \
		echo "rocq-quantum: the build printed a warning" >&2; exit 1; fi
	@echo "rocq-quantum: compiled $$(grep -c '\.v$$' rocq/quantum/_RocqProject) listed sources, no warning"

rocq: rocq-quantum

gate:
	sh ci/check.sh
	sh ci/check_rocq.sh

# Removes the one directory rocq-sync creates; a BUILD_DIR that is a link
# keeps its target directory.
clean:
	@if [ -d "$(ROCQ_TREE)" ]; then rm -r -- "$(ROCQ_TREE)"; fi
