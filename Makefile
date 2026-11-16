# Working-tree builds of gororoba-math, for GNU make. The admission gate
# (ci/check.sh, ci/check_rocq.sh) builds an export of HEAD; these targets
# build the files as they stand, edits included, and leave the source
# directories of rocq/ without build products.
#
#   make lean           lake build --wfail in lean/ (the Lake tree is lean/.lake)
#   make rocq-open      rocq/open: make all, in $(BUILD_DIR)/rocq/open
#   make rocq-quantum   rocq/open, which rocq/quantum reads, then rocq/quantum
#   make rocq-delegation  rocq/delegation
#                       Each Rocq target fails on a warning line of the
#                       makefile generator and on a (source, warning) pair
#                       of its build log that ci/rocq-warnings/allowed.tsv
#                       lacks (ci/rocq_warning_pairs.py --new-only)
#   make rocq           the three Rocq trees
#   make gate           ci/check.sh and ci/check_rocq.sh on HEAD
#   make clean          remove the Rocq build tree $(BUILD_DIR)/rocq
#
# BUILD_DIR    build directory: build in the checkout root (ignored by git;
#              on a host that keeps build trees outside checkouts, a
#              symbolic link to such a directory), or a directory outside
#              the checkout. Any other path inside the checkout is refused.
# ROCQ_SWITCH  opam switch of ci/install_rocq.sh, default rocq-9.3.
# ROCQ_JOBS    parallel compilations of each Rocq build, default the online
#              processor count; it is passed to the build of each tree and
#              is independent of a -j given to this make. rocq/open peaks
#              near 2 GB a job (ci/check_rocq.sh).
#
# The warning options are the option lines of each tree's _RocqProject
# (-w all,+default: the default set is fatal and every other warning
# prints); this file adds no compiler option. rocq/open/Makefile adds the Flocq
# library root of the switch, as it does under the gate.

BUILD_DIR ?= build
ROCQ_SWITCH ?= rocq-9.3
ROCQ_JOBS ?= $(shell getconf _NPROCESSORS_ONLN)
PYTHON ?= python3

ROCQ_TREE := $(BUILD_DIR)/rocq
# rocq-sync writes this file into a tree it creates; rocq-sync and clean
# touch no existing directory that lacks it.
MARKER := $(ROCQ_TREE)/.gororoba-math-build-tree
OPAM := opam exec --switch=$(ROCQ_SWITCH) --
# rsync keeps a receiver file that an exclude pattern matches, so a sync
# leaves the compiled objects and generated makefiles of the build tree in
# place. The sync compares contents (--checksum) and copies no modification
# time, so a source whose bytes changed carries the time of the sync, later
# than any object compiled from its previous bytes, and an unchanged source
# keeps its time; make recompiles the changed sources and their dependents.
ROCQ_PRODUCTS := '*.vo' '*.vok' '*.vos' '*.glob' '*.aux' '.*.cache' \
	'Makefile.rocq' 'Makefile.rocq.*' '.Makefile.rocq*.d' \
	'/open/html/' '/open/metrics/' '/*.log' \
	'/.gororoba-math-build-tree'

.PHONY: help lean rocq rocq-sync rocq-open rocq-quantum rocq-delegation gate clean

help:
	@sed -n '1,/^$$/p' Makefile

lean:
	cd lean && lake build --wfail

# The build tree is BUILD_DIR/rocq after links are resolved. It is refused
# when it lies inside the checkout anywhere but build/rocq, which keeps a
# sync with --delete, and clean, away from rocq/ and every tracked path. A
# compiled object whose source left the checkout is removed after the
# sync, so a deleted module stops being importable.
rocq-sync:
	@top=$$(pwd -P); tree=$$(realpath -m -- "$(ROCQ_TREE)"); \
	case "$$tree" in \
		"$$top/build/rocq") ;; \
		"$$top"|"$$top"/*) echo "rocq-sync: BUILD_DIR must be build or a directory outside the checkout, not $(BUILD_DIR)" >&2; exit 1 ;; \
	esac; \
	if [ -e "$(ROCQ_TREE)" ] && [ ! -f "$(MARKER)" ]; then \
		echo "rocq-sync: $(ROCQ_TREE) exists and is not a build tree of this Makefile" >&2; exit 1; \
	fi
	mkdir -p "$(ROCQ_TREE)"
	touch "$(MARKER)"
	rsync -rlpgoD --checksum --delete $(foreach pattern,$(ROCQ_PRODUCTS),--exclude=$(pattern)) rocq/ "$(ROCQ_TREE)/"
	@find "$(ROCQ_TREE)" -name '*.vo' | while IFS= read -r object; do \
		stem=$${object%.vo}; \
		[ -f "$$stem.v" ] || rm -f -- "$$stem.vo" "$$stem.vok" "$$stem.vos" "$$stem.glob" \
			"$$(dirname "$$stem")/.$$(basename "$$stem").aux"; \
	done

# The build of tree $(1) writes its log, which the warning ratchet reads.
# --output-sync=target keeps each compilation's lines together, and
# --no-print-directory keeps the build directory's name out of the log.
define rocq_build
	@status=0; $(OPAM) make --no-print-directory --output-sync=target -C "$(ROCQ_TREE)/$(1)" $(2) --jobs=$(ROCQ_JOBS) \
		>"$(ROCQ_TREE)/$(1)-build.log" 2>&1 || status=$$?; \
	if [ "$$status" -ne 0 ]; then tail -n 60 "$(ROCQ_TREE)/$(1)-build.log" >&2; exit "$$status"; fi
endef
# The ratchet of ci/check_rocq.sh on the log of tree $(1), new pairs only:
# an incremental build recompiles only changed sources, so its log cannot
# show that an allowed warning stopped. A source with a new warning has
# left its object behind, and a second run would find it up to date and
# print nothing, so the objects of each source the ratchet names are
# removed.
define rocq_ratchet
	@if ! $(PYTHON) -I ci/rocq_warning_pairs.py --tree $(1) --new-only \
		--allowed ci/rocq-warnings/allowed.tsv --causes ci/rocq-warnings/causes.tsv \
		"$(ROCQ_TREE)/$(1)-build.log" 2>"$(ROCQ_TREE)/$(1)-ratchet.log"; then \
		cat "$(ROCQ_TREE)/$(1)-ratchet.log" >&2; \
		sed -n 's/^+ //p' "$(ROCQ_TREE)/$(1)-ratchet.log" | cut -f 1 | while IFS= read -r source; do \
			base="$(ROCQ_TREE)/$(1)/$${source%.v}"; rm -f -- "$$base.vo" "$$base.vok" "$$base.vos" "$$base.glob"; \
		done; \
		echo "rocq-$(1): a warning outside ci/rocq-warnings/allowed.tsv; the objects of the sources it names are removed" >&2; \
		exit 1; \
	fi
endef
# rocq makefile prints a warning only about its own input; the compile
# options do not reach it.
define rocq_makefile
	(cd "$(ROCQ_TREE)/$(1)" && $(OPAM) rocq makefile --no-rocq-package-warning -f _RocqProject -o Makefile.rocq) \
		>"$(ROCQ_TREE)/$(1)-makefile.log" 2>&1 || { cat "$(ROCQ_TREE)/$(1)-makefile.log" >&2; exit 1; }
	@if grep -n '[Ww]arning' "$(ROCQ_TREE)/$(1)-makefile.log" >&2; then \
		echo "rocq-$(1): rocq makefile printed a warning" >&2; exit 1; fi
endef

rocq-open: rocq-sync
	$(call rocq_build,open,all)
	$(call rocq_ratchet,open)
	@echo "rocq-open: compiled $$(grep -c '\.v$$' rocq/open/_RocqProject) listed sources, no warning outside the allow-list"

rocq-quantum: rocq-open
	$(call rocq_makefile,quantum)
	$(call rocq_build,quantum,-f Makefile.rocq)
	$(call rocq_ratchet,quantum)
	@echo "rocq-quantum: compiled $$(grep -c '\.v$$' rocq/quantum/_RocqProject) listed sources, no warning outside the allow-list"

# rocq/delegation imports the standard library alone.
rocq-delegation: rocq-sync
	$(call rocq_makefile,delegation)
	$(call rocq_build,delegation,-f Makefile.rocq)
	$(call rocq_ratchet,delegation)
	@echo "rocq-delegation: compiled $$(grep -c '\.v$$' rocq/delegation/_RocqProject) listed sources, no warning outside the allow-list"

rocq: rocq-quantum rocq-delegation

gate:
	sh ci/check.sh
	sh ci/check_rocq.sh

# Removes a tree that rocq-sync created, recognized by its marker file, and
# nothing else; a BUILD_DIR that is a link keeps its target directory.
clean:
	@if [ -f "$(MARKER)" ]; then rm -r -- "$(ROCQ_TREE)"; \
	elif [ -e "$(ROCQ_TREE)" ]; then \
		echo "clean: $(ROCQ_TREE) is not a build tree of this Makefile; left in place" >&2; exit 1; \
	fi
