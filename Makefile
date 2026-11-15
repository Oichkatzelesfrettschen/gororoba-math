# Working-tree builds of gororoba-math, for GNU make. The admission gate
# (ci/check.sh, ci/check_rocq.sh) builds an export of HEAD; these targets
# build the files as they stand, edits included, and leave the source
# directories of rocq/ without build products.
#
#   make lean           lake build --wfail in lean/ (the Lake tree is lean/.lake)
#   make rocq-open      rocq/open: make all, in $(BUILD_DIR)/rocq/open
#   make rocq-quantum   rocq/open, which rocq/quantum reads, then
#                       rocq/quantum with -w @all; a warning line from the
#                       makefile generator or the build fails the target
#   make rocq-delegation  rocq/delegation with -w +default
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
# (-w +default in rocq/open and rocq/delegation, -w @all in rocq/quantum);
# this file adds no compiler option. rocq/open/Makefile adds the Flocq
# library root of the switch, as it does under the gate.

BUILD_DIR ?= build
ROCQ_SWITCH ?= rocq-9.3
ROCQ_JOBS ?= $(shell getconf _NPROCESSORS_ONLN)

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
	'/open/html/' '/open/metrics/' '/quantum-build.log' \
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

rocq-open: rocq-sync
	$(OPAM) make -C "$(ROCQ_TREE)/open" --jobs=$(ROCQ_JOBS) all

# Under -w @all rocq prints a warning and exits 0 (ci/check_rocq.sh), so the
# search of the log, which holds the output of the makefile generator and
# of the build, is the check that fails the target. A source that warned
# has left its object behind, and a second run would find it up to date and
# print nothing, so a log with a warning removes the objects of rocq/quantum,
# whether the build itself passed or failed. The build runs with
# --no-print-directory, which keeps the build directory's own name out of
# the searched log.
rocq-quantum: rocq-open
	(cd "$(ROCQ_TREE)/quantum" && $(OPAM) rocq makefile --no-rocq-package-warning -f _RocqProject -o Makefile.rocq) \
		>"$(ROCQ_TREE)/quantum-build.log" 2>&1 || { cat "$(ROCQ_TREE)/quantum-build.log" >&2; exit 1; }
	@status=0; $(OPAM) make --no-print-directory -C "$(ROCQ_TREE)/quantum" -f Makefile.rocq --jobs=$(ROCQ_JOBS) \
		>>"$(ROCQ_TREE)/quantum-build.log" 2>&1 || status=$$?; \
	if [ "$$status" -ne 0 ]; then tail -n 60 "$(ROCQ_TREE)/quantum-build.log" >&2; fi; \
	if grep -n '[Ww]arning' "$(ROCQ_TREE)/quantum-build.log" >&2; then \
		find "$(ROCQ_TREE)/quantum" \( -name '*.vo' -o -name '*.vok' -o -name '*.vos' -o -name '*.glob' \) -exec rm -f -- {} +; \
		echo "rocq-quantum: the makefile generator or the build printed a warning; the objects of rocq/quantum are removed" >&2; exit 1; fi; \
	exit "$$status"
	@echo "rocq-quantum: compiled $$(grep -c '\.v$$' rocq/quantum/_RocqProject) listed sources, no warning"

# rocq/delegation imports the standard library alone.
rocq-delegation: rocq-sync
	cd "$(ROCQ_TREE)/delegation" && $(OPAM) rocq makefile --no-rocq-package-warning -f _RocqProject -o Makefile.rocq
	$(OPAM) make --no-print-directory -C "$(ROCQ_TREE)/delegation" -f Makefile.rocq --jobs=$(ROCQ_JOBS)
	@echo "rocq-delegation: compiled $$(grep -c '\.v$$' rocq/delegation/_RocqProject) listed sources"

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
