# Rocq proof build system for open_gororoba formal verification.
#
# WHY:  Machine-checked proofs elevate claim evidence from "tested at
#       sample points" to "proven for all valid inputs."
# WHAT: Compiles .v files to kernel-checked .vo proof objects.
# HOW:  opam exec --switch=rocq-9.3 -- make --jobs="$(nproc)" all
#
# REQUIRES: opam switch rocq-9.3 with rocq-core 9.3.0.

# Guard: require an opam switch with the pinned Rocq toolchain and the
# matching Flocq compiled library. Compiled Flocq objects carry the OCaml
# runtime identity, so a Rocq binary from one switch cannot consume objects
# built by another switch.
ifndef OPAM_SWITCH_PREFIX
$(error OPAM_SWITCH_PREFIX is not set. Run: opam exec --switch=rocq-9.3 -- make)
endif

# FP24Representable.v imports Flocq.Core. Keep the dependency in the active
# opam switch and map its physical installation to the Flocq logical root.
# FLOCQ_ROOT remains overrideable for reproducible CI or a hermetic build.
FLOCQ_ROOT ?= $(if $(OPAM_SWITCH_PREFIX),$(OPAM_SWITCH_PREFIX)/lib/coq/user-contrib/Flocq,$(shell opam var lib 2>/dev/null)/coq/user-contrib/Flocq)
FLOCQ_CORE_VO := $(FLOCQ_ROOT)/Core/Core.vo
ifeq ($(wildcard $(FLOCQ_CORE_VO)),)
$(error Flocq Core.vo is missing at $(FLOCQ_CORE_VO). Install coq-flocq.4.2.2 in the active Rocq switch.)
endif
ROCQ_EXTERNAL_ARGS := -R "$(FLOCQ_ROOT)" Flocq
# The dependency scanner must not turn installed Flocq sources into build
# targets under the opam prefix. Compiler invocations receive ROCQ_EXTERNAL_ARGS
# and consume the installed .vo objects directly.
ROCQ_PROJECT_FLAGS := -f _RocqProject

# The proof corpus has two logical roots and produces local proof objects.
# Findlib package installation requires exactly one root; select the supported
# standalone generation mode while retaining the fatal warning check below.
ROCQMAKEFILE := rocq makefile --no-rocq-package-warning
ROCQMAKEFILE_WARN_RE := [Ww]arning

# OCaml 5 GC tuning: only `o=` (space_overhead) is effective.
# WHY: OCaml 5 ignores s= (initial heap), i= (minor heap size), O= (compaction).
#      o=200 lets major GC tolerate 200% overhead before collecting, reducing
#      pauses during large `ring` term construction (C912 peaks at ~300MB).
export OCAMLRUNPARAM ?= o=200

# Prefer _RocqProject (Rocq 9.x native), fall back to _CoqProject.
PROJ_FILE := $(shell if [ -f _RocqProject ]; then echo _RocqProject; else echo _CoqProject; fi)

# GNU make's default behavior leaves a target file in place when its
# recipe exits non-zero, which means a Makefile.rocq written by
# rocq-makefile before the warning grep fires would survive across
# invocations and let `make vos` / `make vok` skip the warnings-as-
# errors gate on the next run. .DELETE_ON_ERROR forces make to delete
# any target whose recipe failed, restoring fail-closed semantics.
.DELETE_ON_ERROR:

Makefile.rocq: $(PROJ_FILE) Makefile
	@tmp_log=$$(mktemp); \
	if ! $(ROCQMAKEFILE) -f $(PROJ_FILE) -o Makefile.rocq >"$$tmp_log" 2>&1; then \
	  cat "$$tmp_log"; \
	  rm -f "$$tmp_log" Makefile.rocq Makefile.rocq.conf .Makefile.rocq.d; \
	  exit 1; \
	fi; \
	if grep -n "$(ROCQMAKEFILE_WARN_RE)" "$$tmp_log"; then \
	  cat "$$tmp_log"; \
	  echo "FAIL: rocq makefile emitted a warning; warnings are errors."; \
	  rm -f "$$tmp_log" Makefile.rocq Makefile.rocq.conf .Makefile.rocq.d; \
	  exit 1; \
	fi; \
	cat "$$tmp_log"; \
	rm -f "$$tmp_log"

rocq-makefile-check:
	@tmp_log=$$(mktemp); tmp_make=.Makefile.rocq.check.$$$$; \
	if ! $(ROCQMAKEFILE) -f $(PROJ_FILE) -o "$$tmp_make" >"$$tmp_log" 2>&1; then \
	  cat "$$tmp_log"; \
	  rm -f "$$tmp_log" "$$tmp_make" "$$tmp_make.conf" ".$$tmp_make.d"; \
	  exit 1; \
	fi; \
	if grep -n "$(ROCQMAKEFILE_WARN_RE)" "$$tmp_log"; then \
	  cat "$$tmp_log"; \
	  echo "FAIL: rocq makefile emitted a warning; warnings are errors."; \
	  rm -f "$$tmp_log" "$$tmp_make" "$$tmp_make.conf" ".$$tmp_make.d"; \
	  exit 1; \
	fi; \
	cat "$$tmp_log"; \
	rm -f "$$tmp_log" "$$tmp_make" "$$tmp_make.conf" ".$$tmp_make.d"; \
	echo "OK: rocq makefile completed without warnings."

all: Makefile.rocq
	$(MAKE) --keep-going -f Makefile.rocq all \
		COQEXTRAFLAGS="$(ROCQ_EXTERNAL_ARGS)" VDFILE_FLAGS="$(ROCQ_PROJECT_FLAGS)"

# --- Fast two-phase build pipeline ---
#
# Phase 1: vos (compiled interfaces) -- skips all proof bodies.
#   Checks that definitions, theorem statements, and cross-module
#   imports are well-formed. Seconds, not minutes.
#
# Phase 2: vok (proof checking) -- checks every proof body in parallel.
#   Each file is independent once .vos interfaces exist.
#   Uses every process-visible CPU supplied by the invoking Make jobserver.
#
# Workflow:
#   make vos   # instant interface check (iterative dev)
#   make vok   # full proof verification (CI / pre-commit)

vos: Makefile.rocq
	$(MAKE) --keep-going -f Makefile.rocq vos \
		COQEXTRAFLAGS="$(ROCQ_EXTERNAL_ARGS)" VDFILE_FLAGS="$(ROCQ_PROJECT_FLAGS)"

vok: Makefile.rocq
	$(MAKE) --keep-going -f Makefile.rocq vok \
		COQEXTRAFLAGS="$(ROCQ_EXTERNAL_ARGS)" VDFILE_FLAGS="$(ROCQ_PROJECT_FLAGS)"

# --- Standard targets ---

clean: Makefile.rocq
	$(MAKE) -f Makefile.rocq clean
	rm -f Makefile.rocq Makefile.rocq.conf .Makefile.rocq.d
	rm -f Makefile.coq Makefile.coq.conf .Makefile.coq.d

RUSTC ?= rustc
ADMISSION_CHECK_DIR := $(CURDIR)/../.cache/proof-admission-check
ADMISSION_CHECK := $(ADMISSION_CHECK_DIR)/admission-check
ADMISSION_CHECK_TEST := $(ADMISSION_CHECK_DIR)/admission-check-tests

$(ADMISSION_CHECK): admission_check.rs
	@mkdir -p "$(ADMISSION_CHECK_DIR)"
	$(RUSTC) --edition=2024 -D warnings $< -o "$@"

$(ADMISSION_CHECK_TEST): admission_check.rs
	@mkdir -p "$(ADMISSION_CHECK_DIR)"
	$(RUSTC) --edition=2024 -D warnings --test $< -o "$@"

.PHONY: check-admissions scan-admissions test-admission-check
test-admission-check: $(ADMISSION_CHECK_TEST)
	"$(ADMISSION_CHECK_TEST)"

scan-admissions: $(ADMISSION_CHECK)
	"$(ADMISSION_CHECK)" theories/ verified/

check-admissions: test-admission-check scan-admissions
	@echo "OK: admission unit tests and repository scan passed."

check: all check-admissions

check-plugins:
	rocq compile -q -w +default tests/MathCompMatrixCompatibility.v
	rocq compile -q -w +default tests/PluginCompatibility.v

# Schur geometry and nullity-doubling sources remain outside the canonical project until receipt renewal.
.PHONY: check-schur-geometry
check-schur-geometry: all $(ADMISSION_CHECK)
	"$(ADMISSION_CHECK)" checkpoints/schur-geometry/ tests/SchurAccelerationBoundaries.v
	rocq compile -q -w +default -Q theories OpenGororoba -Q checkpoints/schur-geometry OpenGororobaCheckpoint checkpoints/schur-geometry/CDTowerOperatorCorrespondence.v
	rocq compile -q -w +default -Q theories OpenGororoba -Q checkpoints/schur-geometry OpenGororobaCheckpoint checkpoints/schur-geometry/SchurAccelerationObstruction.v
	rocq compile -q -w +default -Q theories OpenGororoba -Q checkpoints/schur-geometry OpenGororobaCheckpoint checkpoints/schur-geometry/CDUnconditionalDoublingNullity.v
	rocq compile -q -w +default -Q theories OpenGororoba -Q checkpoints/schur-geometry OpenGororobaCheckpoint -Q tests OpenGororobaTests tests/SchurAccelerationBoundaries.v
	rocq check -silent -o -Q theories OpenGororoba -Q checkpoints/schur-geometry OpenGororobaCheckpoint -Q tests OpenGororobaTests OpenGororobaCheckpoint.CDTowerOperatorCorrespondence OpenGororobaCheckpoint.SchurAccelerationObstruction OpenGororobaCheckpoint.CDUnconditionalDoublingNullity OpenGororobaTests.SchurAccelerationBoundaries
	@mkdir -p "$(ADMISSION_CHECK_DIR)"
	$(RUSTC) --edition=2024 -D warnings tests/schur_acceleration_mutations.rs -o "$(ADMISSION_CHECK_DIR)/schur-acceleration-mutations"
	"$(ADMISSION_CHECK_DIR)/schur-acceleration-mutations" "$(CURDIR)" "$(ADMISSION_CHECK_DIR)/schur-acceleration-mutations-output"
	$(RUSTC) --edition=2024 -D warnings tests/doubling_nullity_mutations.rs -o "$(ADMISSION_CHECK_DIR)/doubling-nullity-mutations"
	"$(ADMISSION_CHECK_DIR)/doubling-nullity-mutations" "$(CURDIR)" "$(ADMISSION_CHECK_DIR)/doubling-nullity-mutations-output"

extract: all
	@echo "Extracting OCaml code from Rocq..."
	@mkdir -p extraction/golden
	@if [ -f extraction/ExtractQuaternion.v ]; then \
	  rocq compile -Q theories OpenGororoba -Q verified OpenGororobaVerified \
	    extraction/ExtractQuaternion.v; \
	fi

extract-check: extract
	@echo "Checking extraction golden file..."
	@if [ -f extraction/golden/extracted_quat.ml.golden ]; then \
	  diff -u extraction/golden/extracted_quat.ml.golden extraction/extracted_quat.ml && \
	  echo "MATCH: extraction output matches golden file" || \
	  (echo "DIFF: extraction output differs from golden file"; exit 1); \
	else echo "SKIP: no golden file yet"; fi

# Gallina -> C emission via CertiRocq (rocq-certirocq 0.9.1+9.1), run under
# the rocq-certirocq switch. The C is correct relative to a trusted base, which
# the headers of extraction/ExtractFP24Admit.v and extraction/ExtractR2VBDP4.v
# list. Each emission target removes its expected outputs before it compiles,
# so a file left by an earlier run cannot stand in for a missing one; outputs
# land in extraction/ (ignored by git). The compiler version is captured before
# it is trimmed, so a failing gcc fails the record step.
ROCQ_EXTRACT_ARGS = $(ROCQ_EXTERNAL_ARGS) -R theories OpenGororoba -R verified OpenGororobaVerified
GCC_VERSION = v=$$(gcc --version) && printf '%s\n' "$$v" | head -n 1
FP24_C := OpenGororoba.FP24Representable.sint_range_admit
extract-c: all
	@echo "Emitting C of $(FP24_C) from Rocq via CertiRocq..."
	@rm -f $(FP24_C).c $(FP24_C).h extraction/$(FP24_C).c extraction/$(FP24_C).h
	@rocq compile $(ROCQ_EXTRACT_ARGS) extraction/ExtractFP24Admit.v
	@mv $(FP24_C).c $(FP24_C).h extraction/
	@echo "Emitted extraction/$(FP24_C).{c,h}"

# Emission of the R2VB DP4 transform kernel: the two theories it reads are
# compiled first under the running switch, so no object of another build is
# read, then extraction/ExtractR2VBDP4.v emits dp4 and dp4_operand_admit plus
# the Z/positive/bool constructor glue.
R2VB_C := OpenGororoba.R2VBTransformDP4.dp4.c OpenGororoba.R2VBTransformDP4.dp4.h \
  OpenGororoba.R2VBTransformDP4.dp4_operand_admit.c OpenGororoba.R2VBTransformDP4.dp4_operand_admit.h \
  r2vb_dp4_glue.c r2vb_dp4_glue.h
extract-r2vb-c:
	@echo "Emitting R2VB DP4 C from Rocq via CertiRocq..."
	@rm -f $(R2VB_C) $(addprefix extraction/,$(R2VB_C))
	@rocq compile $(ROCQ_EXTRACT_ARGS) theories/FP24Representable.v
	@rocq compile $(ROCQ_EXTRACT_ARGS) theories/R2VBTransformDP4.v
	@rocq compile $(ROCQ_EXTRACT_ARGS) extraction/ExtractR2VBDP4.v
	@mv $(R2VB_C) extraction/
	@echo "Emitted extraction/OpenGororoba.R2VBTransformDP4.*.{c,h} and glue"

# Compare the emitted sources and headers and the glue
# (golden/r2vb_dp4_extraction.sha256), and every .c and .h of the CertiRocq
# runtime (golden/certirocq_runtime.sha256: package bytes, equal on two hosts
# measured 2026-11-16), with the retained hashes. The prebuilt runtime objects
# and the C compiler depend on the host, so extraction/r2vb_dp4_record.txt
# records them with the switch packages instead of comparing them.
extract-r2vb-check: extract-r2vb-c
	@RT="$$(opam var lib)/coq/user-contrib/CertiRocq/Plugin/runtime"; \
	cd extraction && \
	sha256sum $(R2VB_C) >r2vb_dp4_extraction.sha256.new && \
	(cd "$$RT" && LC_ALL=C ls -- *.c *.h | while IFS= read -r f; do sha256sum -- "$$f"; done) \
	  >certirocq_runtime.sha256.new && \
	diff -u golden/r2vb_dp4_extraction.sha256 r2vb_dp4_extraction.sha256.new && \
	diff -u golden/certirocq_runtime.sha256 certirocq_runtime.sha256.new && \
	{ opam list --installed --columns=name,version rocq-core rocq-certirocq coq-flocq ocaml-base-compiler && \
	  (cd "$$RT" && sha256sum -- *.o) && $(GCC_VERSION); } >r2vb_dp4_record.txt && \
	echo "MATCH: R2VB extraction and CertiRocq runtime hashes match golden; record in extraction/r2vb_dp4_record.txt" || \
	{ echo "DIFF: R2VB extraction or CertiRocq runtime hashes differ from golden"; exit 1; }

# Build and run the correspondence harnesses: the extracted dp4 against a
# native integer reference over nine fixtures spanning the B = 181 admission
# boundary, and the extracted gate against its native predicate over five
# known-good and four known-bad rows. Each unit compiles with warnings as
# errors under the narrowest options measured with gcc 15.2: the hand-written
# harnesses under -Wall -Wextra; the emitted units with int-conversion off,
# since CertiRocq puns function pointers into value (long); the glue also
# with format and format-security off, since it prints constructor names
# through non-literal format strings; and gc_stack.c, compiled here from the
# runtime source that golden/certirocq_runtime.sha256 pins, under the default
# warnings. extraction/r2vb_dp4_test_record.txt records the compiler and the
# digests of both binaries.
R2VB_CC = gcc -O1 -std=gnu11
HAND_WARN = -Wall -Wextra -Werror
GEN_WARN = -Werror -Wno-int-conversion
GLUE_WARN = $(GEN_WARN) -Wno-format -Wno-format-security
test-r2vb-correspondence:
	@RT="$$(opam var lib)/coq/user-contrib/CertiRocq/Plugin/runtime"; \
	cd extraction && \
	$(R2VB_CC) -Werror -I "$$RT" -c "$$RT/gc_stack.c" -o gc_stack.o && \
	$(R2VB_CC) $(GEN_WARN) -I "$$RT" -c OpenGororoba.R2VBTransformDP4.dp4.c -o dp4.o && \
	$(R2VB_CC) $(GEN_WARN) -I "$$RT" -c OpenGororoba.R2VBTransformDP4.dp4_operand_admit.c -o dp4_operand_admit.o && \
	$(R2VB_CC) $(GLUE_WARN) -I "$$RT" -c r2vb_dp4_glue.c -o r2vb_dp4_glue.o && \
	$(R2VB_CC) $(HAND_WARN) -I "$$RT" -c test_r2vb_dp4_correspondence.c -o test_r2vb_dp4_correspondence.o && \
	$(R2VB_CC) $(HAND_WARN) -I "$$RT" -c test_r2vb_dp4_admit_correspondence.c -o test_r2vb_dp4_admit_correspondence.o && \
	$(R2VB_CC) -o test_r2vb_dp4 test_r2vb_dp4_correspondence.o dp4.o r2vb_dp4_glue.o gc_stack.o && \
	$(R2VB_CC) -o test_r2vb_dp4_admit test_r2vb_dp4_admit_correspondence.o dp4_operand_admit.o r2vb_dp4_glue.o gc_stack.o && \
	{ $(GCC_VERSION) && sha256sum test_r2vb_dp4 test_r2vb_dp4_admit; } >r2vb_dp4_test_record.txt && \
	./test_r2vb_dp4 && ./test_r2vb_dp4_admit

# Compile-check the emitted FP24 C against the CertiRocq runtime headers under
# the emitted-unit options; a missing emission fails. The check compiles; it
# compares no digest (no golden file pins this emission).
extract-c-check: extract-c
	@RT="$$(opam var lib)/coq/user-contrib/CertiRocq/Plugin/runtime"; \
	echo "Compile-checking emitted C against $$RT ..."; \
	$(R2VB_CC) $(GEN_WARN) -I "$$RT" -c -o /dev/null extraction/$(FP24_C).c && \
	echo "PASS: emitted FP24 C compiles with warnings as errors" || \
	{ echo "FAIL: emitted C did not compile"; exit 1; }

count:
	@echo "Theory files:  $$(ls theories/*.v 2>/dev/null | wc -l)"
	@echo "Verified files: $$(ls verified/*.v 2>/dev/null | wc -l)"
	@echo "Total .v files: $$(ls theories/*.v verified/*.v 2>/dev/null | wc -l)"
	@echo "Compiled .vo:   $$(ls theories/*.vo verified/*.vo 2>/dev/null | wc -l)"
	@echo "Interfaces .vos: $$(ls theories/*.vos verified/*.vos 2>/dev/null | wc -l)"
	@echo "Checked .vok:    $$(ls theories/*.vok verified/*.vok 2>/dev/null | wc -l)"

.PHONY: all vos vok clean check check-plugins extract extract-check extract-c extract-c-check extract-r2vb-c extract-r2vb-check test-r2vb-correspondence count rocq-makefile-check
