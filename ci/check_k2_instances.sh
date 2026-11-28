#!/bin/sh
# Usage: sh ci/check_k2_instances.sh
# The gate of rocq/k2-instances, the 64 rendered modules that certify the 21
# quadrics of K2 for the fiber E8-bar to VB over F_32029 (K2Split.order lists
# them in compile order). It runs nightly and on dispatch (the k2-instances
# workflow) and is no part of ci/check_rocq.sh: one rocq check process over all
# 64 modules was killed at 15 GB in both conversion modes, and the compile
# alone takes 15 min 49 s at three jobs (measured 2026-11-27, Rocq 9.3.0, a
# 32-thread x86-64 host). From an export of HEAD outside the checkout, under
# the opam switch of ci/install_rocq.sh:
#   0. inventory: the files of the tree, at any depth, are the sources that
#      K2Split.order lists, that file, kernel-assumptions.txt and README.md,
#      so no object or nested source rides along; no source holds an
#      admission, a declared assumption or a switched-off kernel check (a
#      textual scan, calibrated on planted lines; step 3 is the authority).
#   1. closure: rocq/quantum compiles K2CofactorSplit and what it imports,
#      under the options of its _RocqProject.
#   2. compile: each module compiles with -w all,+default; the warning tags
#      printed (a bracketed name, with or without categories, at the end of
#      a line) carry only the two names of allowed_warnings below, both rows
#      of ci/rocq-warnings/causes.tsv; the tag reader is calibrated on the
#      three shapes. A copy of the first step with one changed hexadecimal
#      digit of its last cofactor word must fail in the check lemma, at the
#      unification of its computed value with true.
#   3. kernel: rocq check -silent -o -norec re-checks each module in a
#      process of its own. With the bytecode machine a step takes at most
#      5.9 GB and 45 s, and the aggregate module, which loads the 63 others,
#      10.6 GB and 72 s; with the checker's own reduction the two steps
#      measured take 7.9 GB and 192 s (s17_00) and 8.9 GB and 212 s (s07_07),
#      and the aggregate 4.5 GB (same measurement). -norec admits what the module imports: the other
#      modules of this tree, each checked by its own process here, and the
#      rocq/quantum and Stdlib modules that ci/check_rocq.sh checks. Every
#      context summary reports nothing relying on type-in-type, an unsafe
#      fixpoint or assumed positivity, and the axioms of all summaries are
#      exactly the lines of rocq/k2-instances/kernel-assumptions.txt: 26
#      fields of Stdlib and Corelib modules, which -norec lists because it
#      admits those modules (a full check of the same imports lists none),
#      and which also lists an axiom declared in an admitted module
#      (measured 2026-11-27, Rocq 9.3.0). Calibrated on a module that
#      declares an axiom.
#   4. drift: when K2_CERTIFICATE names the pinned certificate export (an
#      untracked file of 39.6 MB whose sha256 the generator holds),
#      ci/quantum-sources/k2_cofactor_split.py --check renders the tree again
#      and requires it equal, and rejects a copy with one changed digit.
#      Without it the step reports skip.
# Environment: ROCQ_CHECK_VM (0, the default, or 1: the checker converts with
# the bytecode machine), ROCQ_JOBS (compile jobs, default 1: one compile
# peaks at 6.65 GB), ROCQ_BUILD_DIR (parent of the scratch directory, default
# $TMPDIR or /tmp; the objects take about 900 MB), K2_CERTIFICATE.
# Needs git, opam, tar, make and python3 (or PYTHON) on PATH.
# Exit status: 0 every check passed, 1 a check failed, 2 a tool or the switch
# is missing.
set -eu
PYTHON=${PYTHON:-python3}
export PYTHON
allowed_warnings='deprecated-transitive-library-file-since-Stdlib-9.0
disj-pattern-notation'

for tool in git opam tar make "$PYTHON"; do
  command -v "$tool" >/dev/null || {
    echo "check_k2_instances: $tool is not on PATH (README.md, Toolchain)" >&2
    exit 2
  }
done
switch=rocq-9.3
check_machine=
case ${ROCQ_CHECK_VM:-0} in
0) ;;
1) check_machine='-bytecode-compiler yes' ;;
*)
  echo "check_k2_instances: ROCQ_CHECK_VM is ${ROCQ_CHECK_VM}; it takes 0 or 1" >&2
  exit 2
  ;;
esac
jobs=${ROCQ_JOBS:-1}
opam switch list --short | grep -q -x -F "$switch" || {
  echo "check_k2_instances: opam switch $switch does not exist; run sh ci/install_rocq.sh" >&2
  exit 2
}

root=$(git -C "$(dirname "$0")" rev-parse --show-toplevel)
work=$(mktemp -d "${ROCQ_BUILD_DIR:-${TMPDIR:-/tmp}}/gororoba-math-k2.XXXXXXXX")
trap 'rm -r "$work" </dev/null' EXIT
trap 'exit 130' INT
trap 'exit 143' TERM
git -C "$root" archive HEAD rocq/quantum rocq/k2-instances ci/quantum-sources ci/rocq-warnings/causes.tsv | tar -x -C "$work"
tree="$work/rocq/k2-instances"
order="$tree/K2Split.order"

fail() {
  echo "check_k2_instances: $*" >&2
  exit 1
}
# run_logged LOG COMMAND...: runs the command with its output in LOG and, on
# failure, prints the end of LOG and fails.
run_logged() {
  log=$1
  shift
  "$@" >"$log" 2>&1 || {
    tail -n 40 "$log" >&2
    fail "failed: $* (log above)"
  }
}
# Prints the lines of the source files named as arguments that declare an
# admission, an assumption or a kernel-check switch. Status 0 with lines, 1
# without, 2 when grep could not read a file.
forbidden_lines() {
  grep -n -E '(^|[^A-Za-z0-9_])(Admitted|Admit|admit|Axioms?|Parameters?|Conjectures?|Hypothes[ie]s|Variables?|Context|bypass_check|Unset)([^A-Za-z0-9_]|$)' "$@"
}
# Prints the warning names of the build log $1: the first field of a
# bracketed tag that ends a line.
warning_names() {
  sed -n 's/^.*\[\([A-Za-z0-9._-]*\)\(,[A-Za-z0-9._,-]*\)\{0,1\}\]$/\1/p' "$1" | LC_ALL=C sort -u
}
# Prints, sorted, the axiom names of the context summary in the log $1.
checked_axioms() {
  awk '/^\* Axioms:/ { inside = 1; next } /^\* / { inside = 0 } inside && NF { sub(/^[ \t]+/, ""); print }' "$1" | LC_ALL=C sort -u
}
# Succeeds when the context summary in the log $1 holds its Axioms section and
# reports nothing relying on type-in-type, an unsafe fixpoint or assumed
# positivity.
context_is_closed() {
  grep -q '^\* Axioms:' "$1" || return 1
  for line in '* Constants/Inductives relying on type-in-type: <none>' \
    '* Constants/Inductives relying on unsafe (co)fixpoints: <none>' \
    '* Inductives whose positivity is assumed: <none>'; do
    grep -q -x -F "$line" "$1" || return 1
  done
}

# 0. Inventory and the textual scan.
[ -s "$order" ] || fail "rocq/k2-instances/K2Split.order is absent or empty"
(cd "$tree" && find . ! -type d | sed 's|^\./||' | LC_ALL=C sort) >"$work/files.txt"
{
  sed 's/$/.v/' "$order"
  printf 'K2Split.order\nREADME.md\nkernel-assumptions.txt\n'
} | LC_ALL=C sort >"$work/files-expected.txt"
diff "$work/files-expected.txt" "$work/files.txt" >"$work/inventory.diff" || {
  cat "$work/inventory.diff" >&2
  fail "the files of rocq/k2-instances differ from K2Split.order and the three named files (< expected, > tracked)"
}
modules=$(awk 'END { print NR }' "$order")
scan_status=0
(cd "$tree" && forbidden_lines ./*.v) >"$work/forbidden.txt" || scan_status=$?
case $scan_status in
0)
  head -n 20 "$work/forbidden.txt" >&2
  fail "a source of rocq/k2-instances holds an admission, a declared assumption or a kernel-check switch"
  ;;
1) ;;
*) fail "the textual scan could not read the sources of rocq/k2-instances (grep status $scan_status)" ;;
esac
mkdir "$work/mutant"
for planted in 'Axiom planted : False.' 'Admit Obligations.' 'Context (h : False).' 'Proof. Admitted.' 'Unset Guard Checking.'; do
  printf '%s\n' "$planted" >"$work/mutant/planted-line.v"
  forbidden_lines "$work/mutant/planted-line.v" >/dev/null || fail "calibration: the textual scan accepted the line: $planted"
done
printf 'Axiom planted : False.\n' >"$work/mutant/PlantedAxiom.v"
echo "check_k2_instances: $modules modules and three named files tracked; no admission, declared assumption or kernel-check switch"

# 1. The closure in rocq/quantum.
cd "$work/rocq/quantum"
run_logged "$work/quantum-makefile.log" opam exec --switch="$switch" -- rocq makefile --no-rocq-package-warning -f _RocqProject -o Makefile.rocq
run_logged "$work/quantum-closure.log" opam exec --switch="$switch" -- make -f Makefile.rocq --jobs="$jobs" K2CofactorSplit.vo
echo "check_k2_instances: rocq/quantum compiled K2CofactorSplit and its imports"

# 2. The compile of the tree, in the order of K2Split.order.
cd "$tree"
{
  printf -- '-Q . ""\n-Q ../quantum ""\n-arg -w\n-arg all,+default\n'
  sed 's/$/.v/' "$order"
} >_RocqProject
run_logged "$work/k2-makefile.log" opam exec --switch="$switch" -- rocq makefile --no-rocq-package-warning -f _RocqProject -o Makefile.rocq
run_logged "$work/k2-build.log" opam exec --switch="$switch" -- make --keep-going --output-sync=target -f Makefile.rocq --jobs="$jobs"
while IFS= read -r module; do
  [ -f "$module.vo" ] || fail "$module has no compiled object"
done <"$order"
printf 'Warning: one line [cal-one,cal,default]\nWarning: two lines\n[cal-two,cal]\nWarning: no category [cal-three]\n' >"$work/warning-calibration.log"
[ "$(warning_names "$work/warning-calibration.log" | tr '\n' ' ')" = 'cal-one cal-three cal-two ' ] || fail "calibration: the warning reader missed a tag shape"
warning_names "$work/k2-build.log" >"$work/warning-names.txt"
printf '%s\n' "$allowed_warnings" | LC_ALL=C sort >"$work/warning-allowed.txt"
unexpected=$(LC_ALL=C comm -23 "$work/warning-names.txt" "$work/warning-allowed.txt")
[ -z "$unexpected" ] || fail "the compile printed a warning outside the two allowed names: $unexpected"
while IFS= read -r name; do
  cut -f 1 "$work/ci/rocq-warnings/causes.tsv" | grep -q -x -F "$name" || fail "ci/rocq-warnings/causes.tsv lacks the warning $name"
done <"$work/warning-allowed.txt"
first_step=$(grep -m 1 's[0-9][0-9]_00$' "$order")
cp "$tree/$first_step.v" "$work/mutant/$first_step.v"
"$PYTHON" -I - "$work/mutant/$first_step.v" <<'PY'
import re
import sys

path = sys.argv[1]
with open(path, encoding="utf-8") as handle:
    text = handle.read()
# The last hexadecimal digit of the last packed word of the sparse cofactor table.
last = list(re.finditer(r"0x[0-9a-f]+%N", text))[-1]
at = last.end() - 3
digit = "2" if text[at] == "1" else "1"
with open(path, "w", encoding="utf-8") as handle:
    handle.write(text[:at] + digit + text[at + 1 :])
PY
if cmp -s "$tree/$first_step.v" "$work/mutant/$first_step.v"; then
  fail "calibration: the mutant equals its source"
fi
if (cd "$work/mutant" && opam exec --switch="$switch" -- rocq compile -q -w all,+default -Q . "" -Q "$tree" "" -Q "$work/rocq/quantum" "" "$first_step.v") >"$work/mutant.log" 2>&1; then
  fail "calibration: $first_step compiled with one changed digit"
fi
grep -q 'Unable to unify' "$work/mutant.log" || {
  tail -n 20 "$work/mutant.log" >&2
  fail "calibration: the mutant of $first_step failed elsewhere than at the value of its check"
}
echo "check_k2_instances: $modules modules compiled; a copy of $first_step with one changed digit is rejected"

# 3. The kernel check, one process per module.
(cd "$work/mutant" && run_logged "$work/planted-compile.log" opam exec --switch="$switch" -- rocq compile -q -Q . "" PlantedAxiom.v)
# shellcheck disable=SC2086 # check_machine holds two words or none
(cd "$work/mutant" && opam exec --switch="$switch" -- rocq check -silent -o $check_machine -Q . "" -norec PlantedAxiom) >"$work/planted-kernel.log" 2>&1 || true
checked_axioms "$work/planted-kernel.log" | grep -q -x -F 'PlantedAxiom.planted' || fail "calibration: the context summary of a module that declares an axiom omits it"
: >"$work/axioms-all.txt"
while IFS= read -r module; do
  # shellcheck disable=SC2086 # check_machine holds two words or none
  run_logged "$work/kernel-$module.log" opam exec --switch="$switch" -- rocq check -silent -o $check_machine -Q . "" -Q ../quantum "" -norec "$module"
  context_is_closed "$work/kernel-$module.log" || {
    cat "$work/kernel-$module.log" >&2
    fail "the context summary of $module lacks a section or reports an unchecked construct"
  }
  checked_axioms "$work/kernel-$module.log" >>"$work/axioms-all.txt"
done <"$order"
LC_ALL=C sort -u "$work/axioms-all.txt" >"$work/axioms.txt"
diff "$tree/kernel-assumptions.txt" "$work/axioms.txt" >"$work/axioms.diff" || {
  cat "$work/axioms.diff" >&2
  fail "the kernel checks differ from rocq/k2-instances/kernel-assumptions.txt (< ledger, > checked)"
}
{
  cat "$work/axioms.txt"
  echo PlantedAxiom.planted
} | LC_ALL=C sort -u >"$work/axioms-planted.txt"
if diff "$tree/kernel-assumptions.txt" "$work/axioms-planted.txt" >/dev/null; then
  fail "calibration: the ledger comparison accepted a declared axiom"
fi
echo "check_k2_instances: kernel check passed on $modules modules, one process each (${check_machine:-default conversion}); axioms match the ledger ($(grep -c . "$tree/kernel-assumptions.txt"))"

# 4. Drift against the pinned certificate export.
if [ -n "${K2_CERTIFICATE:-}" ]; then
  [ -f "$K2_CERTIFICATE" ] || fail "K2_CERTIFICATE names no file: $K2_CERTIFICATE"
  K2_INSTANCES_ROCQ="$work/drift-good"
  export K2_INSTANCES_ROCQ
  mkdir "$K2_INSTANCES_ROCQ" "$work/drift-mutant"
  for name in "$tree"/K2CofactorE8barVB*.v "$order"; do
    cp "$name" "$K2_INSTANCES_ROCQ/"
    cp "$name" "$work/drift-mutant/"
  done
  run_logged "$work/drift.log" "$PYTHON" -I "$work/ci/quantum-sources/k2_cofactor_split.py" "$K2_CERTIFICATE" --check
  cp "$work/mutant/$first_step.v" "$work/drift-mutant/$first_step.v"
  K2_INSTANCES_ROCQ="$work/drift-mutant"
  if "$PYTHON" -I "$work/ci/quantum-sources/k2_cofactor_split.py" "$K2_CERTIFICATE" --check >"$work/drift-mutant.log" 2>&1; then
    fail "calibration: --check accepted a tree with one changed digit"
  fi
  echo "check_k2_instances: the tree equals the rendering of the pinned export; a changed digit is rejected"
else
  echo "check_k2_instances: skip drift: K2_CERTIFICATE names no pinned certificate export"
fi
echo "check_k2_instances: passed"
