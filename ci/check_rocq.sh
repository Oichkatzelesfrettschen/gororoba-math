#!/bin/sh
# Usage: sh ci/check_rocq.sh
# The Rocq half of the admission gate. It exports the tracked rocq/ tree of
# HEAD into a scratch directory outside the checkout and, under the opam
# switch of ci/install_rocq.sh:
#   1. rocq/open: every tracked source of theories/ and verified/ is listed
#      in _RocqProject; make all, check-schur-geometry, check-admissions
#      (the scanner's unit tests, then no Admitted or admit in theories/ and
#      verified/) and extract-check pass; every listed source has its .vo.
#   2. rocq/quantum: every tracked source is listed in _RocqProject; the
#      generated makefile compiles each with -w @all against
#      rocq/open/verified; the log holds no warning; every listed source
#      has its .vo; the admission scanner of rocq/open accepts the tree.
# Environment: ROCQ_SWITCH (default rocq-9.3), ROCQ_JOBS (default the online
# processor count), ROCQ_BUILD_DIR (parent of the scratch directory, default
# $TMPDIR or /tmp; the two trees need about 600 MB).
# Needs git, opam, tar, make, rustc and getconf on PATH. Exit status: 0 every
# check passed, 1 a check failed, 2 a tool or the switch is missing.
set -eu

for tool in git opam tar make rustc getconf; do
  command -v "$tool" >/dev/null || {
    echo "check_rocq: $tool is not on PATH (README.md, Toolchain)" >&2
    exit 2
  }
done
switch=${ROCQ_SWITCH:-rocq-9.3}
jobs=${ROCQ_JOBS:-$(getconf _NPROCESSORS_ONLN)}
opam switch list --short | grep -q -x -F "$switch" || {
  echo "check_rocq: opam switch $switch does not exist; run sh ci/install_rocq.sh" >&2
  exit 2
}

root=$(git -C "$(dirname "$0")" rev-parse --show-toplevel)
work=$(mktemp -d "${ROCQ_BUILD_DIR:-${TMPDIR:-/tmp}}/gororoba-math-rocq.XXXXXXXX")
trap 'rm -r "$work"' EXIT INT TERM
git -C "$root" archive HEAD rocq | tar -x -C "$work"

# Fails when a source of the newline-separated list $2 is absent from the
# project file $1, printing each absent one.
unlisted_sources() {
  awk 'NR == FNR { listed[$1] = 1; next } !($1 in listed) { print; missing = 1 } END { exit missing }' "$1" "$2"
}
# Fails when a .v source listed in the project file $1 (run in its
# directory) has no .vo beside it, printing each such source.
uncompiled_sources() {
  grep '\.v$' "$1" | while IFS= read -r source; do
    [ -f "${source}o" ] || echo "$source"
  done >"$work/uncompiled.txt"
  [ ! -s "$work/uncompiled.txt" ] || {
    cat "$work/uncompiled.txt"
    return 1
  }
}
run_logged() {
  log=$1
  shift
  "$@" >"$log" 2>&1 || {
    tail -n 60 "$log" >&2
    echo "check_rocq: failed: $*" >&2
    exit 1
  }
}

cd "$work/rocq/open"
git -C "$root" ls-files -- 'rocq/open/theories/*.v' 'rocq/open/verified/*.v' | sed 's|^rocq/open/||' >"$work/open-sources.txt"
[ -s "$work/open-sources.txt" ] || {
  echo "check_rocq: git tracks no source under rocq/open/theories or rocq/open/verified" >&2
  exit 1
}
unlisted_sources _RocqProject "$work/open-sources.txt" >"$work/unlisted.txt" || {
  echo "check_rocq: rocq/open/_RocqProject does not list:" >&2
  cat "$work/unlisted.txt" >&2
  exit 1
}
{
  cat "$work/open-sources.txt"
  echo theories/OmittedSourceCalibration.v
} >"$work/open-sources-bad.txt"
if unlisted_sources _RocqProject "$work/open-sources-bad.txt" >/dev/null; then
  echo "check_rocq: the listing check accepted a source the project file omits" >&2
  exit 1
fi
for target in all check-schur-geometry check-admissions extract-check; do
  run_logged "$work/open-$target.log" opam exec --switch="$switch" -- make --jobs="$jobs" "$target"
  echo "check_rocq: rocq/open $target passed"
done
uncompiled_sources _RocqProject || {
  echo "check_rocq: rocq/open sources above have no .vo" >&2
  exit 1
}
echo "check_rocq: rocq/open compiled all $(grep -c '\.v$' _RocqProject) listed sources"

cd "$work/rocq/quantum"
git -C "$root" ls-files -- 'rocq/quantum/*.v' | sed 's|^rocq/quantum/||' >"$work/quantum-sources.txt"
[ -s "$work/quantum-sources.txt" ] || {
  echo "check_rocq: git tracks no source under rocq/quantum" >&2
  exit 1
}
unlisted_sources _RocqProject "$work/quantum-sources.txt" >"$work/unlisted.txt" || {
  echo "check_rocq: rocq/quantum/_RocqProject does not list:" >&2
  cat "$work/unlisted.txt" >&2
  exit 1
}
run_logged "$work/quantum-makefile.log" opam exec --switch="$switch" -- rocq makefile -f _RocqProject -o Makefile.rocq
run_logged "$work/quantum-all.log" opam exec --switch="$switch" -- make -f Makefile.rocq --jobs="$jobs"
if grep -n '[Ww]arning' "$work/quantum-makefile.log" "$work/quantum-all.log" >&2; then
  echo "check_rocq: the rocq/quantum build printed a warning" >&2
  exit 1
fi
uncompiled_sources _RocqProject || {
  echo "check_rocq: rocq/quantum sources above have no .vo" >&2
  exit 1
}
run_logged "$work/quantum-admissions.log" "$work/rocq/.cache/proof-admission-check/admission-check" "$work/rocq/quantum/"
echo "check_rocq: rocq/quantum compiled all $(grep -c '\.v$' _RocqProject) listed sources with no warning and no admission"
echo "check_rocq: passed"
