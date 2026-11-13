#!/bin/sh
# Usage: sh ci/check_rocq.sh
# The Rocq half of the admission gate. It exports the tracked rocq/ tree of
# HEAD into a scratch directory outside the checkout and, under the opam
# switch of ci/install_rocq.sh:
#   0. inventory: every tracked .v under rocq/ sits in theories/ or verified/
#      of rocq/open, in rocq/quantum, or on one of the two name lists below
#      (compiled by a make target of rocq/open; held uncompiled).
#   1. rocq/open: every tracked source of theories/ and verified/ is a line
#      of _RocqProject, which compiles them with -w +default (each warning
#      of the default set is an error); make all, check-schur-geometry,
#      check-admissions (the scanner's unit tests, then no Admitted or admit
#      in theories/ and verified/), check-plugins and extract-check pass;
#      every listed source has its .vo.
#   2. rocq/quantum: every tracked source is a line of _RocqProject; the
#      generated makefile compiles each with -w @all against
#      rocq/open/verified. Under -w @all rocq prints a warning and exits 0
#      (measured, Rocq 9.3.0), so the check that fails the build is the
#      search of the log for a warning line, calibrated on a source with a
#      deprecated import; every listed source has its .vo; the admission
#      scanner of rocq/open accepts the tree.
# Environment: ROCQ_SWITCH (default rocq-9.3), ROCQ_JOBS (default the online
# processor count), ROCQ_BUILD_DIR (parent of the scratch directory, default
# $TMPDIR or /tmp; the two trees need about 600 MB). At six jobs the whole
# script peaked at 11.9 GB of memory (systemd scope accounting, 12-thread
# x86-64 host), and a run capped at 12 GB was killed in the build of
# rocq/open; lower ROCQ_JOBS on a host with less.
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

# Sources outside the three project-listed directories. A make target of
# rocq/open compiles each source of the first list (check-schur-geometry the
# four Schur sources, extract ExtractQuaternion.v, check-plugins the two
# plugin fixtures). No recipe this script runs compiles a source of the
# second list: check-schur-geometry scans the certificate for admissions
# only, ExtractFP24Admit.v and ExtractR2VBDP4.v belong to the CertiRocq
# recipes extract-c and extract-r2vb-c, which need a rocq-certirocq switch,
# and no recipe names RustExtractSpike.v.
target_compiled='rocq/open/checkpoints/schur-geometry/CDTowerOperatorCorrespondence.v
rocq/open/checkpoints/schur-geometry/CDUnconditionalDoublingNullity.v
rocq/open/checkpoints/schur-geometry/SchurAccelerationObstruction.v
rocq/open/extraction/ExtractQuaternion.v
rocq/open/tests/MathCompMatrixCompatibility.v
rocq/open/tests/PluginCompatibility.v
rocq/open/tests/SchurAccelerationBoundaries.v'
held_uncompiled='rocq/open/checkpoints/schur-geometry/NullityTwelveCoefficientCertificate.v
rocq/open/extraction/ExtractFP24Admit.v
rocq/open/extraction/ExtractR2VBDP4.v
rocq/open/extraction/RustExtractSpike.v'

# Fails unless the sources of the list $1 that lie outside the three
# project-listed directories are exactly the two lists above, printing the
# difference.
outside_sources_match() {
  grep -v -E '^rocq/(open/(theories|verified)|quantum)/' "$1" | LC_ALL=C sort >"$work/outside.txt" || true
  printf '%s\n%s\n' "$target_compiled" "$held_uncompiled" | LC_ALL=C sort >"$work/outside-named.txt"
  diff "$work/outside-named.txt" "$work/outside.txt"
}
# Fails when a line of the newline-separated source list $2 is absent, as a
# whole line, from the project file $1, printing each absent one. An empty
# project file lists nothing, so every source is absent from it.
unlisted_sources() {
  status=0
  grep -F -x -v -f "$1" "$2" || status=$?
  case $status in
    0) return 1 ;;
    1) return 0 ;;
    *) return 2 ;;
  esac
}
# Succeeds when a log among the arguments holds a warning line, printing it.
log_holds_warning() {
  grep -n '[Ww]arning' "$@"
}

git -C "$root" ls-files -- 'rocq/*.v' >"$work/tracked-sources.txt"
if grep -n '[[:space:]]' "$work/tracked-sources.txt" >&2; then
  echo "check_rocq: the tracked sources above hold whitespace in their path, which a project file cannot list" >&2
  exit 1
fi
outside_sources_match "$work/tracked-sources.txt" >"$work/outside.diff" || {
  echo "check_rocq: sources outside the project-listed directories differ from the lists in ci/check_rocq.sh (< named, > tracked):" >&2
  cat "$work/outside.diff" >&2
  exit 1
}
{
  cat "$work/tracked-sources.txt"
  echo rocq/open/tests/UnnamedSourceCalibration.v
} >"$work/tracked-sources-bad.txt"
if outside_sources_match "$work/tracked-sources-bad.txt" >/dev/null; then
  echo "check_rocq: the inventory check accepted a source that neither list names" >&2
  exit 1
fi
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
    # A compiler error or a killed process can sit far above the tail of a
    # parallel build's log.
    grep -n -E '^(Error|File ")|Killed|Out of memory|\*\*\* \[' "$log" | tail -n 20 >&2 || true
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
# A name that extends a listed one after a space, and an empty project file.
echo 'theories/Prelude.v extra.v' >"$work/open-sources-bad.txt"
: >"$work/empty-project.txt"
if unlisted_sources _RocqProject "$work/open-sources-bad.txt" >/dev/null ||
  unlisted_sources "$work/empty-project.txt" "$work/open-sources.txt" >/dev/null; then
  echo "check_rocq: the listing check accepted a name that extends a listed one, or an empty project file" >&2
  exit 1
fi
for target in all check-schur-geometry check-admissions check-plugins extract-check; do
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
# The tree has two logical roots and installs no package, the case in which
# rocq makefile asks for --no-rocq-package-warning; any other line it prints
# that names a warning still fails the check below.
run_logged "$work/quantum-makefile.log" opam exec --switch="$switch" -- rocq makefile --no-rocq-package-warning -f _RocqProject -o Makefile.rocq
run_logged "$work/quantum-all.log" opam exec --switch="$switch" -- make -f Makefile.rocq --jobs="$jobs"
mkdir "$work/warning-calibration"
echo 'From Coq Require Import List.' >"$work/warning-calibration/DeprecatedPrefix.v"
(
  cd "$work/warning-calibration"
  run_logged "$work/warning-calibration.log" opam exec --switch="$switch" -- rocq compile -q -w @all -Q . "" DeprecatedPrefix.v
)
log_holds_warning "$work/warning-calibration.log" >/dev/null || {
  echo "check_rocq: rocq compile -w @all printed no warning for a deprecated import, so the log search cannot fail the build" >&2
  exit 1
}
if log_holds_warning "$work/quantum-makefile.log" "$work/quantum-all.log" >&2; then
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
