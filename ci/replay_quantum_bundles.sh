#!/bin/sh
# Usage: GOROROBA_QUANTUM=PATH [ROCQ=PATH] [GOROROBA_ROOT=PATH] \
#          sh ci/replay_quantum_bundles.sh [BUNDLE...]
# Runs the retained Rocq replays of the gororoba-quantum checkout at
# $GOROROBA_QUANTUM against the sources of this checkout's rocq/quantum.
# Each BUNDLE names a directory docs/evidence/BUNDLE of that checkout that
# holds a replay_rocq.sh, or TargetFlipN21 (compile with -w +all, no
# warning, rocq check on rocq/quantum/TargetFlipN21.v). With no BUNDLE every
# such bundle runs, one after the other. A bundle's script runs unchanged
# from a shadow root whose proofs/ holds the files of rocq/quantum and whose
# other entries are links to the gororoba-quantum checkout, so its reads of
# proofs/NAME.v land here; before it runs, every proofs/ row of the bundle's
# source_hashes.sha256 is compared with the shadow copy, so a source that
# differs from the digest its record holds fails the bundle. A bundle whose
# script reads GOROROBA_ROOT (a gororoba-open checkout at the commit its
# README names) is skipped, with a line saying so, while GOROROBA_ROOT is
# unset, and a named bundle that needs it ends the run with status 2.
# ROCQ names the rocq executable (default rocq on PATH); a switch is used
# as `opam exec --switch=rocq-9.3 -- sh ci/replay_quantum_bundles.sh`. The
# bundle scripts require the toolchain banner of their toolchain.txt. The
# folding_proofs bundle also compares its stdout with its retained
# rocq_replay.log. Runs on demand, outside the admission gate, because it
# reads another repository and needs Rocq. Peak memory is that of one
# bundle's compile (the Stiefel bundle takes about nine minutes).
# Exit status: 0 at least one bundle passed and none failed, 1 a bundle
# failed or none ran, 2 a tool, the checkout or a name is missing. Writes
# only under a temporary directory it removes.
set -eu

for tool in git cp cmp grep sha256sum mktemp sh; do
  command -v "$tool" >/dev/null || {
    echo "replay_quantum_bundles: $tool is not on PATH" >&2
    exit 2
  }
done
rocq=${ROCQ:-rocq}
command -v "$rocq" >/dev/null || {
  echo "replay_quantum_bundles: $rocq is not on PATH; set ROCQ or run under opam exec" >&2
  exit 2
}
quantum=${GOROROBA_QUANTUM:?replay_quantum_bundles: set GOROROBA_QUANTUM to a gororoba-quantum checkout}
[ -d "$quantum/docs/evidence" ] || {
  echo "replay_quantum_bundles: $quantum/docs/evidence does not exist" >&2
  exit 2
}
quantum=$(CDPATH='' cd -- "$quantum" && pwd)
root=$(git -C "$(dirname "$0")" rev-parse --show-toplevel)
work=$(mktemp -d)
trap 'rm -r "$work"' EXIT INT TERM

if [ "$#" -eq 0 ]; then
  explicit=0
  set -- $(for script in "$quantum"/docs/evidence/*/replay_rocq.sh; do
    basename "$(dirname "$script")"
  done) TargetFlipN21
else
  explicit=1
fi

# Builds the shadow root of bundle $1 in $work/shadow-$1.
make_shadow() {
  shadow="$work/shadow-$1"
  mkdir -p "$shadow/proofs" "$shadow/docs/evidence"
  cp "$root"/rocq/quantum/*.v "$shadow/proofs/"
  cp -R "$quantum/docs/evidence/$1" "$shadow/docs/evidence/$1"
  for entry in "$quantum"/* "$quantum"/.[!.]*; do
    [ -e "$entry" ] || continue
    case "$(basename "$entry")" in
    proofs | .git | docs) ;;
    *) ln -s "$entry" "$shadow/$(basename "$entry")" ;;
    esac
  done
  for entry in "$quantum"/docs/*; do
    [ "$(basename "$entry")" = evidence ] || ln -s "$entry" "$shadow/docs/$(basename "$entry")"
  done
}

# Prints the status of the replay of bundle $1 on its last line.
replay() {
  if [ "$1" = TargetFlipN21 ]; then
    scratch="$work/TargetFlipN21"
    mkdir "$scratch"
    cp "$root/rocq/quantum/TargetFlipN21.v" "$scratch/"
    (
      cd "$scratch"
      "$rocq" compile -q -w +all TargetFlipN21.v >compile.log 2>&1 || exit 1
      if grep -q 'arning:' compile.log; then exit 1; fi
      "$rocq" check -silent -o TargetFlipN21 >check.log 2>&1
    )
    return
  fi
  make_shadow "$1"
  shadow="$work/shadow-$1"
  ledger="$shadow/docs/evidence/$1/source_hashes.sha256"
  if [ -f "$ledger" ] && grep -q -E '  \*?proofs/' "$ledger"; then
    grep -E '  \*?proofs/' "$ledger" >"$work/rows.txt"
    (cd "$shadow" && sha256sum -c --quiet "$work/rows.txt") || return 1
  fi
  log="$work/$1.out"
  (cd "$shadow" && ROCQ="$rocq" GOROROBA_ROOT="${GOROROBA_ROOT:-}" sh "docs/evidence/$1/replay_rocq.sh") >"$log" 2>"$log.err" ||
    {
      tail -n 20 "$log.err" >&2
      return 1
    }
  [ "$1" != folding_proofs ] || cmp -s "$log" "$quantum/docs/evidence/folding_proofs/rocq_replay.log"
}

passed=0
failed=0
skipped=0
for bundle in "$@"; do
  if [ "$bundle" != TargetFlipN21 ] && [ ! -f "$quantum/docs/evidence/$bundle/replay_rocq.sh" ]; then
    echo "replay_quantum_bundles: $bundle has no replay_rocq.sh in $quantum/docs/evidence" >&2
    exit 2
  fi
  if [ "$bundle" != TargetFlipN21 ] && [ -z "${GOROROBA_ROOT:-}" ] &&
    grep -q GOROROBA_ROOT "$quantum/docs/evidence/$bundle/replay_rocq.sh"; then
    if [ "$explicit" -eq 1 ]; then
      echo "replay_quantum_bundles: $bundle reads GOROROBA_ROOT, which is unset" >&2
      exit 2
    fi
    echo "replay_quantum_bundles: skip $bundle: GOROROBA_ROOT is unset"
    skipped=$((skipped + 1))
    continue
  fi
  start=$(date +%s)
  if replay "$bundle"; then
    echo "replay_quantum_bundles: pass $bundle ($(($(date +%s) - start)) s)"
    passed=$((passed + 1))
  else
    echo "replay_quantum_bundles: FAIL $bundle ($(($(date +%s) - start)) s)" >&2
    failed=$((failed + 1))
  fi
done
echo "replay_quantum_bundles: $passed passed, $failed failed, $skipped skipped; gororoba-quantum $(git -C "$quantum" rev-parse HEAD 2>/dev/null || echo unknown)"
[ "$failed" -eq 0 ] && [ "$passed" -gt 0 ]
