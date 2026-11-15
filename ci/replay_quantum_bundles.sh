#!/bin/sh
# Usage: GOROROBA_QUANTUM=PATH [ROCQ=PATH] [GOROROBA_ROOT=PATH] \
#          sh ci/replay_quantum_bundles.sh [--ledgers-only] [BUNDLE...]
# Runs the retained Rocq replays of the gororoba-quantum checkout at
# $GOROROBA_QUANTUM against the sources of this checkout's rocq/quantum.
# A BUNDLE is one path component (letters, digits, '.', '_', '-', no leading
# '-' or '.') that names a directory docs/evidence/BUNDLE of that checkout
# holding a replay_rocq.sh, or TargetFlipN21 (compile with -w +all, no
# warning, rocq check on rocq/quantum/TargetFlipN21.v); any other word ends
# the run with status 2 before anything is created. With no BUNDLE every such
# bundle runs, one after the other.
#
# Ledger comparison. Before a bundle runs, each row of the *.sha256 files of
# its directory that reads `DIGEST  proofs/NAME.v` is compared with
# rocq/quantum/NAME.v. A row under a deeper directory (proofs/theories/,
# proofs/verified/, proofs/evidence/) names a gororoba-open source: when the
# bundle's script names that ledger, the row is compared with the same path
# under $GOROROBA_ROOT if that is set, and otherwise left to the script; a
# ledger the script does not name is a frozen record of an earlier
# gororoba-open state, and its gororoba-open rows are not compared. Rows of other trees (docs/,
# scripts/, results/, crates/, data/) are the bundle script's to check.
# One row is skipped by name and digest: the ledger source_hashes.sha256 of
# cd-sign-python-translation holds a digest of CdSignSourceCertificate.v
# that predates the source (gororoba-quantum documents it as a stale
# manifest, STALE_ROWS below); the closure ledgers of that bundle hold the
# current digest and are compared. --ledgers-only stops after this
# comparison, needs no Rocq, and prints one line per bundle; without
# GOROROBA_ROOT that line reports the gororoba-open rows as not compared,
# and TargetFlipN21, which has no ledger, is refused as a name.
#
# Replay. The bundle's script runs unchanged from a shadow root made of a
# copy of the bundle directory, a copy of rocq/quantum as proofs/, and
# symbolic links to the entries of the gororoba-quantum checkout that the
# bundle's ledgers name (and to docs/ entries other than docs/evidence). A
# link cannot be read-only: a retained script, which writes only to its own
# mktemp directories, could still write the linked entries of the checkout,
# and it reads GOROROBA_ROOT and ROCQ from the environment. GOROROBA_QUANTUM
# is not passed to it. A bundle whose script reads GOROROBA_ROOT is skipped,
# with a line saying so, while GOROROBA_ROOT is unset, and a named bundle
# that needs it ends the run with status 2. ROCQ names the rocq executable
# (default rocq on PATH); a switch is used as
# `opam exec --switch=rocq-9.3 -- sh ci/replay_quantum_bundles.sh`. The
# folding_proofs bundle also compares its stdout with its retained
# rocq_replay.log. Runs on demand, outside the admission gate, because it
# reads another repository and needs Rocq. Peak memory is that of one
# bundle's compile (the Stiefel bundle takes about nine minutes).
# Exit status: 0 at least one bundle passed and none failed, 1 a bundle
# failed or none ran, 2 a tool, the checkout or a name is missing or
# refused. Writes only under a temporary directory it removes, also on INT
# and TERM.
set -eu

ledgers_only=0
if [ "${1:-}" = --ledgers-only ]; then
  ledgers_only=1
  shift
fi
for tool in git cp cmp grep awk sha256sum mktemp sh; do
  command -v "$tool" >/dev/null || {
    echo "replay_quantum_bundles: $tool is not on PATH" >&2
    exit 2
  }
done
rocq=${ROCQ:-rocq}
if [ "$ledgers_only" -eq 0 ]; then
  command -v "$rocq" >/dev/null || {
    echo "replay_quantum_bundles: $rocq is not on PATH; set ROCQ or run under opam exec" >&2
    exit 2
  }
fi
# A replay runs from a temporary directory, so an executable named by a relative path is made absolute.
case $rocq in
*/*) [ "$ledgers_only" -eq 1 ] || rocq=$(CDPATH='' cd -- "$(dirname "$rocq")" && pwd)/$(basename "$rocq") ;;
esac
quantum=${GOROROBA_QUANTUM:?replay_quantum_bundles: set GOROROBA_QUANTUM to a gororoba-quantum checkout}
[ -d "$quantum/docs/evidence" ] || {
  echo "replay_quantum_bundles: $quantum/docs/evidence does not exist" >&2
  exit 2
}
quantum=$(CDPATH='' cd -- "$quantum" && pwd)
# A bundle script runs from its shadow root, so a relative GOROROBA_ROOT is made absolute here.
if [ -n "${GOROROBA_ROOT:-}" ]; then
  [ -d "$GOROROBA_ROOT" ] || {
    echo "replay_quantum_bundles: GOROROBA_ROOT=$GOROROBA_ROOT is no directory" >&2
    exit 2
  }
  GOROROBA_ROOT=$(CDPATH='' cd -- "$GOROROBA_ROOT" && pwd)
fi
root=$(git -C "$(dirname "$0")" rev-parse --show-toplevel)

# bundle/ledger:source:digest, rows skipped while they hold that digest (see the header)
STALE_ROWS='cd-sign-python-translation/source_hashes.sha256:CdSignSourceCertificate.v:37f2109eacff0065a03ec01d80fb27e70c036cfafc3a46fae1cd5f49770d56ef'

if [ "$#" -eq 0 ]; then
  explicit=0
  set -- $(for script in "$quantum"/docs/evidence/*/replay_rocq.sh; do
    basename "$(dirname "$script")"
  done)
  [ "$ledgers_only" -eq 1 ] || set -- "$@" TargetFlipN21
else
  explicit=1
fi

# Accepts only a single plain path component naming a bundle; nothing is created before this passes.
for bundle in "$@"; do
  case $bundle in
  "" | -* | .* | *[!A-Za-z0-9_.-]*)
    echo "replay_quantum_bundles: $bundle is no bundle name" >&2
    exit 2
    ;;
  esac
  if [ "$bundle" = TargetFlipN21 ] && [ "$ledgers_only" -eq 1 ]; then
    echo "replay_quantum_bundles: TargetFlipN21 has no ledger" >&2
    exit 2
  fi
  if [ "$bundle" != TargetFlipN21 ] && { [ -L "$quantum/docs/evidence/$bundle" ] || [ ! -f "$quantum/docs/evidence/$bundle/replay_rocq.sh" ]; }; then
    echo "replay_quantum_bundles: $bundle has no replay_rocq.sh in docs/evidence of the checkout" >&2
    exit 2
  fi
done

work=$(mktemp -d)
trap 'rm -r "$work" </dev/null' EXIT
trap 'exit 130' INT
trap 'exit 143' TERM
mkdir -p "$work/ledger-root/proofs"
cp "$root"/rocq/quantum/*.v "$work/ledger-root/proofs/"

# Compares the ledger rows of bundle $1 as the header says; prints one summary line and returns its status.
check_ledgers() {
  dir="$quantum/docs/evidence/$1"
  : >"$work/rows.txt"
  : >"$work/open-rows.txt"
  : >"$work/skipped.txt"
  for ledger in "$dir"/*.sha256; do
    [ -f "$ledger" ] || continue
    scripted=0
    ! grep -q -F "$(basename "$ledger")" "$dir/replay_rocq.sh" || scripted=1
    awk -v key="$1/$(basename "$ledger")" -v stale="$STALE_ROWS" -v rows="$work/rows.txt" -v open="$work/open-rows.txt" -v scripted="$scripted" '
      BEGIN { n = split(stale, s, " ") }
      {
        digest = $1
        path = $0
        sub(/^[0-9a-f]+ [ *]/, "", path)
        if (path ~ /^proofs\/[A-Za-z0-9_]+\.v$/) {
          name = substr(path, 8)
          skip = 0
          for (i = 1; i <= n; i++) if (s[i] == key ":" name ":" digest) skip = 1
          if (skip) print "skipped" > "/dev/stderr"
          else print digest "  " path >> rows
        } else if (scripted && path ~ /^proofs\//) print digest "  " path >> open
      }' "$ledger" 2>>"$work/skipped.txt"
  done
  skipped=$(grep -c skipped "$work/skipped.txt" 2>/dev/null || true)
  : >"$work/skipped.txt"
  quantum_rows=$(grep -c . "$work/rows.txt" || true)
  open_rows=$(grep -c . "$work/open-rows.txt" || true)
  if [ "$quantum_rows" -gt 0 ] && ! (cd "$work/ledger-root" && sha256sum -c --quiet "$work/rows.txt" >"$work/ledger.out" 2>&1); then
    cat "$work/ledger.out" >&2
    echo "replay_quantum_bundles: ledger FAIL $1: a proofs/ row differs from rocq/quantum" >&2
    return 1
  fi
  where="left to the bundle script"
  [ "$ledgers_only" -eq 0 ] || [ "$open_rows" -eq 0 ] || where="NOT COMPARED: GOROROBA_ROOT is unset and no script runs"
  if [ "$open_rows" -gt 0 ] && [ -n "${GOROROBA_ROOT:-}" ]; then
    if ! (cd "$GOROROBA_ROOT" && sha256sum -c --quiet "$work/open-rows.txt" >"$work/ledger.out" 2>&1); then
      cat "$work/ledger.out" >&2
      echo "replay_quantum_bundles: ledger FAIL $1: a gororoba-open row differs from GOROROBA_ROOT" >&2
      return 1
    fi
    where="checked against GOROROBA_ROOT"
  fi
  echo "replay_quantum_bundles: ledger ok $1: $quantum_rows rocq/quantum rows, $open_rows gororoba-open rows ($where), $skipped stale row skipped"
}

# Builds the shadow root of bundle $1 in $work/shadow-$1.
make_shadow() {
  shadow="$work/shadow-$1"
  mkdir -p "$shadow/proofs" "$shadow/docs/evidence"
  cp "$root"/rocq/quantum/*.v "$shadow/proofs/"
  cp -R "$quantum/docs/evidence/$1" "$shadow/docs/evidence/$1"
  for ledger in "$quantum/docs/evidence/$1"/*.sha256 "$quantum/docs/evidence/$1"/SHA256SUMS; do
    [ -f "$ledger" ] || continue
    awk '{ path = $0; sub(/^[0-9a-f]+ [ *]/, "", path); split(path, part, "/"); if (part[1] != path) print part[1] }' "$ledger"
  done | sort -u >"$work/linked.txt"
  while IFS= read -r entry; do
    case $entry in
    proofs | docs | .git | "" | .* | -*) continue ;;
    esac
    [ -e "$quantum/$entry" ] && [ ! -e "$shadow/$entry" ] && ln -s "$quantum/$entry" "$shadow/$entry"
  done <"$work/linked.txt"
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
  check_ledgers "$1" || return 1
  [ "$ledgers_only" -eq 0 ] || return 0
  make_shadow "$1"
  shadow="$work/shadow-$1"
  log="$work/$1.out"
  (cd "$shadow" && env -u GOROROBA_QUANTUM ROCQ="$rocq" GOROROBA_ROOT="${GOROROBA_ROOT:-}" sh "docs/evidence/$1/replay_rocq.sh") >"$log" 2>"$log.err" ||
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
  if [ "$ledgers_only" -eq 0 ] && [ "$bundle" != TargetFlipN21 ] && [ -z "${GOROROBA_ROOT:-}" ] &&
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
