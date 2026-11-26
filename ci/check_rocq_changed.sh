#!/bin/sh
# Usage: sh ci/check_rocq.sh --changed [--plan] [--base REV] [--probe PATH]
#        sh ci/check_rocq_changed.sh --save DIR WORK   (called by ci/check_rocq.sh)
# The changed-source tier of the Rocq half of the gate. It compiles the Rocq
# sources that differ from the build tree the last green full gate saved, and
# the sources that import them, with the options of each tree's _RocqProject
# (-w all,+default), and compares the warnings of the recompiled sources with
# ci/rocq-warnings/allowed.tsv. It runs no kernel check (rocq check), no
# compile of the sources outside the project files and none of the inventory,
# plugin, extraction or evidence checks: the dispatched and nightly rocq
# workflow keeps those (AGENTS.md, "Landing").
#   --plan   stop after the decision whether any compile is due.
#   --base   the revision HEAD is compared with to decide whether a path under
#            rocq/, ci/install_rocq.sh or a script of this tier (ci/check_rocq.sh,
#            ci/check_rocq_changed.sh, ci/rocq_warning_pairs.py,
#            ci/rocq-warnings/) changed (default HEAD^1, the base of a pull
#            request's merge commit). With no such path the tier reports skip
#            and exits 0; a change to a script alone compiles nothing over a
#            saved tree and runs the calibration. GITHUB_OUTPUT, when set, receives touched=true
#            or touched=false.
#   --probe  a tracked rocq/**/*.v source that the tier treats as changed and
#            extends by a comment in its export, a measurement aid for a run
#            whose commit changes no source.
#   --save   (internal) writes the compiled objects of the export WORK, the
#            manifest of HEAD and the identity of the switch into DIR.
# Baseline. ROCQ_OBJECTS names a directory that --save wrote. The tier
# compares its manifest (the git blob of every path of rocq/ and of
# ci/install_rocq.sh) with HEAD's and compiles everything, as the full gate
# does, when the directory, its manifest or its switch identity is absent or
# differs, a saved path is deleted, or ci/install_rocq.sh, a path under
# rocq/open/opam/, a _RocqProject or a Makefile changed. Otherwise the saved
# objects are laid over the export, every file but the changed sources is dated
# 2000-01-01 so that make sees the objects as current, and make compiles the
# changed sources and the sources that depend on them.
# Calibration. Every run first checks the decision on synthetic manifests
# (identical, one changed source, a deleted source, a changed project file, a
# changed installer, no baseline), requires an untouched revision to report
# skip, and compiles a two-source fixture: a known-good build, then a broken
# proof in the dependent source, which must fail while the first source's
# object stays untouched.
# Environment: ROCQ_OBJECTS, ROCQ_JOBS (default the online processor count),
# ROCQ_BUILD_DIR (parent of the scratch directory, default $TMPDIR or /tmp).
# Needs git, opam with the rocq-9.3 switch (ci/install_rocq.sh), tar, make,
# getconf and python3 (or PYTHON); --plan needs git alone.
# Exit status: 0 passed or skipped, 1 a check failed, 2 a tool or the switch
# is missing or an argument is wrong.
set -eu
PYTHON=${PYTHON:-python3}
export PYTHON
switch=rocq-9.3

usage() {
  echo "usage: check_rocq.sh --changed [--plan] [--base REV] [--probe PATH]" >&2
  exit 2
}

mode=run
base='HEAD^1'
probe=
save_dir=
save_work=
while [ $# -gt 0 ]; do
  case $1 in
    --changed) ;;
    --plan) mode=plan ;;
    --base)
      [ $# -ge 2 ] || usage
      base=$2
      shift
      ;;
    --probe)
      [ $# -ge 2 ] || usage
      probe=$2
      shift
      ;;
    --save)
      [ $# -ge 3 ] || usage
      mode=save
      save_dir=$2
      save_work=$3
      shift 2
      ;;
    *) usage ;;
  esac
  shift
done

tools="git"
[ "$mode" = plan ] || tools="git opam tar make getconf $PYTHON"
for tool in $tools; do
  command -v "$tool" >/dev/null || {
    echo "check_rocq --changed: $tool is not on PATH" >&2
    exit 2
  }
done

root=$(git -C "$(dirname "$0")" rev-parse --show-toplevel)
work=
trap '[ -z "$work" ] || rm -r "$work" </dev/null' EXIT
trap 'exit 130' INT
trap 'exit 143' TERM

# The blob of every path of rocq/ and of the installer, sorted.
manifest_of_head() {
  git -C "$root" ls-tree -r --format='%(objectname)%x09%(path)' HEAD -- rocq ci/install_rocq.sh | LC_ALL=C sort
}

# The identity of the switch the objects were built under: the Rocq version
# and the md5 of the Ltac plugin, which every object records.
switch_identity() {
  lib=$(opam var lib --switch="$switch" 2>/dev/null || true)
  plugin=
  [ -z "$lib" ] || plugin=$(find "$lib" -name ltac_plugin.cmxs 2>/dev/null | LC_ALL=C sort | head -n 1)
  if [ -z "$plugin" ]; then
    echo unknown
    return 0
  fi
  version=$(opam exec --switch="$switch" -- rocq --version 2>/dev/null | tr '\n' ' ')
  printf '%s%s\n' "$version" "$(md5sum <"$plugin" | cut -d ' ' -f 1)"
}

# decide SAVED CURRENT OUT: writes OUT/changed.txt (paths of CURRENT whose
# blob differs from SAVED or that SAVED lacks), OUT/deleted.txt and
# OUT/reason.txt (empty when an incremental build is sound; otherwise the
# reason for a full compile). An absent or empty SAVED is a full compile.
decide() {
  : >"$3/deleted.txt"
  : >"$3/reason.txt"
  if [ ! -s "$1" ]; then
    cut -f 2 "$2" | LC_ALL=C sort >"$3/changed.txt"
    echo "no saved manifest" >"$3/reason.txt"
    return 0
  fi
  LC_ALL=C comm -13 "$1" "$2" | cut -f 2 | LC_ALL=C sort >"$3/changed.txt"
  cut -f 2 "$1" | LC_ALL=C sort >"$3/saved-paths.txt"
  cut -f 2 "$2" | LC_ALL=C sort >"$3/current-paths.txt"
  LC_ALL=C comm -23 "$3/saved-paths.txt" "$3/current-paths.txt" >"$3/deleted.txt"
  if [ -s "$3/deleted.txt" ]; then
    echo "a path of the saved tree is deleted" >"$3/reason.txt"
  elif grep -q -E '^ci/install_rocq\.sh$' "$3/changed.txt"; then
    echo "ci/install_rocq.sh changed" >"$3/reason.txt"
  elif grep -q -E '^rocq/open/opam/' "$3/changed.txt"; then
    echo "the opam ports changed" >"$3/reason.txt"
  elif grep -q -E '(^|/)(_RocqProject|Makefile)$' "$3/changed.txt"; then
    echo "a project file or Makefile changed" >"$3/reason.txt"
  fi
}

touched_paths() {
  git -C "$root" diff --name-only "$1" HEAD -- rocq ci/install_rocq.sh ci/check_rocq.sh ci/check_rocq_changed.sh ci/rocq_warning_pairs.py ci/rocq-warnings
}

set_output() {
  [ -z "${GITHUB_OUTPUT:-}" ] || echo "touched=$1" >>"$GITHUB_OUTPUT"
}

if [ "$mode" = save ]; then
  mkdir -p "$save_dir"
  (cd "$save_work" && find rocq/open/theories rocq/open/verified rocq/quantum rocq/delegation -type f \( -name '*.vo' -o -name '*.glob' -o -name '.*.aux' \) | LC_ALL=C sort >"$save_dir/objects.txt")
  [ -s "$save_dir/objects.txt" ] || {
    echo "check_rocq --changed: $save_work holds no compiled object to save" >&2
    exit 1
  }
  tar -c -C "$save_work" -T "$save_dir/objects.txt" | tar -x -C "$save_dir"
  manifest_of_head >"$save_dir/manifest.tsv"
  switch_identity >"$save_dir/switch-identity.txt"
  echo "check_rocq --changed: saved $(grep -c . "$save_dir/objects.txt") objects, manifest of $(grep -c . "$save_dir/manifest.tsv") paths, switch $(cat "$save_dir/switch-identity.txt")"
  exit 0
fi

git -C "$root" rev-parse --verify -q "$base^{commit}" >/dev/null || {
  echo "check_rocq --changed: the revision $base is absent from the checkout (a shallow clone needs fetch-depth 2 for HEAD^1)" >&2
  exit 2
}
touched=$(touched_paths "$base")
if [ -n "$probe" ]; then
  case $probe in
    rocq/*.v) ;;
    *)
      echo "check_rocq --changed: --probe takes a rocq/**/*.v path, not $probe" >&2
      exit 2
      ;;
  esac
  case /$probe/ in
    */../*)
      echo "check_rocq --changed: --probe path holds a parent reference" >&2
      exit 2
      ;;
  esac
  git -C "$root" ls-files --error-unmatch -- "$probe" >/dev/null 2>&1 || {
    echo "check_rocq --changed: --probe names an untracked path: $probe" >&2
    exit 2
  }
  touched="${touched:+$touched
}$probe"
fi
if [ -z "$touched" ]; then
  echo "check_rocq --changed: skip: no path under rocq/, ci/install_rocq.sh or the scripts of this tier differs between $base and HEAD; the dispatched rocq workflow holds the gate"
  set_output false
  exit 0
fi
set_output true
echo "check_rocq --changed: $(printf '%s\n' "$touched" | grep -c .) path(s) differ from $base:"
printf '%s\n' "$touched" | head -n 20
if [ "$mode" = plan ]; then
  exit 0
fi

opam switch list --short | grep -q -x -F "$switch" || {
  echo "check_rocq --changed: opam switch $switch does not exist; run sh ci/install_rocq.sh" >&2
  exit 2
}
jobs=${ROCQ_JOBS:-$(getconf _NPROCESSORS_ONLN)}
work=$(mktemp -d "${ROCQ_BUILD_DIR:-${TMPDIR:-/tmp}}/gororoba-math-rocq-changed.XXXXXXXX")
started=$(date +%s)

run_logged() {
  log=$1
  shift
  "$@" >"$log" 2>&1 || {
    tail -n 60 "$log" >&2
    grep -n -E '^(Error|File ")|Killed|Out of memory|\*\*\* \[' "$log" | tail -n 20 >&2 || true
    echo "check_rocq --changed: failed: $*" >&2
    exit 1
  }
}

# Builds the project in the current directory with rocq makefile.
build_project() {
  run_logged "$1.makefile" opam exec --switch="$switch" -- rocq makefile --no-rocq-package-warning -f _RocqProject -o Makefile.rocq
  if grep -n '[Ww]arning' "$1.makefile" >&2; then
    echo "check_rocq --changed: rocq makefile printed a warning" >&2
    exit 1
  fi
  run_logged "$1" opam exec --switch="$switch" -- make --keep-going --output-sync=target -f Makefile.rocq --jobs="$jobs"
}

# Calibration: the decision on synthetic manifests.
cal="$work/calibration"
mkdir -p "$cal/case"
tab=$(printf '\t')
{
  printf 'a1%srocq/open/_RocqProject\n' "$tab"
  printf 'a2%srocq/open/Makefile\n' "$tab"
  printf 'a3%srocq/open/theories/A.v\n' "$tab"
  printf 'a4%srocq/quantum/B.v\n' "$tab"
  printf 'a5%sci/install_rocq.sh\n' "$tab"
  printf 'a6%srocq/open/opam/p.export\n' "$tab"
} | LC_ALL=C sort >"$cal/saved.tsv"
# calibrate_case LABEL SED EXPECTED REASON: SED edits the saved manifest into
# the current one; EXPECTED is the space-separated changed paths; REASON is
# yes when the decision must force a full compile.
calibrate_case() {
  sed -e "$2" "$cal/saved.tsv" | LC_ALL=C sort >"$cal/current.tsv"
  decide "$cal/saved.tsv" "$cal/current.tsv" "$cal/case"
  got=$(tr '\n' ' ' <"$cal/case/changed.txt" | sed 's/ $//')
  [ "$got" = "$3" ] || {
    echo "check_rocq --changed: calibration $1: changed paths '$got', expected '$3'" >&2
    exit 1
  }
  if [ "$4" = yes ]; then
    [ -s "$cal/case/reason.txt" ] || {
      echo "check_rocq --changed: calibration $1: the decision allowed an incremental build" >&2
      exit 1
    }
  elif [ -s "$cal/case/reason.txt" ]; then
    echo "check_rocq --changed: calibration $1: the decision forced a full compile: $(cat "$cal/case/reason.txt")" >&2
    exit 1
  fi
}
calibrate_case identical 's/^a/a/' '' no
calibrate_case one-source 's/^a3/z3/' 'rocq/open/theories/A.v' no
calibrate_case deleted-source '/theories\/A\.v/d' '' yes
calibrate_case project-file 's/^a1/z1/' 'rocq/open/_RocqProject' yes
calibrate_case makefile 's/^a2/z2/' 'rocq/open/Makefile' yes
calibrate_case installer 's/^a5/z5/' 'ci/install_rocq.sh' yes
calibrate_case opam-ports 's/^a6/z6/' 'rocq/open/opam/p.export' yes
decide "$cal/absent.tsv" "$cal/saved.tsv" "$cal/case"
[ -s "$cal/case/reason.txt" ] || {
  echo "check_rocq --changed: calibration: an absent baseline did not force a full compile" >&2
  exit 1
}
[ -z "$(touched_paths HEAD)" ] || {
  echo "check_rocq --changed: calibration: HEAD against itself reports a touched path" >&2
  exit 1
}

# Calibration: a known-good and a known-bad compile of a two-source project.
fx="$work/fixture"
mkdir "$fx"
printf '%s\n' '-Q . Fixture' '-arg -w' '-arg all,+default' 'Base.v' 'Dependent.v' >"$fx/_RocqProject"
printf 'Lemma base_true : True.\nProof. exact I. Qed.\n' >"$fx/Base.v"
printf 'From Fixture Require Import Base.\nLemma dependent_true : True.\nProof. exact base_true. Qed.\n' >"$fx/Dependent.v"
(
  cd "$fx"
  build_project "$work/fixture-good.log"
  sleep 1
  touch "$work/fixture-stamp"
  sleep 1
  printf 'Lemma broken : 1 = 2.\nProof. reflexivity. Qed.\n' >>Dependent.v
  if (build_project "$work/fixture-bad.log") >/dev/null 2>&1; then
    echo "check_rocq --changed: calibration: a source with a broken proof compiled" >&2
    exit 1
  fi
  grep -q 'Error' "$work/fixture-bad.log" && grep -q 'Dependent' "$work/fixture-bad.log" || {
    echo "check_rocq --changed: calibration: the broken proof did not fail in the changed source" >&2
    exit 1
  }
  [ ! Base.vo -nt "$work/fixture-stamp" ] || {
    echo "check_rocq --changed: calibration: the unchanged source was compiled again" >&2
    exit 1
  }
)
echo "check_rocq --changed: calibrated: decision cases, skip on an untouched revision, a broken proof fails and leaves the unchanged object"

# The export and the baseline.
git -C "$root" archive HEAD rocq ci/rocq_warning_pairs.py ci/rocq-warnings | tar -x -C "$work"
git -C "$root" -c core.quotePath=false ls-tree -r --name-only HEAD -- rocq | LC_ALL=C sort >"$work/tree-files.txt"
(cd "$work" && find rocq ! -type d | LC_ALL=C sort) >"$work/export-files.txt"
diff "$work/tree-files.txt" "$work/export-files.txt" >"$work/export.diff" || {
  echo "check_rocq --changed: the export of HEAD differs from its tree (< tree, > export); an export-ignore attribute removes a path:" >&2
  cat "$work/export.diff" >&2
  exit 1
}
if [ -n "$probe" ]; then
  printf '\n(* probe *)\n' >>"$work/$probe"
fi
manifest_of_head >"$work/current.tsv"
mkdir "$work/decision"
saved_objects=${ROCQ_OBJECTS:-}
reason=
if [ -z "$saved_objects" ] || [ ! -d "$saved_objects/rocq" ]; then
  reason="no saved build tree"
  : >"$work/saved.tsv"
elif [ "$(switch_identity)" = unknown ] || [ "$(switch_identity)" != "$(cat "$saved_objects/switch-identity.txt" 2>/dev/null || echo none)" ]; then
  reason="the switch differs from the saved one"
  : >"$work/saved.tsv"
else
  cp "$saved_objects/manifest.tsv" "$work/saved.tsv" 2>/dev/null || : >"$work/saved.tsv"
fi
decide "$work/saved.tsv" "$work/current.tsv" "$work/decision"
[ -n "$reason" ] || reason=$(cat "$work/decision/reason.txt")
{
  grep -E '\.v$' "$work/decision/changed.txt" || true
  [ -z "$probe" ] || echo "$probe"
} | LC_ALL=C sort -u >"$work/changed-v.txt"

if [ -n "$reason" ]; then
  echo "check_rocq --changed: full compile: $reason"
  incremental=0
else
  incremental=1
  cp -a "$saved_objects/rocq/." "$work/rocq/"
  find "$work/rocq" -type f ! -name '*.vo' ! -name '*.glob' ! -name '.*.aux' -exec touch -d '2000-01-01 00:00:00' {} +
  while IFS= read -r source; do
    touch "$work/$source"
  done <"$work/changed-v.txt"
  echo "check_rocq --changed: incremental: $(grep -c . "$work/changed-v.txt") changed source(s) over $(grep -c . "$saved_objects/objects.txt") saved objects"
fi
grep -E '^rocq/open/(checkpoints|extraction|tests)/.*\.v$' "$work/changed-v.txt" >"$work/outside-changed.txt" || true
if [ "$incremental" -eq 1 ] && [ -s "$work/outside-changed.txt" ]; then
  echo "check_rocq --changed: not compiled by this tier (the dispatched rocq workflow compiles them):"
  cat "$work/outside-changed.txt"
fi

# Every source of a tree is a line of its project file, as in the full gate.
for tree in open quantum delegation; do
  case $tree in
    open) pattern='^rocq/open/(theories|verified)/.*\.v$' ;;
    *) pattern="^rocq/$tree/.*\\.v\$" ;;
  esac
  grep -E "$pattern" "$work/tree-files.txt" | sed "s|^rocq/$tree/||" >"$work/$tree-sources.txt"
  [ -s "$work/$tree-sources.txt" ] || {
    echo "check_rocq --changed: HEAD holds no source under rocq/$tree" >&2
    exit 1
  }
  if grep -F -x -v -f "$work/rocq/$tree/_RocqProject" "$work/$tree-sources.txt" >"$work/$tree-unlisted.txt"; then
    echo "check_rocq --changed: rocq/$tree/_RocqProject does not list:" >&2
    cat "$work/$tree-unlisted.txt" >&2
    exit 1
  fi
  grep -A 1 -x -F -- '-arg -w' "$work/rocq/$tree/_RocqProject" | grep -q -x -F -- '-arg all,+default' || {
    echo "check_rocq --changed: rocq/$tree/_RocqProject lacks the option lines -arg -w and -arg all,+default" >&2
    exit 1
  }
done

changed_in() {
  grep -q -E "$1" "$work/changed-v.txt"
}
run_open=0
run_quantum=0
run_delegation=0
if [ "$incremental" -eq 0 ]; then
  run_open=1
  run_quantum=1
  run_delegation=1
else
  ! changed_in '^rocq/open/(theories|verified)/' || run_open=1
  ! changed_in '^rocq/quantum/' || run_quantum=1
  ! changed_in '^rocq/delegation/' || run_delegation=1
  # rocq/quantum imports rocq/open.
  [ "$run_open" -eq 0 ] || run_quantum=1
fi

touch "$work/stamp"
sleep 1
ratchet_failed=
ratchet() {
  ratchet_status=0
  "$PYTHON" -I "$work/ci/rocq_warning_pairs.py" --tree "$1" --new-only \
    --allowed "$work/ci/rocq-warnings/allowed.tsv" --causes "$work/ci/rocq-warnings/causes.tsv" \
    --observed "$work/warnings-$1.tsv" "$2" || ratchet_status=$?
  case $ratchet_status in
    0) ;;
    1) ratchet_failed="$ratchet_failed rocq/$1" ;;
    *)
      echo "check_rocq --changed: the warning ratchet could not read the log of rocq/$1" >&2
      exit 1
      ;;
  esac
}
rebuilt() {
  find "$work/rocq/$1" -name '*.vo' -newer "$work/stamp" | grep -c . || true
}
open_n=0
quantum_n=0
delegation_n=0
if [ "$run_open" -eq 1 ]; then
  (cd "$work/rocq/open" && run_logged "$work/open-all.log" opam exec --switch="$switch" -- make --keep-going --output-sync=target --jobs="$jobs" all)
  open_n=$(rebuilt open)
  ratchet open "$work/open-all.log"
  echo "check_rocq --changed: rocq/open compiled $open_n object(s)"
fi
if [ "$run_quantum" -eq 1 ]; then
  (cd "$work/rocq/quantum" && build_project "$work/quantum-all.log")
  quantum_n=$(rebuilt quantum)
  ratchet quantum "$work/quantum-all.log"
  echo "check_rocq --changed: rocq/quantum compiled $quantum_n object(s)"
fi
if [ "$run_delegation" -eq 1 ]; then
  (cd "$work/rocq/delegation" && build_project "$work/delegation-all.log")
  delegation_n=$(rebuilt delegation)
  ratchet delegation "$work/delegation-all.log"
  echo "check_rocq --changed: rocq/delegation compiled $delegation_n object(s)"
fi
[ -z "$ratchet_failed" ] || {
  echo "check_rocq --changed: a warning outside ci/rocq-warnings/allowed.tsv in:$ratchet_failed (printed above)" >&2
  exit 1
}
elapsed=$(($(date +%s) - started))
if [ "$incremental" -eq 1 ]; then
  tier_mode=incremental
else
  tier_mode=full
fi
echo "check_rocq --changed: passed: mode=$tier_mode jobs=$jobs open=$open_n quantum=$quantum_n delegation=$delegation_n seconds=$elapsed; no kernel check ran"
