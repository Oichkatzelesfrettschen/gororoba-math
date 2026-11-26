#!/bin/sh
# Usage: sh ci/check_rocq.sh --changed [--plan] [--base REV] [--probe PATH]
#        sh ci/check_rocq_changed.sh --save DIR   (called by ci/check_rocq.sh)
# The changed-source tier of the Rocq half of the gate. On a pull request it
# compiles the Rocq sources that differ from the build tree the last green full
# gate saved, and the sources that import them, with the options of each tree's
# _RocqProject (-w all,+default), and compares the warnings of the recompiled
# sources with ci/rocq-warnings/allowed.tsv. It also runs the admission scan of
# the three trees, a textual check that a changed project source declares no
# assumption that the tree's kernel-assumptions.txt omits
# (ci/rocq-declared-axioms.awk), the inventory checks that need no compile
# (ci/rocq_inventory.sh), the compile of the sources outside the project files
# that import a recompiled module, and its own calibration.
# It runs no kernel check (rocq check): the full rocq workflow (every push to
# main, nightly, manual dispatch) keeps that, the axiom ledgers, the evidence
# calibration, the plugin-free mutation harnesses of check-schur-geometry and
# the pure-kernel re-check, and AGENTS.md ("Landing") lists them.
#   --plan   stop after the decision whether any check is due.
#   --base   the revision HEAD is compared with to decide whether a path that
#            the tier reads changed (default HEAD^1, the base of a pull
#            request's merge commit). With no such path the tier reports skip
#            and exits 0. GITHUB_OUTPUT, when set, receives touched=true or
#            touched=false.
#   --probe  a tracked rocq/**/*.v source that the tier treats as changed and
#            extends by a comment in its export, a measurement aid for a run
#            whose commit changes no source.
#   --save   (internal) writes the compiled objects of the export that
#            ci/check_rocq.sh built, the manifest of HEAD and the identity of
#            the switch into DIR; the export is named by ROCQ_EXPORT.
# Paths that make a run: rocq/, ci/install_rocq.sh, ci/check_rocq.sh,
# ci/check_rocq_changed.sh, ci/rocq_inventory.sh, ci/rocq-declared-axioms.awk,
# ci/rocq_warning_pairs.py, ci/rocq-warnings/, the evidence producer and its
# calibration (ci/kernel_replay_evidence.py, ci/check_kernel_replay_evidence.sh,
# ci/flocq_manifest.py, ci/flocq-import-corpus.tsv), the generator directories
# ci/quantum-sources/ and ci/delegation-sources/, and any .gitattributes file.
# Baseline. ROCQ_OBJECTS names a directory that --save wrote. The tier compares
# its manifest (the git blob of every path of rocq/ and of ci/install_rocq.sh)
# with HEAD's and compiles everything, as the full gate does, when the
# directory, its manifest or its switch identity is absent, empty or differs, a
# saved path is deleted, ci/install_rocq.sh, a path under rocq/open/opam/, a
# _RocqProject or a Makefile changed, or the warning parser or its lists
# changed (a full compile also runs the warning check without --new-only, so a
# stale allowed row fails). Otherwise the saved objects are laid over the
# export; their time is set to the time of the restore and that of every other
# file to 2000-01-01, whatever the saved times were; the objects of each changed source
# are deleted and the source is touched; make then compiles the changed sources
# and the sources that depend on them, and the script requires each changed
# source's object to be newer than a stamp taken before the build.
# Calibration. Every run, the skip and --plan paths included, checks the
# decision on synthetic manifests, the assumption scan on a synthetic source
# and an untouched revision's skip. A run that compiles also builds a fixture
# project, saves its objects with the save routine, dates them 2099, and
# restores them over a fresh export: a changed Base.v must rebuild Dependent.v
# and leave Other.v, a Base.v change that breaks Dependent.v must fail, and a
# broken proof must fail; the admission scan must reject an Admitted fixture.
# Utilities beyond POSIX that it requires, checked at start: GNU tar (-T),
# md5sum and rustc. Needs git, opam with the rocq-9.3 switch
# (ci/install_rocq.sh), make, getconf and python3 (or PYTHON); --plan needs git.
# Environment: ROCQ_OBJECTS, ROCQ_JOBS (default the online processor count),
# ROCQ_BUILD_DIR (parent of the scratch directory, default $TMPDIR or /tmp).
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
fail() {
  echo "check_rocq --changed: $*" >&2
  exit 1
}

mode=run
base='HEAD^1'
probe=
save_dir=
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
      [ $# -ge 2 ] || usage
      mode=save
      save_dir=$2
      shift
      ;;
    *) usage ;;
  esac
  shift
done

tools="git awk sort comm cut find"
[ "$mode" = plan ] || tools="$tools opam tar make getconf md5sum rustc $PYTHON"
for tool in $tools; do
  command -v "$tool" >/dev/null || {
    echo "check_rocq --changed: $tool is not on PATH" >&2
    exit 2
  }
done
if [ "$mode" != plan ]; then
  tar --version 2>/dev/null | grep -q 'GNU tar' || {
    echo "check_rocq --changed: GNU tar (-T) is required" >&2
    exit 2
  }
fi

root=$(git -C "$(dirname "$0")" rev-parse --show-toplevel)
# A signal ends the script through the EXIT cleanup, which keeps the status
# the script ended with when the removal itself fails.
work=
trap 'status=$?; [ -z "$work" ] || rm -r "$work" </dev/null || :; exit "$status"' EXIT
trap 'exit 130' INT
trap 'exit 143' TERM
work=$(mktemp -d "${ROCQ_BUILD_DIR:-${TMPDIR:-/tmp}}/gororoba-math-rocq-changed.XXXXXXXX")
tab=$(printf '\t')
inventory="$root/ci/rocq_inventory.sh"
[ -r "$inventory" ] || fail "$inventory is unreadable"
# shellcheck source=ci/rocq_inventory.sh
. "$inventory"

# Writes the sorted manifest of HEAD (blob and path of rocq/ and of the
# installer) to the file $1.
manifest_of_head() {
  git -C "$root" -c core.quotePath=false ls-tree -r --format='%(objectname)%x09%(path)' HEAD -- rocq ci/install_rocq.sh >"$1.unsorted" ||
    fail "git ls-tree failed"
  LC_ALL=C sort "$1.unsorted" >"$1" || fail "sort failed"
  rm "$1.unsorted"
}

# Sets identity to the Rocq version and the md5 of the Ltac plugin of the
# switch, which every object records; empty when any part is unreadable.
read_switch_identity() {
  identity=
  lib=$(opam var lib --switch="$switch" 2>/dev/null) || return 0
  [ -n "$lib" ] || return 0
  find "$lib" -name ltac_plugin.cmxs >"$work/plugins.unsorted" 2>/dev/null || return 0
  LC_ALL=C sort "$work/plugins.unsorted" >"$work/plugins.txt" || return 0
  plugin=$(head -n 1 "$work/plugins.txt") || return 0
  [ -n "$plugin" ] || return 0
  version=$(opam exec --switch="$switch" -- rocq --version 2>/dev/null) || return 0
  [ -n "$version" ] || return 0
  digest=$(md5sum <"$plugin") || return 0
  digest=${digest%% *}
  [ -n "$digest" ] || return 0
  identity="$(printf '%s' "$version" | tr '\n' ' ')$digest"
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

# The paths whose change makes a run, relative to the revision $1.
touched_paths() {
  git -C "$root" diff --name-only "$1" HEAD -- rocq ci/install_rocq.sh ci/check_rocq.sh \
    ci/check_rocq_changed.sh ci/rocq_inventory.sh ci/rocq-declared-axioms.awk \
    ci/rocq_warning_pairs.py ci/rocq-warnings ci/kernel_replay_evidence.py \
    ci/check_kernel_replay_evidence.sh ci/flocq_manifest.py ci/flocq-import-corpus.tsv \
    ci/quantum-sources ci/delegation-sources .gitattributes ':(glob)**/.gitattributes'
}

set_output() {
  [ -z "${GITHUB_OUTPUT:-}" ] || echo "touched=$1" >>"$GITHUB_OUTPUT"
}

# newer FILE STAMP: succeeds when FILE exists and is newer than STAMP.
newer() {
  [ -f "$1" ] || return 1
  newer_list=$(find "$1" -newer "$2") || return 1
  [ -n "$newer_list" ]
}

# save_objects SRC DEST DIR...: copies the object files below the directories
# DIR of SRC into DEST, keeping their times, and fails unless DEST then holds
# exactly the files listed.
save_objects() {
  src=$1
  dest=$2
  shift 2
  mkdir -p "$dest" || fail "cannot create $dest"
  (cd "$src" && find "$@" -type f \( -name '*.vo' -o -name '*.glob' -o -name '.*.aux' \)) >"$work/objects.unsorted" ||
    fail "find failed in $src"
  LC_ALL=C sort "$work/objects.unsorted" >"$dest/objects.txt" || fail "sort failed"
  [ -s "$dest/objects.txt" ] || fail "$src holds no compiled object to save"
  tar -c -f "$work/objects.tar" -C "$src" -T "$dest/objects.txt" || fail "tar could not write the objects"
  tar -x -f "$work/objects.tar" -C "$dest" || fail "tar could not read the objects"
  rm "$work/objects.tar"
  (cd "$dest" && find "$@" -type f) >"$work/objects.copied" || fail "find failed in $dest"
  LC_ALL=C sort "$work/objects.copied" >"$work/objects.copied.sorted" || fail "sort failed"
  cmp -s "$dest/objects.txt" "$work/objects.copied.sorted" || fail "the saved objects differ from the list of $src"
}

# overlay_objects SAVED EXPORT: lays the saved objects over the export, sets the
# time of every object to one instant now (newer than the library objects of
# the switch, which each object depends on, whatever clock saved it) and of every other
# file to 2000-01-01, waits a second so that a source touched afterwards is
# newer, and removes each object whose source the export lacks.
overlay_objects() {
  cp -pR "$1/rocq/." "$2/rocq/" || fail "cannot copy the saved objects"
  find "$2/rocq" -type f ! -name '*.vo' ! -name '*.glob' ! -name '.*.aux' -exec touch -t 200001010000 {} + ||
    fail "cannot date the sources"
  # One reference time for every object: make rebuilds a target whose
  # prerequisite is newer, and separate touch calls would order the objects.
  touch "$2/object-time" || fail "cannot create the reference time"
  find "$2/rocq" -type f \( -name '*.vo' -o -name '*.glob' -o -name '.*.aux' \) -exec touch -r "$2/object-time" {} + ||
    fail "cannot date the objects"
  rm "$2/object-time"
  sleep 1
  find "$2/rocq" -type f -name '*.vo' >"$work/overlay-objects.txt" || fail "find failed"
  while IFS= read -r object; do
    [ -f "${object%o}" ] || rm -f "$object" "${object}s" "${object%o}ok" "${object%.vo}.glob"
  done <"$work/overlay-objects.txt"
}

# drop_objects LIST ROOT: removes the objects of each source of LIST (paths
# relative to ROOT) and touches the source.
drop_objects() {
  while IFS= read -r source; do
    [ -n "$source" ] || continue
    stem=${source%.v}
    directory=$(dirname "$source")
    leaf=$(basename "$stem")
    rm -f "$2/$stem.vo" "$2/$stem.vos" "$2/$stem.vok" "$2/$stem.glob" "$2/$directory/.$leaf.aux"
    touch "$2/$source" || fail "cannot touch $source"
  done <"$1"
}

if [ "$mode" = save ]; then
  [ -n "${ROCQ_EXPORT:-}" ] || fail "--save needs ROCQ_EXPORT, the export that ci/check_rocq.sh built"
  save_objects "$ROCQ_EXPORT" "$save_dir" rocq/open/theories rocq/open/verified rocq/quantum rocq/delegation
  manifest_of_head "$save_dir/manifest.tsv"
  read_switch_identity
  [ -n "$identity" ] || fail "the identity of the switch is unreadable"
  printf '%s\n' "$identity" >"$save_dir/switch-identity.txt"
  echo "check_rocq --changed: saved $(awk 'END { print NR }' "$save_dir/objects.txt") objects, manifest of $(awk 'END { print NR }' "$save_dir/manifest.tsv") paths, switch $identity"
  exit 0
fi

# Calibration: the decision on synthetic manifests and the assumption scan.
cal="$work/calibration"
mkdir -p "$cal/case"
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
  [ "$got" = "$3" ] || fail "calibration $1: changed paths '$got', expected '$3'"
  if [ "$4" = yes ]; then
    [ -s "$cal/case/reason.txt" ] || fail "calibration $1: the decision allowed an incremental build"
  elif [ -s "$cal/case/reason.txt" ]; then
    fail "calibration $1: the decision forced a full compile: $(cat "$cal/case/reason.txt")"
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
[ -s "$cal/case/reason.txt" ] || fail "calibration: an absent baseline did not force a full compile"
git -C "$root" diff --name-only HEAD HEAD >"$cal/untouched.txt" || fail "git diff failed"
[ ! -s "$cal/untouched.txt" ] || fail "calibration: HEAD against itself reports a changed path"
untouched=$(touched_paths HEAD)
[ -z "$untouched" ] || fail "calibration: HEAD against itself reports a touched path"

# The assumption scan on a synthetic source: top-level assumptions are named,
# those inside a Module Type, a comment or (for Hypothesis) a Section are not.
cat >"$cal/Assume.v" <<'ASSUME'
(* Axiom in_comment : False. *)
Axiom top_axiom : False.
Parameters (p q : nat).
Hypothesis top_hypothesis : False.
Section S.
Hypothesis section_hypothesis : False.
End S.
Module Type T.
Axiom in_module_type : False.
End T.
Module M.
Conjecture nested_conjecture : False.
End M.
ASSUME
printf '%s\n' top_axiom p q top_hypothesis M.nested_conjecture >"$cal/assume-expected.txt"
awk -f "$root/ci/rocq-declared-axioms.awk" "$cal/Assume.v" >"$cal/assume-found.txt" || fail "the assumption scan failed"
cmp -s "$cal/assume-expected.txt" "$cal/assume-found.txt" || fail "calibration: the assumption scan names $(tr '\n' ' ' <"$cal/assume-found.txt")"

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
  echo "check_rocq --changed: skip: no path that the tier reads (rocq/, ci/install_rocq.sh, the Rocq gate scripts and lists, the evidence producer, the generators, .gitattributes) differs between $base and HEAD; the full rocq workflow (push to main, nightly, dispatch) holds the gate"
  set_output false
  exit 0
fi
set_output true
printf '%s\n' "$touched" >"$work/touched.txt"
echo "check_rocq --changed: $(awk 'END { print NR }' "$work/touched.txt") path(s) differ from $base:"
head -n 20 "$work/touched.txt"
if [ "$mode" = plan ]; then
  exit 0
fi

opam switch list --short | grep -q -x -F "$switch" || {
  echo "check_rocq --changed: opam switch $switch does not exist; run sh ci/install_rocq.sh" >&2
  exit 2
}
jobs=${ROCQ_JOBS:-$(getconf _NPROCESSORS_ONLN)}
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

# Calibration of the mechanism on a fixture project: Base.v, Dependent.v
# (imports Base) and Other.v. A full build, its objects saved by save_objects
# and dated 2099, then three restores over a fresh export.
fx="$work/fixture"
mkdir -p "$fx/src/rocq/fixture"
(
  cd "$fx/src/rocq/fixture"
  printf '%s\n' '-Q . Fixture' '-arg -w' '-arg all,+default' 'Base.v' 'Dependent.v' 'Other.v' >_RocqProject
  printf 'Lemma base_true : True.\nProof. exact I. Qed.\n' >Base.v
  printf 'From Fixture Require Import Base.\nLemma dependent_true : True.\nProof. exact base_true. Qed.\n' >Dependent.v
  printf 'Lemma other_true : True.\nProof. exact I. Qed.\n' >Other.v
  build_project "$work/fixture-full.log"
)
save_objects "$fx/src" "$fx/saved" rocq/fixture
find "$fx/saved/rocq" -type f -exec touch -t 209901010000 {} + || fail "cannot date the fixture objects"
# fixture_case NAME: a fresh export of the fixture sources over the saved
# objects, with Base.v edited by the commands on standard input. Sets
# fixture_dir; the changed source is touched and its objects removed.
fixture_case() {
  fixture_dir="$fx/$1/rocq/fixture"
  mkdir -p "$fixture_dir"
  cp "$fx/src/rocq/fixture/_RocqProject" "$fx/src/rocq/fixture/Base.v" "$fx/src/rocq/fixture/Dependent.v" "$fx/src/rocq/fixture/Other.v" "$fixture_dir/" ||
    fail "cannot copy the fixture sources"
  overlay_objects "$fx/saved" "$fx/$1"
  printf '%s\n' rocq/fixture/Base.v >"$fx/$1/changed.txt"
}
fixture_stamp() {
  drop_objects "$fx/$1/changed.txt" "$fx/$1"
  touch "$fx/$1/stamp" || fail "cannot stamp"
  sleep 1
}
fixture_case benign
printf 'Lemma base_extra : True.\nProof. exact I. Qed.\n' >>"$fixture_dir/Base.v"
fixture_stamp benign
(cd "$fixture_dir" && build_project "$work/fixture-benign.log")
newer "$fixture_dir/Base.vo" "$fx/benign/stamp" || fail "calibration: the changed Base.v kept an older object"
newer "$fixture_dir/Dependent.vo" "$fx/benign/stamp" || fail "calibration: Dependent.v kept a stale object after Base.v changed"
! newer "$fixture_dir/Other.vo" "$fx/benign/stamp" || fail "calibration: the unrelated Other.v was compiled again"
fixture_case breaking
printf 'Lemma base_true_renamed : True.\nProof. exact I. Qed.\n' >"$fixture_dir/Base.v"
fixture_stamp breaking
if (cd "$fixture_dir" && build_project "$work/fixture-breaking.log") >/dev/null 2>&1; then
  fail "calibration: a Base.v change that breaks Dependent.v passed over a stale Dependent object"
fi
grep -q 'Dependent' "$work/fixture-breaking.log" || fail "calibration: the break did not fail in Dependent.v"
fixture_case proof
printf 'Lemma broken : 1 = 2.\nProof. reflexivity. Qed.\n' >>"$fixture_dir/Base.v"
fixture_stamp proof
if (cd "$fixture_dir" && build_project "$work/fixture-proof.log") >/dev/null 2>&1; then
  fail "calibration: a source with a broken proof compiled"
fi
grep -q 'Error' "$work/fixture-proof.log" || fail "calibration: the broken proof gave no error"
echo "check_rocq --changed: calibrated: decision cases, skip on an untouched revision, the assumption scan, a restored overlay (dependent rebuilt, unrelated object kept, a break fails, saved objects dated 2099), a broken proof fails"

# The export and the baseline.
git -C "$root" archive HEAD rocq ci/rocq_warning_pairs.py ci/rocq-warnings | tar -x -C "$work" || fail "cannot export HEAD"
git -C "$root" -c core.quotePath=false ls-tree -r --name-only HEAD -- rocq >"$work/tree-files.unsorted" || fail "git ls-tree failed"
LC_ALL=C sort "$work/tree-files.unsorted" >"$work/tree-files.txt" || fail "sort failed"
(cd "$work" && find rocq ! -type d) >"$work/export-files.unsorted" || fail "find failed"
LC_ALL=C sort "$work/export-files.unsorted" >"$work/export-files.txt" || fail "sort failed"
diff "$work/tree-files.txt" "$work/export-files.txt" >"$work/export.diff" || {
  echo "check_rocq --changed: the export of HEAD differs from its tree (< tree, > export); an export-ignore attribute removes a path:" >&2
  cat "$work/export.diff" >&2
  exit 1
}
if [ -n "$probe" ]; then
  printf '\n(* probe *)\n' >>"$work/$probe"
fi
grep '\.v$' "$work/tree-files.txt" >"$work/tracked-sources.txt" || fail "HEAD tracks no Rocq source"
outside_sources_match "$work/tracked-sources.txt" >"$work/outside.diff" || {
  echo "check_rocq --changed: sources outside the project-listed directories differ from the lists of ci/rocq_inventory.sh (< named, > tracked):" >&2
  cat "$work/outside.diff" >&2
  exit 1
}
for tree in open quantum delegation; do
  case $tree in
    open) pattern='^rocq/open/(theories|verified)/.*\.v$' ;;
    *) pattern="^rocq/$tree/.*\\.v\$" ;;
  esac
  grep -E "$pattern" "$work/tree-files.txt" | sed "s|^rocq/$tree/||" >"$work/$tree-sources.txt" || fail "HEAD holds no source under rocq/$tree"
  if unlisted_sources "$work/rocq/$tree/_RocqProject" "$work/$tree-sources.txt" >"$work/$tree-unlisted.txt"; then
    :
  else
    echo "check_rocq --changed: rocq/$tree/_RocqProject does not list:" >&2
    cat "$work/$tree-unlisted.txt" >&2
    exit 1
  fi
  warning_options_set "$work/rocq/$tree/_RocqProject" || fail "rocq/$tree/_RocqProject lacks the option lines -arg -w and -arg all,+default"
done
check_delegation_stated "$work/rocq/delegation" || fail "the delegation inventory check failed"

# The admission scan of the three trees, calibrated on a fixture that holds Admitted.
(cd "$work/rocq/open" && run_logged "$work/admission-build.log" opam exec --switch="$switch" -- make check-admissions)
scanner="$work/rocq/.cache/proof-admission-check/admission-check"
mkdir "$work/admitted"
printf 'Lemma not_proved : False.\nProof.\nAdmitted.\n' >"$work/admitted/Admitted.v"
if "$scanner" "$work/admitted/" >"$work/admitted.log" 2>&1; then
  fail "calibration: the admission scan accepted an Admitted proof"
fi
run_logged "$work/quantum-admissions.log" "$scanner" "$work/rocq/quantum/"
run_logged "$work/delegation-admissions.log" "$scanner" "$work/rocq/delegation/"
echo "check_rocq --changed: admission scan passed on rocq/open, rocq/quantum and rocq/delegation"

# The baseline decision.
manifest_of_head "$work/current.tsv"
mkdir "$work/decision"
saved_objects=${ROCQ_OBJECTS:-}
reason=
: >"$work/saved.tsv"
if [ -z "$saved_objects" ] || [ ! -d "$saved_objects/rocq" ]; then
  reason="no saved build tree"
else
  saved_identity=
  [ ! -s "$saved_objects/switch-identity.txt" ] || saved_identity=$(cat "$saved_objects/switch-identity.txt") || saved_identity=
  read_switch_identity
  if [ -z "$identity" ] || [ -z "$saved_identity" ] || [ "$identity" = unknown ] || [ "$saved_identity" = unknown ]; then
    reason="the identity of the switch or of the saved one is empty or unreadable"
  elif [ "$identity" != "$saved_identity" ]; then
    reason="the switch differs from the saved one"
  elif [ ! -s "$saved_objects/manifest.tsv" ] || [ ! -s "$saved_objects/objects.txt" ]; then
    reason="the saved manifest or object list is empty"
  else
    cp "$saved_objects/manifest.tsv" "$work/saved.tsv" || fail "cannot read the saved manifest"
  fi
fi
decide "$work/saved.tsv" "$work/current.tsv" "$work/decision"
[ -n "$reason" ] || reason=$(cat "$work/decision/reason.txt")
ratchet_inputs=
if grep -q -E '^ci/(rocq_warning_pairs\.py|rocq-warnings/)' "$work/touched.txt"; then
  ratchet_inputs=1
  [ -n "$reason" ] || reason="the warning parser or its lists changed"
fi
rocq_touched=
if grep -q -E '^(rocq/|ci/install_rocq\.sh$)' "$work/touched.txt"; then
  rocq_touched=1
fi
{
  grep -E '\.v$' "$work/decision/changed.txt" || true
  [ -z "$probe" ] || echo "$probe"
} | LC_ALL=C sort -u >"$work/changed-v.txt"
cut -f 2 "$work/current.tsv" >"$work/current-paths.txt"
grep -E '^rocq/(open/(theories|verified)|quantum|delegation)/.*\.v$' "$work/changed-v.txt" >"$work/changed-project.txt" || true

# The tier compiles trees only when a path of rocq/, the installer or the
# warning parser changed; the other paths run the checks above and below.
compile_trees=0
if [ -n "$rocq_touched" ] || [ -n "$ratchet_inputs" ]; then
  compile_trees=1
fi
if [ "$compile_trees" -eq 0 ]; then
  echo "check_rocq --changed: no Rocq source or ratchet input changed; no tree is compiled"
  incremental=1
  : >"$work/changed-v.txt"
  : >"$work/changed-project.txt"
elif [ -n "$reason" ]; then
  echo "check_rocq --changed: full compile: $reason"
  incremental=0
  cp "$work/tracked-sources.txt" "$work/changed-v.txt"
  cp "$work/tracked-sources.txt" "$work/changed-project.txt"
else
  incremental=1
fi

# The assumption scan of the changed project sources.
check_declared_axioms() {
  scan_status=0
  while IFS= read -r source; do
    [ -n "$source" ] || continue
    case $source in
      rocq/open/theories/*)
        ledger=rocq/open/kernel-assumptions.txt
        module=OpenGororoba.${source#rocq/open/theories/}
        ;;
      rocq/open/verified/*)
        ledger=rocq/open/kernel-assumptions.txt
        module=OpenGororobaVerified.${source#rocq/open/verified/}
        ;;
      rocq/quantum/*)
        ledger=rocq/quantum/kernel-assumptions.txt
        module=${source#rocq/quantum/}
        ;;
      *)
        ledger=rocq/delegation/kernel-assumptions.txt
        module=GororobaDelegation.${source#rocq/delegation/}
        ;;
    esac
    module=${module%.v}
    module=$(printf '%s' "$module" | tr / .)
    awk -f "$root/ci/rocq-declared-axioms.awk" "$work/$source" >"$work/declared.txt" || fail "the assumption scan failed on $source"
    while IFS= read -r name; do
      [ -n "$name" ] || continue
      if ! grep -F -x -q -- "$module.$name" "$work/$ledger"; then
        echo "check_rocq --changed: $source declares the assumption $module.$name that $ledger does not list" >&2
        scan_status=1
      fi
    done <"$work/declared.txt"
  done <"$1"
  [ "$scan_status" -eq 0 ]
}
check_declared_axioms "$work/changed-project.txt" || fail "an assumption is declared outside the kernel assumption ledgers (a textual check; rocq check stays the authority)"

if [ "$incremental" -eq 1 ] && [ "$compile_trees" -eq 1 ]; then
  cp -p "$saved_objects/objects.txt" "$work/saved-objects.txt" || fail "cannot read the saved object list"
  overlay_objects "$saved_objects" "$work"
  drop_objects "$work/changed-v.txt" "$work"
  echo "check_rocq --changed: incremental: $(awk 'END { print NR }' "$work/changed-v.txt") changed source(s) over $(awk 'END { print NR }' "$work/saved-objects.txt") saved objects"
fi

changed_in() {
  grep -q -E "$1" "$work/changed-v.txt"
}
run_open=0
run_quantum=0
run_delegation=0
if [ "$compile_trees" -eq 1 ]; then
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
fi

touch "$work/stamp" || fail "cannot stamp"
sleep 1
ratchet_failed=
ratchet() {
  ratchet_status=0
  if [ "$incremental" -eq 1 ]; then
    "$PYTHON" -I "$work/ci/rocq_warning_pairs.py" --tree "$1" --new-only \
      --allowed "$work/ci/rocq-warnings/allowed.tsv" --causes "$work/ci/rocq-warnings/causes.tsv" \
      --observed "$work/warnings-$1.tsv" "$2" || ratchet_status=$?
  else
    "$PYTHON" -I "$work/ci/rocq_warning_pairs.py" --tree "$1" \
      --allowed "$work/ci/rocq-warnings/allowed.tsv" --causes "$work/ci/rocq-warnings/causes.tsv" \
      --observed "$work/warnings-$1.tsv" "$2" || ratchet_status=$?
  fi
  case $ratchet_status in
    0) ;;
    1) ratchet_failed="$ratchet_failed rocq/$1" ;;
    *) fail "the warning ratchet could not read the log of rocq/$1" ;;
  esac
}
# count_rebuilt TREE: the objects of the tree newer than the stamp.
count_rebuilt() {
  find "$work/rocq/$1" -name '*.vo' -newer "$work/stamp" >"$work/rebuilt-$1.txt" || fail "find failed in rocq/$1"
  awk 'END { print NR }' "$work/rebuilt-$1.txt"
}
open_n=0
quantum_n=0
delegation_n=0
: >"$work/open-logs.txt"
if [ "$run_open" -eq 1 ]; then
  (cd "$work/rocq/open" && run_logged "$work/open-all.log" opam exec --switch="$switch" -- make --keep-going --output-sync=target --jobs="$jobs" all)
  open_n=$(count_rebuilt open)
  echo "$work/open-all.log" >>"$work/open-logs.txt"
  echo "check_rocq --changed: rocq/open compiled $open_n object(s)"
fi

# The sources outside the project files, as the targets of rocq/open compile
# them (check-schur-geometry without its mutation harnesses and kernel check,
# check-plugins, extract-check). A group runs when a source of it or a path of
# its directory changed, or when it names a module that this run rebuilt (a
# textual match, so a group may run without need); a full compile runs all.
if [ -f "$work/rebuilt-open.txt" ]; then
  sed -n 's|^.*/\([^/]*\)\.vo$|\1|p' "$work/rebuilt-open.txt" >"$work/rebuilt-modules.txt" || fail "sed failed"
else
  : >"$work/rebuilt-modules.txt"
fi
mention_pattern=
if [ -s "$work/rebuilt-modules.txt" ]; then
  mention_pattern=$(awk 'NR > 1 { printf "|" } { printf "%s", $0 }' "$work/rebuilt-modules.txt")
fi
group_due() {
  # group_due DIRECTORY-PATTERN SOURCE...
  [ "$incremental" -eq 0 ] && return 0
  pattern=$1
  shift
  grep -q -E "$pattern" "$work/touched.txt" && return 0
  [ -n "$mention_pattern" ] || return 1
  for outside in "$@"; do
    grep -q -w -E "$mention_pattern" "$work/$outside" && return 0
  done
  return 1
}
compile_outside() {
  # compile_outside LOG ARGUMENTS...: rocq compile in rocq/open
  outside_log=$1
  shift
  (cd "$work/rocq/open" && run_logged "$work/$outside_log" opam exec --switch="$switch" -- rocq compile -q -w all,+default "$@")
  echo "$work/$outside_log" >>"$work/open-logs.txt"
}
schur_flags='-Q theories OpenGororoba -Q checkpoints/schur-geometry OpenGororobaCheckpoint'
outside_run=
if [ "$compile_trees" -eq 1 ]; then
  if group_due '^rocq/open/(checkpoints|tests)/' rocq/open/checkpoints/schur-geometry/CDTowerOperatorCorrespondence.v rocq/open/checkpoints/schur-geometry/CDUnconditionalDoublingNullity.v rocq/open/checkpoints/schur-geometry/NullityTwelveCoefficientCertificate.v rocq/open/checkpoints/schur-geometry/SchurAccelerationObstruction.v rocq/open/tests/SchurAccelerationBoundaries.v; then
    # shellcheck disable=SC2086 # the flag list is words by design
    compile_outside open-outside-nullity.log $schur_flags checkpoints/schur-geometry/NullityTwelveCoefficientCertificate.v
    for checkpoint in CDTowerOperatorCorrespondence SchurAccelerationObstruction CDUnconditionalDoublingNullity; do
      # shellcheck disable=SC2086
      compile_outside "open-outside-$checkpoint.log" $schur_flags "checkpoints/schur-geometry/$checkpoint.v"
    done
    # shellcheck disable=SC2086
    compile_outside open-outside-boundaries.log $schur_flags -Q tests OpenGororobaTests tests/SchurAccelerationBoundaries.v
    outside_run="$outside_run schur-geometry"
  fi
  if group_due '^rocq/open/tests/' rocq/open/tests/MathCompMatrixCompatibility.v rocq/open/tests/PluginCompatibility.v; then
    compile_outside open-outside-mathcomp.log tests/MathCompMatrixCompatibility.v
    compile_outside open-outside-plugin.log tests/PluginCompatibility.v
    outside_run="$outside_run plugins"
  fi
  if group_due '^rocq/open/extraction/' rocq/open/extraction/ExtractQuaternion.v; then
    (cd "$work/rocq/open" && run_logged "$work/open-outside-extract.log" opam exec --switch="$switch" -- make --keep-going --output-sync=target --jobs="$jobs" extract-check)
    echo "$work/open-outside-extract.log" >>"$work/open-logs.txt"
    outside_run="$outside_run extract-check"
  fi
  echo "check_rocq --changed: sources outside the project files compiled:${outside_run:- none}"
fi
if [ -s "$work/open-logs.txt" ]; then
  # shellcheck disable=SC2046 # one log per word
  ratchet open $(cat "$work/open-logs.txt")
fi
if [ "$run_quantum" -eq 1 ]; then
  (cd "$work/rocq/quantum" && build_project "$work/quantum-all.log")
  quantum_n=$(count_rebuilt quantum)
  ratchet quantum "$work/quantum-all.log"
  echo "check_rocq --changed: rocq/quantum compiled $quantum_n object(s)"
fi
if [ "$run_delegation" -eq 1 ]; then
  (cd "$work/rocq/delegation" && build_project "$work/delegation-all.log")
  delegation_n=$(count_rebuilt delegation)
  ratchet delegation "$work/delegation-all.log"
  echo "check_rocq --changed: rocq/delegation compiled $delegation_n object(s)"
fi
[ -z "$ratchet_failed" ] || fail "a warning differs from ci/rocq-warnings/allowed.tsv in:$ratchet_failed (printed above)"

# Each changed project source has an object newer than the stamp.
if [ "$incremental" -eq 1 ] && [ "$compile_trees" -eq 1 ]; then
  while IFS= read -r source; do
    [ -n "$source" ] || continue
    object=$work/${source%.v}.vo
    newer "$object" "$work/stamp" || fail "the object of the changed source $source is missing or older than the build"
  done <"$work/changed-project.txt"
fi

elapsed=$(($(date +%s) - started))
if [ "$incremental" -eq 1 ]; then
  tier_mode=incremental
else
  tier_mode=full
fi
echo "check_rocq --changed: not checked here: rocq check and the axiom ledgers, the evidence calibration, the mutation harnesses and kernel check of check-schur-geometry, the generators (ci/check_quantum_sources.sh, ci/check_delegation_sources.sh run on demand), the sources held uncompiled"
echo "check_rocq --changed: passed: mode=$tier_mode jobs=$jobs open=$open_n quantum=$quantum_n delegation=$delegation_n seconds=$elapsed"
