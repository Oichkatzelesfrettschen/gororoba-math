#!/bin/sh
# Usage: sh ci/check_flocq_manifest.sh
# Calibrates ci/flocq_manifest.py, which records the Flocq objects of the
# rocq-9.3 switch in ci/flocq-manifest.json. Every case runs the producer and
# requires its exit status and a named output text.
# On a scratch copy of the switch's Flocq directory, through FLOCQ_ROOT:
#   known-good: --check on the real switch exits 0 and reports equal;
#   one byte of one .vo changed, one .vo removed, one extra .vo: --check exits
#     1 and names the differing external/Flocq/ path;
#   one .vo replaced by a symbolic link: exits 2 with a refusal;
#   FLOCQ_ROOT empty, and FLOCQ_ROOT a symbolic link: exit 2 with a refusal.
# On a scratch copy of the producer with its own repository and manifest:
#   --write creates the manifest and --check then exits 0;
#   a manifest that is a symbolic link: --write exits 2 and its target keeps
#     its bytes;
#   a manifest of the wrong shape: --check exits 1 and names the shape.
# The scratch directories live under FLOCQ_BUILD_DIR (default TMPDIR or /tmp)
# and are removed on exit, also on INT (status 130) and TERM (status 143).
# Needs git, opam, cmp, dd, find and PYTHON (default python3) on PATH. Exit
# status: 0 every case behaved, 1 a case misbehaved, 2 a tool or the switch is
# missing.
set -eu

PYTHON=${PYTHON:-python3}
export PYTHON
for tool in git opam cmp dd find "$PYTHON"; do
  command -v "$tool" >/dev/null || {
    echo "check_flocq_manifest: $tool is not on PATH" >&2
    exit 2
  }
done
switch=rocq-9.3
opam switch list --short | grep -q -x -F "$switch" || {
  echo "check_flocq_manifest: opam switch $switch does not exist" >&2
  exit 2
}

root=$(git -C "$(dirname "$0")" rev-parse --show-toplevel)
manifest_py="$root/ci/flocq_manifest.py"
work=$(mktemp -d "${FLOCQ_BUILD_DIR:-${TMPDIR:-/tmp}}/flocq-manifest.XXXXXXXX")
trap 'rm -r "$work" </dev/null' EXIT
trap 'exit 130' INT
trap 'exit 143' TERM

flocq=$(opam exec --switch="$switch" -- sh -c 'printf "%s" "$OPAM_SWITCH_PREFIX/lib/coq/user-contrib/Flocq"') || {
  echo "check_flocq_manifest: cannot resolve the Flocq directory of $switch" >&2
  exit 2
}
cp -R "$flocq" "$work/pristine"

# run_case LABEL ROOT SCRIPT ARGUMENT...: runs the producer under the switch
# with FLOCQ_ROOT set to ROOT ("unset": the variable removed, "": set empty)
# and prints its exit status; the output goes to LABEL.out.
run_case() {
  label=$1
  root_value=$2
  script=$3
  shift 3
  status=0
  case $root_value in
    unset)
      env -u FLOCQ_ROOT opam exec --switch="$switch" -- "$PYTHON" -I "$script" "$@" >"$work/$label.out" 2>&1 || status=$?
      ;;
    *)
      env FLOCQ_ROOT="$root_value" opam exec --switch="$switch" -- "$PYTHON" -I "$script" "$@" >"$work/$label.out" 2>&1 || status=$?
      ;;
  esac
  echo "$status"
}

# expect LABEL WANT GOT: fails the run when a case exits other than WANT.
expect() {
  [ "$3" = "$2" ] || {
    echo "check_flocq_manifest: $1 exited $3, expected $2" >&2
    cat "$work/$1.out" >&2
    exit 1
  }
}

# expect_text LABEL TEXT: fails the run when the output of a case lacks TEXT.
expect_text() {
  grep -q -F -- "$2" "$work/$1.out" || {
    echo "check_flocq_manifest: $1 output lacks: $2" >&2
    cat "$work/$1.out" >&2
    exit 1
  }
}

cases=0
status=$(run_case known-good unset "$manifest_py" --check)
expect known-good 0 "$status"
expect_text known-good "flocq_manifest: equal, 35 objects"
cases=$((cases + 1))

victim=$(cd "$work/pristine" && find . -name '*.vo' | LC_ALL=C sort | head -n 1)
victim=${victim#./}
[ -n "$victim" ] || {
  echo "check_flocq_manifest: the switch's Flocq directory holds no .vo" >&2
  exit 1
}

# Case: one byte of one .vo changed.
cp -R "$work/pristine" "$work/case"
printf 'X' | dd of="$work/case/$victim" bs=1 count=1 conv=notrunc 2>/dev/null
cmp -s "$work/pristine/$victim" "$work/case/$victim" && {
  echo "check_flocq_manifest: the byte mutation left $victim unchanged" >&2
  exit 1
}
status=$(run_case byte "$work/case" "$manifest_py" --check)
expect byte 1 "$status"
expect_text byte "first differing path: external/Flocq/$victim"
cases=$((cases + 1))

# Case: one .vo removed.
rm -r "$work/case" </dev/null
cp -R "$work/pristine" "$work/case"
rm "$work/case/$victim"
status=$(run_case removed "$work/case" "$manifest_py" --check)
expect removed 1 "$status"
expect_text removed "first differing path: external/Flocq/"
cases=$((cases + 1))

# Case: one extra .vo.
rm -r "$work/case" </dev/null
cp -R "$work/pristine" "$work/case"
cp "$work/pristine/$victim" "$work/case/Extra_Calibration.vo"
status=$(run_case extra "$work/case" "$manifest_py" --check)
expect extra 1 "$status"
expect_text extra "first differing path: external/Flocq/"
cases=$((cases + 1))

# Case: one .vo replaced by a symbolic link to the pristine object.
rm -r "$work/case" </dev/null
cp -R "$work/pristine" "$work/case"
rm "$work/case/$victim"
ln -s "$work/pristine/$victim" "$work/case/$victim"
status=$(run_case symlink "$work/case" "$manifest_py" --check)
expect symlink 2 "$status"
expect_text symlink "refused:"
cases=$((cases + 1))

# Case: FLOCQ_ROOT set empty.
status=$(run_case empty-root "" "$manifest_py" --check)
expect empty-root 2 "$status"
expect_text empty-root "FLOCQ_ROOT is set but empty"
cases=$((cases + 1))

# Case: FLOCQ_ROOT a symbolic link to the Flocq directory.
ln -s "$work/pristine" "$work/rootlink"
status=$(run_case root-link "$work/rootlink" "$manifest_py" --check)
expect root-link 2 "$status"
expect_text root-link "symbolic link"
cases=$((cases + 1))

# Producer copy in its own repository: the manifest sits under its ci/.
repo="$work/repo"
mkdir -p "$repo/ci"
cp "$manifest_py" "$repo/ci/flocq_manifest.py"
producer="$repo/ci/flocq_manifest.py"

# Case: --write creates the manifest, and --check then reports it equal.
status=$(run_case write-fresh "$work/pristine" "$producer" --write)
expect write-fresh 0 "$status"
status=$(run_case write-check "$work/pristine" "$producer" --check)
expect write-check 0 "$status"
expect_text write-check "flocq_manifest: equal, 35 objects"
cases=$((cases + 1))

# Case: a manifest that is a symbolic link is not written through.
printf 'sentinel\n' >"$work/outside.json"
rm "$repo/ci/flocq-manifest.json"
ln -s "$work/outside.json" "$repo/ci/flocq-manifest.json"
status=$(run_case write-linked "$work/pristine" "$producer" --write)
expect write-linked 2 "$status"
expect_text write-linked "is a symbolic link"
[ "$(cat "$work/outside.json")" = "sentinel" ] || {
  echo "check_flocq_manifest: --write changed the target of a symbolic link" >&2
  exit 1
}
cases=$((cases + 1))

# Cases: manifests of the wrong shape are named and exit 1.
rm "$repo/ci/flocq-manifest.json"
printf '[]\n' >"$repo/ci/flocq-manifest.json"
status=$(run_case shape-list "$work/pristine" "$producer" --check)
expect shape-list 1 "$status"
expect_text shape-list "invalid shape"
printf '{"schema_version": 1, "switch": "rocq-9.3", "packages": {}, "flocq_objects": [1]}\n' >"$repo/ci/flocq-manifest.json"
status=$(run_case shape-item "$work/pristine" "$producer" --check)
expect shape-item 1 "$status"
expect_text shape-item "invalid shape"
cases=$((cases + 2))

echo "check_flocq_manifest: $cases case(s) behaved"
