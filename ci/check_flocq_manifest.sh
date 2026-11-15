#!/bin/sh
# Usage: sh ci/check_flocq_manifest.sh
# Calibrates ci/flocq_manifest.py, which records the Flocq objects of the
# rocq-9.3 switch in ci/flocq-manifest.json. The known-good case runs --check
# on the real switch and requires exit 0. Each known-bad case runs --check on a
# scratch copy of the switch's Flocq directory, through FLOCQ_ROOT, and
# requires: one byte of one .vo changed exits 1; one .vo removed exits 1; one
# extra .vo exits 1; one .vo replaced by a symbolic link exits 2 (refused).
# Every case that exits 1 must name a differing path on its output.
# The scratch copies live under FLOCQ_BUILD_DIR (default TMPDIR or /tmp) and
# are removed on exit, also on INT (status 130) and TERM (status 143).
# Needs git, opam, cmp, dd and PYTHON (default python3) on PATH. Exit status:
# 0 every case behaved, 1 a case misbehaved, 2 a tool or the switch is missing.
set -eu

PYTHON=${PYTHON:-python3}
export PYTHON
for tool in git opam cmp dd "$PYTHON"; do
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
trap 'rm -r "$work"' EXIT
trap 'exit 130' INT
trap 'exit 143' TERM

flocq=$(opam exec --switch="$switch" -- sh -c 'printf "%s" "$OPAM_SWITCH_PREFIX/lib/coq/user-contrib/Flocq"') || {
  echo "check_flocq_manifest: cannot resolve the Flocq directory of $switch" >&2
  exit 2
}
cp -R "$flocq" "$work/pristine"

# run_check ROOT LABEL: runs --check with FLOCQ_ROOT set to ROOT (unset when
# ROOT is empty) and prints the exit status; the output goes to LABEL.out.
run_check() {
  if [ -n "$1" ]; then
    FLOCQ_ROOT="$1" opam exec --switch="$switch" -- "$PYTHON" -I "$manifest_py" --check >"$work/$2.out" 2>&1 && echo 0 || echo $?
  else
    env -u FLOCQ_ROOT opam exec --switch="$switch" -- "$PYTHON" -I "$manifest_py" --check >"$work/$2.out" 2>&1 && echo 0 || echo $?
  fi
}

# expect LABEL WANT GOT: fails the run when a case exits other than WANT.
expect() {
  if [ "$3" != "$2" ]; then
    echo "check_flocq_manifest: $1 exited $3, expected $2" >&2
    cat "$work/$1.out" >&2
    exit 1
  fi
}

cases=0
status=$(run_check "" known-good)
expect known-good 0 "$status"
cases=$((cases + 1))

victim=$(cd "$work/pristine" && find . -name '*.vo' | LC_ALL=C sort | head -n 1)
victim=${victim#./}
[ -n "$victim" ] || {
  echo "check_flocq_manifest: the switch's Flocq directory holds no .vo" >&2
  exit 1
}

# Case: one byte of one .vo changed.
rm -r "$work/case" 2>/dev/null || true
cp -R "$work/pristine" "$work/case"
printf 'X' | dd of="$work/case/$victim" bs=1 count=1 conv=notrunc 2>/dev/null
cmp -s "$work/pristine/$victim" "$work/case/$victim" && {
  echo "check_flocq_manifest: the byte mutation left $victim unchanged" >&2
  exit 1
}
status=$(run_check "$work/case" byte)
expect byte 1 "$status"
grep -q -F "external/Flocq/$victim" "$work/byte.out" || {
  cat "$work/byte.out" >&2
  echo "check_flocq_manifest: the byte case did not name external/Flocq/$victim" >&2
  exit 1
}
cases=$((cases + 1))

# Case: one .vo removed.
rm -r "$work/case"
cp -R "$work/pristine" "$work/case"
rm "$work/case/$victim"
status=$(run_check "$work/case" removed)
expect removed 1 "$status"
cases=$((cases + 1))

# Case: one extra .vo.
rm -r "$work/case"
cp -R "$work/pristine" "$work/case"
cp "$work/pristine/$victim" "$work/case/Extra_Calibration.vo"
status=$(run_check "$work/case" extra)
expect extra 1 "$status"
cases=$((cases + 1))

# Case: one .vo replaced by a symbolic link to the pristine object.
rm -r "$work/case"
cp -R "$work/pristine" "$work/case"
rm "$work/case/$victim"
ln -s "$work/pristine/$victim" "$work/case/$victim"
status=$(run_check "$work/case" symlink)
expect symlink 2 "$status"
grep -q -F "symbolic link" "$work/symlink.out" || {
  cat "$work/symlink.out" >&2
  echo "check_flocq_manifest: the symlink case did not report the refusal" >&2
  exit 1
}
cases=$((cases + 1))

echo "check_flocq_manifest: $cases case(s) behaved"
