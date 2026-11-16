#!/bin/sh
# Usage: sh ci/check_flocq_manifest.sh
# Calibrates ci/flocq_manifest.py, which records the Flocq objects of the
# rocq-9.3 switch, one entry per producer, in ci/flocq-manifest.json. Every
# case runs the producer and requires its exit status and a named output
# text. The known-good case runs on a producer that the manifest records
# (the entry is selected by the md5 of the switch's ltac_plugin.cmxs), so the
# script runs on demand on such a host.
# On a scratch copy of the switch's Flocq directory, through FLOCQ_ROOT:
#   known-good: --check on the real switch exits 0 and reports equal;
#   one byte of one .vo changed, one .vo removed, one extra .vo: --check exits
#     1 and names the differing external/Flocq/ path;
#   one .vo replaced by a symbolic link: exits 2 with a refusal;
#   FLOCQ_ROOT empty, and FLOCQ_ROOT a symbolic link: exit 2 with a refusal.
# On a scratch copy of the producer with its own repository and manifest:
#   --record creates the manifest and --check then exits 0;
#   a second --record leaves the manifest bytes unchanged;
#   --record beside a foreign producer's entry keeps that entry byte for byte,
#     and --check then exits 0;
#   a manifest that records only a foreign producer: --check exits 1 and
#     names the missing plugin digest;
#   a manifest that is a symbolic link: --record exits 2 and its target keeps
#     its bytes;
#   manifests of the wrong shape (a list, an item that is no object, schema
#     version 1): --check exits 1 and names the shape.
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

# Case: --record creates the manifest, and --check then reports it equal.
status=$(run_case record-fresh "$work/pristine" "$producer" --record)
expect record-fresh 0 "$status"
expect_text record-fresh "added producer"
status=$(run_case record-check "$work/pristine" "$producer" --check)
expect record-check 0 "$status"
expect_text record-check "flocq_manifest: equal, 35 objects, producer "
cases=$((cases + 1))

# Case: a second --record replaces the entry and leaves the bytes unchanged.
cp "$repo/ci/flocq-manifest.json" "$work/recorded.json"
status=$(run_case record-again "$work/pristine" "$producer" --record)
expect record-again 0 "$status"
expect_text record-again "replaced producer"
cmp -s "$work/recorded.json" "$repo/ci/flocq-manifest.json" || {
  echo "check_flocq_manifest: a second --record changed the manifest" >&2
  exit 1
}
cases=$((cases + 1))

# edit_manifest.py SOURCE TARGET MODE writes a scratch manifest: mode foreign
# adds a second producer, zz-foreign, with another plugin digest and other
# object digests; mode foreign-only keeps that producer and drops the rest.
cat >"$work/edit_manifest.py" <<'EOF'
import copy
import json
import sys

source, target, mode = sys.argv[1:]
with open(source) as handle:
    document = json.load(handle)
foreign = copy.deepcopy(document["producers"][0])
foreign["name"] = "zz-foreign"
foreign["toolchain"]["ltac_plugin_md5"] = "1" * 32
foreign["flocq_objects"][0]["sha256"] = "2" * 64
if mode == "foreign":
    document["producers"].append(foreign)
elif mode == "foreign-only":
    document["producers"] = [foreign]
else:
    sys.exit(f"edit_manifest: unknown mode {mode}")
with open(target, "w") as handle:
    json.dump(document, handle, indent=2)
    handle.write("\n")
EOF

# Case: --record beside a foreign entry keeps that entry byte for byte.
"$PYTHON" -I -B "$work/edit_manifest.py" "$repo/ci/flocq-manifest.json" "$work/foreign.json" foreign
cp "$work/foreign.json" "$repo/ci/flocq-manifest.json"
status=$(run_case record-foreign "$work/pristine" "$producer" --record)
expect record-foreign 0 "$status"
"$PYTHON" -I -B - "$work/foreign.json" "$repo/ci/flocq-manifest.json" <<'EOF' || {
import json
import sys

with open(sys.argv[1]) as handle:
    before = json.load(handle)["producers"]
with open(sys.argv[2]) as handle:
    after = json.load(handle)["producers"]
if after != before:
    sys.exit("the producers differ after recording a recorded producer")
EOF
  echo "check_flocq_manifest: --record changed a foreign entry" >&2
  exit 1
}
status=$(run_case record-foreign-check "$work/pristine" "$producer" --check)
expect record-foreign-check 0 "$status"
cases=$((cases + 1))

# Case: a manifest that records only a foreign producer has no entry for this one.
"$PYTHON" -I -B "$work/edit_manifest.py" "$repo/ci/flocq-manifest.json" "$work/foreign-only.json" foreign-only
cp "$work/foreign-only.json" "$repo/ci/flocq-manifest.json"
status=$(run_case foreign-only "$work/pristine" "$producer" --check)
expect foreign-only 1 "$status"
expect_text foreign-only "no producer has ltac_plugin_md5"
cases=$((cases + 1))

# Case: a manifest that is a symbolic link is not written through.
printf 'sentinel\n' >"$work/outside.json"
rm "$repo/ci/flocq-manifest.json"
ln -s "$work/outside.json" "$repo/ci/flocq-manifest.json"
status=$(run_case record-linked "$work/pristine" "$producer" --record)
expect record-linked 2 "$status"
expect_text record-linked "is a symbolic link"
[ "$(cat "$work/outside.json")" = "sentinel" ] || {
  echo "check_flocq_manifest: --record changed the target of a symbolic link" >&2
  exit 1
}
cases=$((cases + 1))

# Cases: manifests of the wrong shape are named and exit 1.
rm "$repo/ci/flocq-manifest.json"
printf '[]\n' >"$repo/ci/flocq-manifest.json"
status=$(run_case shape-list "$work/pristine" "$producer" --check)
expect shape-list 1 "$status"
expect_text shape-list "invalid shape"
printf '{"schema_version": 2, "switch": "rocq-9.3", "producers": [1]}\n' >"$repo/ci/flocq-manifest.json"
status=$(run_case shape-item "$work/pristine" "$producer" --check)
expect shape-item 1 "$status"
expect_text shape-item "invalid shape"
printf '{"schema_version": 1, "switch": "rocq-9.3", "packages": {}, "flocq_objects": []}\n' >"$repo/ci/flocq-manifest.json"
status=$(run_case shape-schema "$work/pristine" "$producer" --check)
expect shape-schema 1 "$status"
expect_text shape-schema "schema_version is 1"
cases=$((cases + 3))

echo "check_flocq_manifest: $cases case(s) behaved"
