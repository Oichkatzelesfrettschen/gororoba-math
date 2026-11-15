#!/bin/sh
# Usage: sh ci/check_kernel_replay_evidence.sh
# Calibrates ci/kernel_replay_evidence.py, the producer of the replay evidence
# that gororoba-open's `gororoba-db theorem identity record-kernel-evidence`
# ingests, on a synthetic two-file proof tree under the opam switch rocq-9.3.
# Known-good inputs must produce evidence in the ingested shape:
#   - a closed theorem over one imported source: two compilations in
#     dependency order, the checker, the assumption query, the proof object
#     digest equal to the written .vo, and an empty assumption list;
#   - a theorem over a declared axiom: the report lists that axiom;
#   - a source that imports Flocq: every .vo of the switch's Flocq library is
#     recorded with its digest in sorted order, and every command maps
#     external/Flocq to Flocq before its target.
# Known-bad inputs must be refused with no evidence file written: a source
# whose compilation prints a warning but exits 0, a source that fails to
# compile, a declaration name the source lacks, a Rocq that reports another
# version, a Flocq library directory without Core/Core.vo, and an output
# directory inside the checkout.
# ci/check_rocq.sh runs it from its export of HEAD. It compiles a few
# sources of a few lines each and writes only under a temporary directory it
# removes. Exit status: 0 every case behaved, 1 a case misbehaved, 2 a tool or
# the switch is missing.
set -eu

PYTHON=${PYTHON:-python3}
for tool in git opam sha256sum "$PYTHON"; do
  command -v "$tool" >/dev/null || {
    echo "check_kernel_replay_evidence: $tool is not on PATH" >&2
    exit 2
  }
done
switch=rocq-9.3
opam switch list --short | grep -q -x -F "$switch" || {
  echo "check_kernel_replay_evidence: opam switch $switch does not exist; run sh ci/install_rocq.sh" >&2
  exit 2
}
here=$(CDPATH='' cd -- "$(dirname -- "$0")" && pwd)
producer="$here/kernel_replay_evidence.py"
work=$(mktemp -d "${TMPDIR:-/tmp}/gororoba-math-replay.XXXXXXXX")
trap 'rm -r "$work"' EXIT INT TERM

fail() {
  echo "check_kernel_replay_evidence: $*" >&2
  exit 1
}

# produce TREE OUT LOG [PRODUCER OPTION...]: run the producer under the switch.
produce() {
  tree=$1
  out=$2
  log=$3
  shift 3
  opam exec --switch="$switch" -- "$PYTHON" -I -B "$producer" --tree "$tree" --out "$out" "$@" >"$log" 2>&1
}

# tree DIR: the fixture proof tree, a prerequisite and a theorem that imports it.
tree() {
  mkdir -p "$1/theories" "$1/verified"
  printf '%s\n' '-R theories OpenGororoba' '-R verified OpenGororobaVerified' \
    theories/Prelude.v verified/C900_Test.v >"$1/_RocqProject"
  printf '%s\n' 'Definition prerequisite : True := I.' >"$1/theories/Prelude.v"
  printf '%s\n' 'From OpenGororoba Require Import Prelude.' \
    'Theorem fixture : True. Proof. exact I. Qed.' >"$1/verified/C900_Test.v"
}

# refused NAME TREE CAUSE [DECLARATION]: the producer must exit 1 with a message
# that holds CAUSE and leave no evidence file.
refused() {
  if produce "$2" "$work/out-$1" "$work/$1.log" --proof verified/C900_Test.v --declaration "${4:-fixture}" \
    --warning-policy fatal_all; then
    fail "$1: the producer accepted the input"
  fi
  [ ! -e "$work/out-$1/C900_Test.evidence.json" ] || fail "$1: a refused run left an evidence file"
  grep -q "$3" "$work/$1.log" || fail "$1: the refusal names another cause: $(head -n 1 "$work/$1.log")"
  echo "check_kernel_replay_evidence: $1 refused"
}

# Known-good: the closed fixture.
tree "$work/good"
produce "$work/good" "$work/out-good" "$work/good.log" --proof verified/C900_Test.v --declaration fixture \
  --warning-policy fatal_all || {
  cat "$work/good.log" >&2
  fail "the producer refused the known-good fixture"
}
"$PYTHON" -I -B - "$work/out-good" "$work/good.log" <<'EOF' || fail "the known-good evidence has the wrong shape"
import hashlib, json, sys
out, log = sys.argv[1:]
evidence = json.load(open(f"{out}/C900_Test.evidence.json"))
summary = json.load(open(log))
digest = lambda path: hashlib.sha256(open(path, "rb").read()).hexdigest()
assert list(evidence) == ["schema_version", "toolchain", "project_sha256", "sources", "proof_object_sha256",
                          "compilation", "checker", "assumptions"], list(evidence)
assert evidence["schema_version"] == 1 and evidence["toolchain"] == "Rocq 9.3.0; OCaml 5.5.1"
assert [s["path"] for s in evidence["sources"]] == ["proofs/theories/Prelude.v", "proofs/verified/C900_Test.v"]
assert [c["arguments"][-1] for c in evidence["compilation"]] == ["theories/Prelude.v", "verified/C900_Test.v"]
assert all(c["exit_code"] == 0 and c["arguments"][:4] == ["compile", "-q", "-w", "+all"] for c in evidence["compilation"])
assert evidence["proof_object_sha256"] == digest(f"{out}/verified/C900_Test.vo")
assert "CONTEXT SUMMARY" in evidence["checker"]["stdout"] + evidence["checker"]["stderr"]
assert evidence["assumptions"]["stdout"] == "Declaration: fixture\nClosed under the global context\n"
assert summary["assumptions"] == {"fixture": []}
for name, value in summary["files"].items():
    assert digest(f"{out}/{name}") == value, name
EOF
echo "check_kernel_replay_evidence: closed fixture accepted"

# Known-good: a declared axiom is reported.
tree "$work/axiom"
printf '%s\n' 'Axiom postulate : False.' 'Theorem fixture : False. Proof. exact postulate. Qed.' >"$work/axiom/verified/C900_Test.v"
produce "$work/axiom" "$work/out-axiom" "$work/axiom.log" --proof verified/C900_Test.v --declaration fixture \
  --warning-policy fatal_default || {
  cat "$work/axiom.log" >&2
  fail "the producer refused the fixture with a declared axiom"
}
"$PYTHON" -I -B - "$work/axiom.log" <<'EOF' || fail "the declared axiom was not reported"
import json, sys
summary = json.load(open(sys.argv[1]))
assert summary["assumptions"] == {"fixture": ["postulate"]}, summary["assumptions"]
EOF
echo "check_kernel_replay_evidence: declared axiom reported"

# Known-good: a source that imports Flocq.
tree "$work/flocq"
printf '%s\n' 'From Flocq Require Import Core.' 'From OpenGororoba Require Import Prelude.' \
  'Theorem fixture : True. Proof. exact I. Qed.' >"$work/flocq/verified/C900_Test.v"
produce "$work/flocq" "$work/out-flocq" "$work/flocq.log" --proof verified/C900_Test.v --declaration fixture \
  --warning-policy fatal_default || {
  cat "$work/flocq.log" >&2
  fail "the producer refused the fixture that imports Flocq"
}
library=$(opam var --switch="$switch" lib)/coq/user-contrib/Flocq
"$PYTHON" -I -B - "$work/out-flocq" "$library" <<'EOF' || fail "the Flocq evidence has the wrong shape"
import hashlib, json, sys
out, library = sys.argv[1:]
evidence = json.load(open(f"{out}/C900_Test.evidence.json"))
objects = evidence["flocq_objects"]
assert list(evidence)[5] == "flocq_objects" and [o["path"] for o in objects] == sorted(o["path"] for o in objects)
assert "external/Flocq/Core/Core.vo" in [o["path"] for o in objects]
for entry in objects:
    data = open(f"{library}/{entry['path'][len('external/Flocq/'):]}", "rb").read()
    assert hashlib.sha256(data).hexdigest() == entry["sha256"], entry["path"]
commands = [*evidence["compilation"], evidence["checker"], evidence["assumptions"]]
assert all(c["arguments"][-4:-1] == ["-R", "external/Flocq", "Flocq"] for c in commands)
EOF
echo "check_kernel_replay_evidence: Flocq objects recorded"

# Known-bad: a warning on an exit status of 0.
tree "$work/warning"
printf '%s\n' 'Set Warnings "deprecated".' '#[deprecated(since="1", note="old")]' 'Definition old := 1.' \
  'Definition prerequisite : True := I.' 'Definition use := old.' >"$work/warning/theories/Prelude.v"
refused warning "$work/warning" 'rejects warning output'

# Known-bad: a source that does not compile, and a declaration the source lacks.
tree "$work/failing"
printf '%s\n' 'From OpenGororoba Require Import Prelude.' 'Theorem fixture : False. Proof. exact I. Qed.' \
  >"$work/failing/verified/C900_Test.v"
refused failing "$work/failing" "failed with exit 1"
tree "$work/absent"
refused absent-declaration "$work/absent" "failed with exit 1" missing_name

# Known-bad: a Flocq library directory without Core/Core.vo.
mkdir "$work/no-flocq"
if FLOCQ_ROOT="$work/no-flocq" produce "$work/flocq" "$work/out-no-flocq" "$work/no-flocq.log" \
  --proof verified/C900_Test.v --declaration fixture --warning-policy fatal_default; then
  fail "the producer accepted a Flocq library without Core.vo"
fi
grep -q 'Flocq Core.vo is missing' "$work/no-flocq.log" || fail "no-flocq: the refusal names another cause"
[ ! -e "$work/out-no-flocq/C900_Test.evidence.json" ] || fail "no-flocq: a refused run left an evidence file"
echo "check_kernel_replay_evidence: missing Flocq library refused"

# Known-bad: a Rocq of another version, found first on PATH.
mkdir "$work/fake"
printf '%s\n' '#!/bin/sh' 'echo "The Rocq Prover, version 9.2.0"' 'echo "compiled with OCaml 5.5.0"' >"$work/fake/rocq"
chmod +x "$work/fake/rocq"
if PATH="$work/fake:$PATH" "$PYTHON" -I -B "$producer" --tree "$work/good" --out "$work/out-version" \
  --proof verified/C900_Test.v --declaration fixture --warning-policy fatal_all >"$work/version.log" 2>&1; then
  fail "the producer accepted another Rocq version"
fi
grep -q 'requires Rocq 9.3.0' "$work/version.log" || fail "version: the refusal names another cause"
echo "check_kernel_replay_evidence: other Rocq version refused"

# Known-bad: an output directory inside the checkout that tracks the tree.
mkdir -p "$work/repo/rocq"
tree "$work/repo/rocq/open"
git -C "$work/repo" init -q
git -C "$work/repo" add rocq/open/_RocqProject
if produce "$work/repo/rocq/open" "$work/repo/out" "$work/inside.log" --proof verified/C900_Test.v \
  --declaration fixture --warning-policy fatal_all; then
  fail "the producer accepted an output directory inside the checkout"
fi
[ ! -e "$work/repo/out" ] || fail "a refused run created a directory in the checkout"
grep -q 'inside the checkout' "$work/inside.log" || fail "checkout: the refusal names another cause"
echo "check_kernel_replay_evidence: output inside the checkout refused"
echo "check_kernel_replay_evidence: 3 known-good and 6 known-bad cases behaved"
