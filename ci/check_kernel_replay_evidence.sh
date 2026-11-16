#!/bin/sh
# Usage: sh ci/check_kernel_replay_evidence.sh
# Calibrates ci/kernel_replay_evidence.py, the producer of the replay evidence
# that gororoba-open's `gororoba-db theorem identity record-kernel-evidence`
# ingests, on a synthetic three-file proof tree under the opam switch rocq-9.3.
# Known-good inputs must produce evidence in the ingested shape, and a
# verifier compares each record with literal expectations:
#   - a closed theorem over a chain of two imported sources, whose dependency
#     order (Prelude, D900_Base, C900_Test) differs from their lexical order:
#     three compilations in dependency order, the checker and the assumption
#     query, each with its complete argument vector, the source and proof
#     object digests equal to the written files, and an empty assumption list;
#   - a theorem over a declared axiom: the report lists that axiom;
#   - a source that imports Flocq: the recorded objects equal, in sorted
#     order, the .vo files the switch's Flocq library holds, each with its
#     digest, every command maps external/Flocq to Flocq before its target,
#     and flocq_producer names the manifest entry that lists those objects.
#     The Flocq object bytes depend on the install prefix and the native
#     toolchain, so the calibration records the running switch as the one
#     producer of a scratch manifest (ci/flocq_manifest.py --record) and
#     passes it with --flocq-manifest; no hosted runner is a recorded producer.
#     The same holds for the source whose Flocq import carries the control
#     prefix Time, and the producer's Flocq import rule gives the consumer's
#     answer on each command of its test table (gororoba-open
#     theorem_replay.rs, command_imports_flocq).
# Known-bad cases must be refused: a source whose compilation prints a
# warning but exits 0, a source that fails to compile, a declaration name the
# source lacks, a Rocq that reports another version, a Flocq library
# directory without Core/Core.vo, a manifest with no entry for the switch's
# objects, with two such entries, of the wrong schema or unreadable, an output
# directory inside the checkout, a
# git that fails, an output directory that is a symbolic link or becomes one
# during the replay, and a summary that cannot be printed (each leaves no
# evidence file); and mutated copies of the known-good evidence (swapped -R
# pairs, lexical compilation order, a truncated Flocq object list, a Flocq
# producer that is missing or renamed, and more), each of which the verifier
# must reject.
# ci/check_rocq.sh runs it from its export of HEAD. It compiles a few
# sources of a few lines each and writes only under a temporary directory it
# removes, also on INT (status 130) and TERM (status 143). Exit status: 0 every
# case behaved, 1 a case misbehaved, 2 a tool or the switch is missing. The
# last line of its output counts the cases.
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
cleanup() {
  # POSIX rm asks before it removes a write-protected file when standard input
  # is a terminal, and the object files of the repositories under $work are
  # mode 444, so a run from a terminal waits here for an answer (measured,
  # GNU coreutils on Ubuntu 26.04.1). With standard input at /dev/null rm
  # removes them unasked.
  rm -r "$work" </dev/null
}
trap cleanup EXIT
trap 'exit 130' INT
trap 'exit 143' TERM

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

# tree DIR: the fixture proof tree. The theorem imports D900_Base, which
# imports the prerequisite, so the dependency order Prelude, D900_Base,
# C900_Test differs from the lexical order Prelude, C900_Test, D900_Base.
tree() {
  mkdir -p "$1/theories" "$1/verified"
  printf '%s\n' '-R theories OpenGororoba' '-R verified OpenGororobaVerified' \
    theories/Prelude.v verified/C900_Test.v verified/D900_Base.v >"$1/_RocqProject"
  printf '%s\n' 'Definition prerequisite : True := I.' >"$1/theories/Prelude.v"
  printf '%s\n' 'From OpenGororoba Require Import Prelude.' \
    'Definition base : True := prerequisite.' >"$1/verified/D900_Base.v"
  printf '%s\n' 'From OpenGororobaVerified Require Import D900_Base.' \
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


# The verifier compares evidence with literal expectations; it shares no code
# with the producer. A failed comparison raises Mismatch (never an assert, which
# an optimized interpreter removes) and ends the process with status 1.
cat >"$work/verify.py" <<'EOF'
import copy
import hashlib
import json
import os
import sys

TOOLCHAIN = "Rocq 9.3.0; OCaml 5.5.1"
PAIRS = ["-R", "theories", "OpenGororoba", "-R", "verified", "OpenGororobaVerified"]
FLOCQ = ["-R", "external/Flocq", "Flocq"]
CLOSED_ORDER = ["theories/Prelude.v", "verified/D900_Base.v", "verified/C900_Test.v"]


class Mismatch(Exception):
    pass


def check(condition, message):
    if not condition:
        raise Mismatch(message)


def digest(path):
    with open(path, "rb") as handle:
        return hashlib.sha256(handle.read()).hexdigest()


def load(path):
    with open(path) as handle:
        return json.load(handle)


def common(evidence, warning, order, module, flocq, tree):
    keys = ["schema_version", "toolchain", "project_sha256", "sources", "proof_object_sha256"]
    keys += ["flocq_objects", "flocq_producer"] if flocq else []
    keys += ["compilation", "checker", "assumptions"]
    check(list(evidence) == keys, f"evidence fields {list(evidence)}")
    check(evidence["schema_version"] == 1, "schema_version")
    check(evidence["toolchain"] == TOOLCHAIN, "toolchain")
    external = FLOCQ if flocq else []
    compiles = [["compile", "-q", "-w", warning, *PAIRS, *external, target] for target in order]
    check([c["arguments"] for c in evidence["compilation"]] == compiles, "compilation vectors or order")
    check(
        evidence["checker"]["arguments"] == ["check", "-silent", "-o", *PAIRS, *external, module],
        "checker vector",
    )
    check(
        evidence["assumptions"]["arguments"]
        == ["compile", "-q", "-w", warning, *PAIRS, *external, "KernelReceiptAssumptions.v"],
        "assumption vector",
    )
    commands = [*evidence["compilation"], evidence["checker"], evidence["assumptions"]]
    check(all(c["exit_code"] == 0 for c in commands), "exit status")
    check("CONTEXT SUMMARY" in evidence["checker"]["stdout"] + evidence["checker"]["stderr"], "checker summary")
    check(evidence["project_sha256"] == digest(f"{tree}/_RocqProject"), "project digest")
    expected = [{"path": f"proofs/{t}", "sha256": digest(f"{tree}/{t}")} for t in sorted(order)]
    check(evidence["sources"] == expected, "sources or their digests")


def closed(evidence, out, summary, tree):
    common(evidence, "+all", CLOSED_ORDER, "OpenGororobaVerified.C900_Test", False, tree)
    check(evidence["proof_object_sha256"] == digest(f"{out}/verified/C900_Test.vo"), "proof object digest")
    check(
        evidence["assumptions"]["stdout"] == "Declaration: fixture\nClosed under the global context\n",
        "assumption output",
    )
    check(summary["assumptions"] == {"fixture": []}, "reported assumptions")
    for name, value in summary["files"].items():
        check(digest(f"{out}/{name}") == value, f"digest of {name}")


def axiom(evidence, summary, tree):
    common(evidence, "+default", ["verified/C900_Test.v"], "OpenGororobaVerified.C900_Test", False, tree)
    check(summary["assumptions"] == {"fixture": ["postulate"]}, f"reported assumptions {summary['assumptions']}")


def library_objects(library):
    found = []
    for directory, _, names in os.walk(library):
        for name in names:
            if name.endswith(".vo"):
                path = os.path.join(directory, name)
                relative = os.path.relpath(path, library).replace(os.sep, "/")
                found.append({"path": f"external/Flocq/{relative}", "sha256": digest(path)})
    return sorted(found, key=lambda entry: entry["path"])


def manifest_producer(manifest, objects):
    names = [entry["name"] for entry in load(manifest)["producers"] if entry["flocq_objects"] == objects]
    check(len(names) == 1, f"{len(names)} manifest entries list the library's objects")
    return names[0]


def flocq(evidence, library, tree, manifest):
    order = ["theories/Prelude.v", "verified/C900_Test.v"]
    common(evidence, "+default", order, "OpenGororobaVerified.C900_Test", True, tree)
    expected = library_objects(library)
    check("external/Flocq/Core/Core.vo" in [entry["path"] for entry in expected], "library lacks Core/Core.vo")
    check(evidence["flocq_objects"] == expected, "recorded objects differ from the library's .vo files")
    check(evidence["flocq_producer"] == manifest_producer(manifest, expected), "flocq_producer")


def swap(arguments, first):
    arguments[first : first + 6] = arguments[first + 3 : first + 6] + arguments[first : first + 3]


def set_item(sequence, index, value):
    sequence[index] = value


def truncate(arguments):
    del arguments[4:]


def sort_lexically(evidence):
    evidence["compilation"].sort(key=lambda c: c["arguments"][-1])


def core_only(evidence):
    evidence["flocq_objects"] = [o for o in evidence["flocq_objects"] if o["path"] == "external/Flocq/Core/Core.vo"]


def unmap_flocq(evidence):
    del evidence["compilation"][0]["arguments"][-4:-1]


CLOSED_MUTANTS = [
    ("compile -R pairs swapped", lambda e: swap(e["compilation"][0]["arguments"], 4)),
    ("checker -R pairs swapped", lambda e: swap(e["checker"]["arguments"], 3)),
    ("assumption -R pairs swapped", lambda e: swap(e["assumptions"]["arguments"], 4)),
    ("compilation in lexical order", sort_lexically),
    ("compilation reversed", lambda e: e["compilation"].reverse()),
    ("warning argument changed", lambda e: set_item(e["compilation"][0]["arguments"], 3, "+default")),
    ("compile vector cut to its prefix", lambda e: truncate(e["compilation"][1]["arguments"])),
    ("checker module dropped", lambda e: e["checker"]["arguments"].pop()),
    ("assumption exit status", lambda e: set_item(e["assumptions"], "exit_code", 1)),
    ("proof object digest", lambda e: set_item(e, "proof_object_sha256", "0" * 64)),
    ("source digest", lambda e: set_item(e["sources"][0], "sha256", "0" * 64)),
    ("project digest", lambda e: set_item(e, "project_sha256", "0" * 64)),
]
FLOCQ_MUTANTS = [
    ("Flocq objects cut to Core/Core.vo", core_only),
    ("last Flocq object dropped", lambda e: e["flocq_objects"].pop()),
    ("Flocq objects unsorted", lambda e: e["flocq_objects"].reverse()),
    ("Flocq object digest", lambda e: set_item(e["flocq_objects"][0], "sha256", "0" * 64)),
    ("Flocq mapping dropped from a command", unmap_flocq),
    ("Flocq objects absent", lambda e: e.pop("flocq_objects")),
    ("Flocq producer absent", lambda e: e.pop("flocq_producer")),
    ("Flocq producer renamed", lambda e: set_item(e, "flocq_producer", "other-producer")),
]


def reject_all(mutants, evidence, verify):
    verify(evidence)
    for name, mutate in mutants:
        mutated = copy.deepcopy(evidence)
        mutate(mutated)
        if mutated == evidence:
            sys.exit(f"verify mutants: {name} changed nothing")
        try:
            verify(mutated)
        except Mismatch:
            continue
        sys.exit(f"verify mutants: the verifier accepted: {name}")
    return len(mutants)


def main(argv):
    mode, rest = argv[0], argv[1:]
    try:
        if mode == "closed":
            out, log, tree = rest
            closed(load(f"{out}/C900_Test.evidence.json"), out, load(log), tree)
        elif mode == "axiom":
            out, log, tree = rest
            axiom(load(f"{out}/C900_Test.evidence.json"), load(log), tree)
        elif mode == "flocq":
            out, library, tree, manifest = rest
            flocq(load(f"{out}/C900_Test.evidence.json"), library, tree, manifest)
        elif mode == "mutants":
            out, log, tree, flocq_out, library, flocq_tree, manifest = rest
            summary = load(log)
            total = reject_all(CLOSED_MUTANTS, load(f"{out}/C900_Test.evidence.json"), lambda e: closed(e, out, summary, tree))
            total += reject_all(
                FLOCQ_MUTANTS, load(f"{flocq_out}/C900_Test.evidence.json"), lambda e: flocq(e, library, flocq_tree, manifest)
            )
            print(total)
        else:
            sys.exit(f"verify: unknown mode {mode}")
    except Mismatch as error:
        sys.exit(f"verify {mode}: {error}")


main(sys.argv[1:])
EOF

# Known-good: the closed fixture.
tree "$work/good"
produce "$work/good" "$work/out-good" "$work/good.log" --proof verified/C900_Test.v --declaration fixture \
  --warning-policy fatal_all || {
  cat "$work/good.log" >&2
  fail "the producer refused the known-good fixture"
}
"$PYTHON" -I -B "$work/verify.py" closed "$work/out-good" "$work/good.log" "$work/good" ||
  fail "the known-good evidence differs from its expectation"
echo "check_kernel_replay_evidence: closed fixture accepted"

# Known-good: a declared axiom is reported.
tree "$work/axiom"
printf '%s\n' 'Axiom postulate : False.' 'Theorem fixture : False. Proof. exact postulate. Qed.' >"$work/axiom/verified/C900_Test.v"
produce "$work/axiom" "$work/out-axiom" "$work/axiom.log" --proof verified/C900_Test.v --declaration fixture \
  --warning-policy fatal_default || {
  cat "$work/axiom.log" >&2
  fail "the producer refused the fixture with a declared axiom"
}
"$PYTHON" -I -B "$work/verify.py" axiom "$work/out-axiom" "$work/axiom.log" "$work/axiom" ||
  fail "the declared axiom was not reported"
echo "check_kernel_replay_evidence: declared axiom reported"

# Known-good: a source that imports Flocq, produced against a scratch manifest
# that records the running switch as its one producer.
mkdir -p "$work/manifest/ci"
cp "$here/flocq_manifest.py" "$work/manifest/ci/flocq_manifest.py"
opam exec --switch="$switch" -- "$PYTHON" -I -B "$work/manifest/ci/flocq_manifest.py" --record \
  >"$work/record.log" 2>&1 || {
  cat "$work/record.log" >&2
  fail "ci/flocq_manifest.py could not record the running switch"
}
manifest="$work/manifest/ci/flocq-manifest.json"
tree "$work/flocq"
printf '%s\n' 'From Flocq Require Import Core.' 'From OpenGororoba Require Import Prelude.' \
  'Theorem fixture : True. Proof. exact I. Qed.' >"$work/flocq/verified/C900_Test.v"
produce "$work/flocq" "$work/out-flocq" "$work/flocq.log" --proof verified/C900_Test.v --declaration fixture \
  --warning-policy fatal_default --flocq-manifest "$manifest" || {
  cat "$work/flocq.log" >&2
  fail "the producer refused the fixture that imports Flocq"
}
library=$(opam var --switch="$switch" lib)/coq/user-contrib/Flocq
"$PYTHON" -I -B "$work/verify.py" flocq "$work/out-flocq" "$library" "$work/flocq" "$manifest" ||
  fail "the Flocq evidence differs from its expectation"
echo "check_kernel_replay_evidence: Flocq objects recorded"

# The Flocq import rule of the producer equals that of the consumer
# (command_imports_flocq in gororoba-open theorem_replay.rs): the table is the
# consumer's test table, prefixed and quoted forms included.
"$PYTHON" -I -B - "$here" <<'EOF' || fail "the Flocq import rule differs from the consumer's table"
import sys

sys.path.insert(0, sys.argv[1])
from kernel_replay_evidence import command_imports_flocq

table = [
    ("From Flocq Require Import Core", True),
    ("From Flocq.Core Require Import Raux", True),
    ("Require Import Flocq.Core.Core", True),
    ("Time From Flocq Require Import Core", True),
    ('#[warnings("-w")] From Flocq Require Import Core', True),
    ("Time Require Import Flocq.Core.Core", True),
    ("From Stdlib Require Import List", False),
    ("Require Import Stdlib.Reals.Reals", False),
    ("Definition Flocq_unrelated := 0", False),
    ("Require", False),
    ('idtac "Example: Require Import Flocq.Core.Core"', False),
    ('Definition note := "From Flocq Require Import Core"', False),
    ('#[local, warnings("-w")] Require Import Flocq.Core.Core', True),
    ("Timeout 10 Require Import Flocq.Core.Core", True),
    ("#[local Require Import Flocq.Core.Core", False),
]
wrong = [command for command, expected in table if command_imports_flocq(command.split()) != expected]
if wrong:
    print("\n".join(wrong), file=sys.stderr)
    sys.exit(1)
EOF

# Known-good: the same fixture with its Flocq import behind a control prefix.
tree "$work/flocq-prefixed"
printf '%s\n' 'Time From Flocq Require Import Core.' 'From OpenGororoba Require Import Prelude.' \
  'Theorem fixture : True. Proof. exact I. Qed.' >"$work/flocq-prefixed/verified/C900_Test.v"
produce "$work/flocq-prefixed" "$work/out-flocq-prefixed" "$work/flocq-prefixed.log" --proof verified/C900_Test.v \
  --declaration fixture --warning-policy fatal_default --flocq-manifest "$manifest" || {
  cat "$work/flocq-prefixed.log" >&2
  fail "the producer refused the fixture whose Flocq import carries a prefix"
}
"$PYTHON" -I -B "$work/verify.py" flocq "$work/out-flocq-prefixed" "$library" "$work/flocq-prefixed" "$manifest" ||
  fail "the evidence of the prefixed Flocq import differs from its expectation"
echo "check_kernel_replay_evidence: Flocq import rule matches the consumer; prefixed import recorded"

# Known-bad: mutated copies of the known-good evidence. The verifier accepts the
# unmutated records first, then rejects each mutation and prints their count.
mutants=$("$PYTHON" -I -B "$work/verify.py" mutants "$work/out-good" "$work/good.log" "$work/good" \
  "$work/out-flocq" "$library" "$work/flocq" "$manifest") || fail "the verifier accepted a mutated evidence record"
echo "check_kernel_replay_evidence: $mutants mutated evidence records rejected"

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

# Known-bad: a manifest that cannot name this producer. The scratch copies
# below differ from the recorded manifest in one way each.
cat >"$work/edit_manifest.py" <<'EOF'
import copy
import json
import sys

source, target, mode = sys.argv[1:]
with open(source) as handle:
    document = json.load(handle)
producers = document["producers"]
if mode == "digest":
    producers[0]["flocq_objects"][0]["sha256"] = "0" * 64
elif mode == "twin":
    twin = copy.deepcopy(producers[0])
    twin["name"] = "twin-" + twin["name"]
    twin["toolchain"]["ltac_plugin_md5"] = "0" * 32
    producers.append(twin)
elif mode == "schema":
    document["schema_version"] = 1
else:
    sys.exit(f"edit_manifest: unknown mode {mode}")
with open(target, "w") as handle:
    json.dump(document, handle, indent=2)
EOF
# refused_manifest NAME MANIFEST CAUSE: the producer must exit 1 on the Flocq tree
# with a message that holds CAUSE and leave no evidence file.
refused_manifest() {
  if produce "$work/flocq" "$work/out-$1" "$work/$1.log" --proof verified/C900_Test.v --declaration fixture \
    --warning-policy fatal_default --flocq-manifest "$2"; then
    fail "$1: the producer accepted the manifest"
  fi
  [ ! -e "$work/out-$1/C900_Test.evidence.json" ] || fail "$1: a refused run left an evidence file"
  grep -q "$3" "$work/$1.log" || fail "$1: the refusal names another cause: $(head -n 1 "$work/$1.log")"
  echo "check_kernel_replay_evidence: $1 refused"
}
"$PYTHON" -I -B "$work/edit_manifest.py" "$manifest" "$work/manifest-digest.json" digest
refused_manifest manifest-no-producer "$work/manifest-digest.json" '^kernel_replay_evidence: 0 producers'
"$PYTHON" -I -B "$work/edit_manifest.py" "$manifest" "$work/manifest-twin.json" twin
refused_manifest manifest-two-producers "$work/manifest-twin.json" '^kernel_replay_evidence: 2 producers'
"$PYTHON" -I -B "$work/edit_manifest.py" "$manifest" "$work/manifest-schema.json" schema
refused_manifest manifest-schema "$work/manifest-schema.json" 'not a schema_version 2 document'
refused_manifest manifest-missing "$work/manifest-absent.json" 'cannot read the Flocq manifest'

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

# Known-bad: git variables of the caller that hide the repository do not hide it from the producer.
for hidden in "GIT_DIR=$work/no-such-git-dir" "GIT_CEILING_DIRECTORIES=$work/repo/rocq"; do
  if (
    export "${hidden?}"
    produce "$work/repo/rocq/open" "$work/repo/out-env" "$work/env.log" --proof verified/C900_Test.v \
      --declaration fixture --warning-policy fatal_all
  ); then
    fail "the producer accepted an output directory inside the checkout under ${hidden%%=*}"
  fi
  [ ! -e "$work/repo/out-env" ] || fail "a run under ${hidden%%=*} created a directory in the checkout"
  grep -q 'inside the checkout' "$work/env.log" || fail "${hidden%%=*}: the refusal names another cause"
done
echo "check_kernel_replay_evidence: output inside the checkout refused under GIT_DIR and GIT_CEILING_DIRECTORIES"

# Known-bad: a git that fails leaves the checkout unknown, so the run is refused
# before it writes anything.
mkdir "$work/fakegit"
printf '%s\n' '#!/bin/sh' 'echo "fatal: calibration failure" >&2' 'exit 128' >"$work/fakegit/git"
chmod +x "$work/fakegit/git"
if PATH="$work/fakegit:$PATH" produce "$work/repo/rocq/open" "$work/repo/out-git" "$work/git.log" \
  --proof verified/C900_Test.v --declaration fixture --warning-policy fatal_all; then
  fail "the producer accepted a failing git"
fi
[ ! -e "$work/repo/out-git" ] || fail "a failing git left a directory in the checkout"
grep -q 'cannot tell whether git tracks the tree' "$work/git.log" || fail "git: the refusal names another cause"
echo "check_kernel_replay_evidence: failing git refused"

# Known-bad: an output directory that is a symbolic link into the checkout.
mkdir "$work/repo/linked"
ln -s "$work/repo/linked" "$work/out-link"
if produce "$work/good" "$work/out-link" "$work/link.log" --proof verified/C900_Test.v --declaration fixture   --warning-policy fatal_all; then
  fail "the producer accepted a symbolic link as the output directory"
fi
[ -z "$(ls -A "$work/repo/linked")" ] || fail "a refused run wrote through the symbolic link"
grep -q 'symbolic link' "$work/link.log" || fail "link: the refusal names another cause"
echo "check_kernel_replay_evidence: symbolic-link output directory refused"

# Known-bad: the output directory becomes a symbolic link into the checkout
# while the replay runs. The wrapper rocq swaps it at the first compilation.
mkdir "$work/swap" "$work/repo/swapped"
cat >"$work/swap/rocq" <<'EOF'
#!/bin/sh
if [ "$1" = compile ] && [ ! -L "$SWAP_OUT" ]; then
  rmdir "$SWAP_OUT" && ln -s "$SWAP_TARGET" "$SWAP_OUT"
fi
exec "$REAL_BIN/rocq" "$@"
EOF
chmod +x "$work/swap/rocq"
if REAL_BIN=$(opam var --switch="$switch" bin) SWAP_OUT="$work/out-swap" SWAP_TARGET="$work/repo/swapped" \
  PATH="$work/swap:$PATH" "$PYTHON" -I -B "$producer" --tree "$work/good" --out "$work/out-swap" \
  --proof verified/C900_Test.v --declaration fixture --warning-policy fatal_all >"$work/swap.log" 2>&1; then
  fail "the producer wrote after the output directory was replaced"
fi
[ -L "$work/out-swap" ] || fail "swap: the wrapper did not replace the output directory"
[ -z "$(ls -A "$work/repo/swapped")" ] || fail "swap: a run wrote through the replaced directory"
grep -q 'symbolic link' "$work/swap.log" || fail "swap: the refusal names another cause"
echo "check_kernel_replay_evidence: output directory replaced during the replay refused"

# Known-bad: a summary that cannot be printed leaves no evidence file.
if opam exec --switch="$switch" -- "$PYTHON" -I -B "$producer" --tree "$work/good" --out "$work/out-full" \
  --proof verified/C900_Test.v --declaration fixture --warning-policy fatal_all >/dev/full 2>"$work/full.log"; then
  fail "the producer reported success with an unwritable summary"
fi
[ ! -e "$work/out-full/C900_Test.evidence.json" ] || fail "a failed summary left an evidence file"
grep -q 'cannot print the summary' "$work/full.log" || fail "full: the refusal names another cause"
echo "check_kernel_replay_evidence: unwritable summary leaves no evidence"
echo "check_kernel_replay_evidence: 3 known-good and $((16 + mutants)) known-bad cases behaved"
