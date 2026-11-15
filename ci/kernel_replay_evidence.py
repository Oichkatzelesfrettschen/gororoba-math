"""Kernel replay evidence of one proof source of rocq/open.

Usage, under the opam switch that carries Rocq 9.3.0 (the producer runs the
`rocq` that PATH resolves, as the retained receipts require):

    opam exec --switch=rocq-9.3 -- "$PYTHON" -I ci/kernel_replay_evidence.py \\
        --proof theories/X.v --declaration NAME [--declaration NAME ...] \\
        --warning-policy fatal_default --out OUTDIR [--tree rocq/open]

The producer builds the dependency closure of `--proof` from the sources of
the tree (`--tree`, default `$GOROROBA_MATH/rocq/open`), copies the closure
into a private scratch directory, compiles each source in dependency order
with the fixed argument vectors below, re-checks the proof object with the
kernel checker, runs `Print Assumptions` for each `--declaration`, and writes
into OUTDIR:

- `STEM.evidence.json`, the replay evidence in the shape gororoba-open's
  `gororoba-db theorem identity record-kernel-evidence` ingests
  (`KernelReplayEvidence`, schema_version 1: toolchain, project_sha256,
  sources, proof_object_sha256, flocq_objects when Flocq is used,
  compilation, checker, assumptions);
- `STEM.compile.txt`, `STEM.kernel.txt` and `STEM.assumptions.txt`, the output
  (stdout followed by stderr) of the proof source's compilation, the checker
  and the assumption query, which a witness binds as its compile, kernel and
  assumption logs;
- `ROOT/STEM.vo`, the proof object, below the `theories` or `verified` root of
  the source, which a witness binds as its proof object.

The evidence file is written last and is removed again when the summary
cannot be printed, so a refused or failed run leaves none. Nothing is written
inside the checkout: an OUTDIR below the git repository that tracks the tree's
`_RocqProject` is refused, and so is a git failure that leaves the repository
unknown. OUTDIR is created and checked before the replay starts (not a symbolic
link, its resolved path outside the checkout and disjoint from the tree, empty)
and checked again, against the directory first seen, immediately before the
first write. The tool prints one JSON summary on stdout, with the digest of
every written file and the assumptions each declaration reports, from which a
witness is filled in.

The fixed contract. A source `ROOT/PATH.v` has the logical module
`OpenGororoba.PATH` under `theories` and `OpenGororobaVerified.PATH` under
`verified`, with `/` read as `.`. Compilation runs
`rocq compile -q -w WARNING -R theories OpenGororoba -R verified
OpenGororobaVerified SOURCE` with WARNING `+all` for `fatal_all` and
`+default` for `fatal_default`, the checker `rocq check -silent -o` with the
same two `-R` pairs and the logical module, and the assumption query compiles
`KernelReceiptAssumptions.v` the way a source compiles. A source of the
closure that imports Flocq adds `-R external/Flocq Flocq` before the target of
each command and copies the `.vo` files of a Flocq library into
`external/Flocq` of the scratch directory, recording each one's digest.
Warning lines, error lines, a nonzero exit status and a local absolute path
in any output refuse the run.

Environment. `FLOCQ_ROOT` names the Flocq library directory; without it,
`$OPAM_SWITCH_PREFIX/lib/coq/user-contrib/Flocq` is used, and without that
`opam var lib` gives the library directory (a relative path resolves below the
tree). The directory must hold `Core/Core.vo`. `COQPATH` and `ROCQPATH` are
removed from the environment of every Rocq process, so no library outside the
scratch directory and the installation is visible.

Needs python3 (standard library only), git and the opam switch.

Exit status: 0 evidence written, 1 a refusal or a failed Rocq command, 2 a
usage error, 143 after SIGTERM (the scratch directory is removed first).
"""

import argparse
import hashlib
import json
import os
import signal
import stat
import subprocess  # noqa: S404 - the producer's job is to run the pinned rocq
import sys
import tempfile
from pathlib import Path, PurePosixPath

TOOLCHAIN = "Rocq 9.3.0; OCaml 5.5.1"
VERSION = "The Rocq Prover, version 9.3.0\ncompiled with OCaml 5.5.1"
LOCAL_PATH_PREFIXES = ("/home/", "/root/", "/tmp/", "/run/user/", "/var/tmp/")  # noqa: S108 - patterns to reject
WARNING_ARGUMENTS = {"fatal_all": "+all", "fatal_default": "+default"}
NAMESPACES = {"theories": "OpenGororoba", "verified": "OpenGororobaVerified"}
# The characters of the Unicode White_Space property, which Rust's
# char::is_whitespace, split_whitespace and trim use.
WHITESPACE = frozenset(
    chr(code)
    for code in (
        *range(0x09, 0x0E),
        0x20,
        0x85,
        0xA0,
        0x1680,
        *range(0x2000, 0x200B),
        0x2028,
        0x2029,
        0x202F,
        0x205F,
        0x3000,
    )
)


class Refusal(Exception):
    """A condition that refuses the run."""


def sha256_hex(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def trim(text: str) -> str:
    start, end = 0, len(text)
    while start < end and text[start] in WHITESPACE:
        start += 1
    while end > start and text[end - 1] in WHITESPACE:
        end -= 1
    return text[start:end]


def split_whitespace(text: str) -> list[str]:
    words: list[str] = []
    word: list[str] = []
    for character in text:
        if character in WHITESPACE:
            if word:
                words.append("".join(word))
                word = []
        else:
            word.append(character)
    if word:
        words.append("".join(word))
    return words


def source_commands(source: str) -> list[str]:
    """The commands of a Rocq source with comments removed, split at periods."""
    cursor = 0
    depth = 0
    quoted = False
    visible: list[str] = []
    commands: list[str] = []
    length = len(source)
    while cursor < length:
        character = source[cursor]
        following = source[cursor + 1] if cursor + 1 < length else None
        if not quoted and character == "(" and following == "*":
            depth += 1
            cursor += 2
            continue
        if depth > 0 and character == "*" and following == ")":
            depth -= 1
            cursor += 2
            visible.append(" ")
            continue
        if depth == 0:
            if character == '"':
                quoted = not quoted
                visible.append(character)
            elif not quoted and character == "." and (following is None or following in WHITESPACE or following == "("):
                command = trim("".join(visible))
                if command:
                    commands.append(command)
                visible = []
            else:
                visible.append(character)
        cursor += 1
    if depth != 0 or quoted:
        raise Refusal("proof source has an unterminated comment or string")
    command = trim("".join(visible))
    if command:
        commands.append(command)
    return commands


def relative_source(recorded: str) -> str:
    if not recorded.startswith("proofs/"):
        raise Refusal("replay source must belong to proofs/")
    return recorded[len("proofs/") :]


def logical_module(recorded: str) -> str:
    source = relative_source(recorded)
    if "/" not in source:
        raise Refusal("replay source lacks its root")
    source_root, stem = source.split("/", 1)
    if source_root not in NAMESPACES:
        raise Refusal("unsupported replay source root")
    if not stem.endswith(".v"):
        raise Refusal("replay source needs .v suffix")
    return f"{NAMESPACES[source_root]}.{stem[:-2].replace('/', '.')}"


def compiler_arguments(source: str, warning: str) -> list[str]:
    return [
        "compile",
        "-q",
        "-w",
        warning,
        "-R",
        "theories",
        "OpenGororoba",
        "-R",
        "verified",
        "OpenGororobaVerified",
        source,
    ]


def checker_arguments(proof_path: str) -> list[str]:
    return [
        "check",
        "-silent",
        "-o",
        "-R",
        "theories",
        "OpenGororoba",
        "-R",
        "verified",
        "OpenGororobaVerified",
        logical_module(proof_path),
    ]


def external_arguments(arguments: list[str], flocq: bool) -> list[str]:
    if not flocq:
        return arguments
    return [*arguments[:-1], "-R", "external/Flocq", "Flocq", arguments[-1]]


def regular_file(root: Path, relative: str) -> Path:
    """A regular file below root reached through no symbolic link."""
    candidate = root
    for part in PurePosixPath(relative).parts:
        candidate = candidate / part
        if candidate.is_symlink():
            raise Refusal(f"evidence path contains a symbolic link: {relative}")
    if not candidate.is_file():
        raise Refusal(f"evidence input must be a regular file: {relative}")
    return candidate


def plain_relative(path: str) -> bool:
    parts = PurePosixPath(path).parts
    return bool(parts) and not path.startswith("/") and all(part not in ("", ".", "..") for part in parts)


def collect_sources(root: Path, directory: Path, sources: set[str]) -> None:
    if directory.is_symlink() or not directory.is_dir():
        raise Refusal(f"proof source root must be a regular directory: {directory}")
    for entry in sorted(directory.iterdir()):
        if entry.is_symlink():
            raise Refusal(f"proof inventory rejects symbolic link {entry}")
        if entry.is_dir():
            collect_sources(root, entry, sources)
        elif entry.suffix == ".v":
            if not entry.is_file():
                raise Refusal(f"proof source is not a regular file: {entry}")
            sources.add(entry.relative_to(root).as_posix())


def load_inventory(tree: Path) -> dict[str, str]:
    """Logical module to recorded locator of every source `_RocqProject` lists."""
    project = tree / "_RocqProject"
    if project.is_symlink() or not project.is_file():
        raise Refusal("proof project must be a regular file")
    raw = project.read_text(encoding="utf-8")
    listed: set[str] = set()
    modules: dict[str, str] = {}
    stems: dict[str, str] = {}
    for number, line in enumerate(raw.splitlines(), start=1):
        trimmed = trim(line.split("#", 1)[0])
        if not trimmed or trimmed.startswith("-"):
            continue
        root = trimmed.split("/", 1)[0]
        if (
            not trimmed.endswith(".v")
            or len(split_whitespace(trimmed)) != 1
            or root not in NAMESPACES
            or not plain_relative(trimmed)
        ):
            raise Refusal(f"invalid proof project source at line {number}: {trimmed}")
        if trimmed in listed:
            raise Refusal(f"duplicate proof project source: {trimmed}")
        listed.add(trimmed)
        stem = PurePosixPath(trimmed).stem
        if stem in stems:
            raise Refusal(f"proof legacy-name collision {stem}: {stems[stem]}, {trimmed}")
        stems[stem] = trimmed
        recorded = f"proofs/{trimmed}"
        modules[logical_module(recorded)] = recorded
    if not listed:
        raise Refusal("proof project contains no source entries")
    actual: set[str] = set()
    for root in NAMESPACES:
        if (tree / root).exists():
            collect_sources(tree, tree / root, actual)
    if listed != actual:
        raise Refusal(
            "proof source inventory mismatch; "
            f"missing listed sources: {sorted(listed - actual)}; unlisted disk sources: {sorted(actual - listed)}"
        )
    return modules


def project_dependencies(
    tree: Path,
    proof_path: str,
    modules: dict[str, str],
    visited: set[str],
    ordered: list[str],
) -> None:
    """Append the closure of proof_path in dependency order, dependencies first."""
    if proof_path in visited:
        return
    visited.add(proof_path)
    source = regular_file(tree, relative_source(proof_path)).read_text(encoding="utf-8")
    for command in source_commands(source):
        words = split_whitespace(command)
        if words and words[0] == "Load":
            raise Refusal(f"kernel witness rejects dynamic Load dependencies in {proof_path}")
        if len(words) > 2 and words[0] == "From" and words[2] == "Require":
            namespace = words[1]
            if not any(namespace == root or namespace.startswith(f"{root}.") for root in NAMESPACES.values()):
                continue
            require_position = 2
        elif words and words[0] == "Require":
            namespace = None
            require_position = 0
        else:
            continue
        after = words[require_position + 1] if len(words) > require_position + 1 else None
        first_module = require_position + (2 if after in ("Import", "Export") else 1)
        for name in words[first_module:]:
            if namespace is not None:
                logical = f"{namespace}.{name}"
            elif name.startswith(("OpenGororoba.", "OpenGororobaVerified.")):
                logical = name
            else:
                matches = [module for module in modules if module.rsplit(".", 1)[-1] == name]
                if len(matches) > 1:
                    raise Refusal(f"ambiguous unqualified project import: {name}")
                if not matches:
                    continue
                logical = matches[0]
            if logical not in modules:
                raise Refusal(f"project import is unlisted: {logical}")
            project_dependencies(tree, modules[logical], modules, visited, ordered)
    ordered.append(proof_path)


def uses_flocq(contents: list[str]) -> bool:
    for source in contents:
        for command in source_commands(source):
            words = split_whitespace(command)
            if (
                len(words) > 2
                and words[0] == "From"
                and words[2] == "Require"
                and (words[1] == "Flocq" or words[1].startswith("Flocq."))
            ):
                return True
            if words and words[0] == "Require" and any(word.startswith("Flocq.") for word in words[1:]):
                return True
    return False


def configured_flocq_root(tree: Path) -> Path:
    if os.environ.get("FLOCQ_ROOT") is not None:
        configured = Path(os.environ["FLOCQ_ROOT"])
    elif os.environ.get("OPAM_SWITCH_PREFIX") is not None:
        configured = Path(os.environ["OPAM_SWITCH_PREFIX"]) / "lib/coq/user-contrib/Flocq"
    else:
        try:
            output = subprocess.run(  # noqa: S603
                ["opam", "var", "lib"],  # noqa: S607
                capture_output=True,
                check=False,
            )
        except OSError as error:
            raise Refusal(f"resolve active opam Flocq library: {error}") from error
        if output.returncode != 0 or output.stderr:
            raise Refusal("cannot resolve active opam Flocq library")
        library = output.stdout.decode("utf-8")
        if not trim(library):
            raise Refusal("active opam library path is empty")
        configured = Path(trim(library)) / "coq/user-contrib/Flocq"
    if not configured.is_absolute():
        configured = tree / configured
    if not (configured / "Core/Core.vo").is_file():
        raise Refusal("configured Flocq Core.vo is missing")
    return configured


def copy_flocq_objects(source: Path, destination: Path, relative: Path, objects: list[dict[str, str]]) -> None:
    (destination / relative).mkdir(parents=True, exist_ok=True)
    for entry in sorted((source / relative).iterdir()):
        child = relative / entry.name
        if entry.is_symlink():
            raise Refusal("Flocq replay rejects symbolic library entries")
        if entry.is_dir():
            copy_flocq_objects(source, destination, child, objects)
        elif entry.is_file() and entry.suffix == ".vo":
            data = entry.read_bytes()
            target = destination / child
            target.write_bytes(data)
            if sha256_hex(target.read_bytes()) != sha256_hex(data):
                raise Refusal("Flocq object changed during copy")
            objects.append({"path": f"external/Flocq/{child.as_posix()}", "sha256": sha256_hex(data)})


def trusted_program() -> Path:
    """The first executable `rocq` of PATH, accepted only at Rocq 9.3.0 on OCaml 5.5.1."""
    search = os.environ.get("PATH")
    if search is None:
        raise Refusal("trusted Rocq replay needs a host PATH")
    for directory in search.split(os.pathsep):
        candidate = Path(directory) / "rocq"
        if not candidate.is_file() or not candidate.stat().st_mode & (stat.S_IXUSR | stat.S_IXGRP | stat.S_IXOTH):
            continue
        candidate = Path(os.path.abspath(candidate))
        try:
            output = subprocess.run([str(candidate), "--version"], capture_output=True, check=False)  # noqa: S603
        except OSError as error:
            raise Refusal(f"execute host-selected Rocq version probe: {error}") from error
        if output.returncode != 0 or output.stderr or trim(output.stdout.decode("utf-8")) != VERSION:
            raise Refusal("trusted replay requires Rocq 9.3.0 compiled with OCaml 5.5.1")
        return candidate
    raise Refusal("trusted Rocq replay requires rocq in the host PATH/opam switch")


def command_log(evidence: dict) -> str:
    return f"{evidence['stdout']}\n{evidence['stderr']}"


def run(program: Path, directory: Path, arguments: list[str]) -> dict:
    environment = {name: value for name, value in os.environ.items() if name not in ("COQPATH", "ROCQPATH")}
    try:
        output = subprocess.run(  # noqa: S603
            [str(program), *arguments],
            cwd=directory,
            env=environment,
            capture_output=True,
            check=False,
        )
    except OSError as error:
        raise Refusal(f"execute trusted Rocq replay: {error}") from error
    try:
        stdout = output.stdout.decode("utf-8")
        stderr = output.stderr.decode("utf-8")
    except UnicodeDecodeError as error:
        raise Refusal("Rocq replay output must be UTF-8") from error
    evidence = {
        "arguments": arguments,
        "exit_code": output.returncode if output.returncode >= 0 else -1,
        "stdout": stdout,
        "stderr": stderr,
    }
    if output.returncode != 0:
        raise Refusal(f"trusted Rocq replay failed with exit {evidence['exit_code']}: {command_log(evidence)}")
    return evidence


def validate_command(evidence: dict) -> None:
    """The output checks a retained command must pass."""
    log = command_log(evidence)
    lines = log.splitlines()
    if any(trim(line).startswith("Error:") or "Fatal Error:" in line for line in lines):
        raise Refusal("retained Rocq replay contains an execution error")
    if any(trim(line).startswith("Warning:") for line in lines):
        raise Refusal("trusted Rocq replay rejects warning output")
    if any(prefix in log for prefix in LOCAL_PATH_PREFIXES):
        raise Refusal("Rocq replay output contains a local absolute path")


def labeled_assumption_reports(log: str) -> dict[str, str]:
    reports: dict[str, str] = {}
    for block in log.split("Declaration:")[1:]:
        if "\n" not in block:
            raise Refusal("assumption log has an incomplete declaration label")
        name, contents = block.split("\n", 1)
        name = trim(name)
        if not name or not name.isascii() or len(split_whitespace(name)) != 1:
            raise Refusal(f"assumption log has an invalid declaration label {name}")
        if name in reports:
            raise Refusal(f"assumption log repeats declaration label {name}")
        reports[name] = contents
    return reports


def reported_assumptions(report: str) -> list[str]:
    """The assumptions one declaration's report lists; a report that is neither closed nor listing is refused."""
    observed: list[str] = []
    assumption_section = False
    closed = False
    for original in report.splitlines():
        line = original
        for prefix in ("Rocq < ", "Coq < "):
            if original.startswith(prefix):
                line = original[len(prefix) :]
                break
        trimmed = trim(line)
        if trimmed in ("Axioms:", "Section Variables:"):
            if closed:
                raise Refusal("assumption log combines a closed context with assumptions")
            assumption_section = True
        elif trimmed == "Closed under the global context":
            if assumption_section:
                raise Refusal("assumption log combines assumptions with a closed context")
            closed = True
        elif assumption_section and line[:1] not in WHITESPACE and ":" in line:
            name = trim(line.split(":", 1)[0])
            if not name or not name.isascii() or len(split_whitespace(name)) != 1:
                raise Refusal(f"invalid assumption report header: {name}")
            if name in observed:
                raise Refusal(f"duplicate reported assumption: {name}")
            observed.append(name)
    if assumption_section == closed or (assumption_section and not observed):
        raise Refusal("assumption log lacks a complete declaration-specific context result")
    return observed


def valid_declaration_name(name: str) -> bool:
    return (
        bool(name)
        and (name[0].isalpha() or name[0] == "_")
        and all(character.isalnum() or character in "_'" for character in name)
    )


def produce(
    tree: Path,
    proof: str,
    declarations: list[str],
    policy: str,
    out: Path,
    checkout: Path | None,
    identity: tuple[int, int],
) -> tuple[dict, Path]:
    """The summary of the written files and the path of the evidence file."""
    if policy not in WARNING_ARGUMENTS:
        raise Refusal("trusted replay requires a fatal warning policy")
    warning = WARNING_ARGUMENTS[policy]
    for name in declarations:
        if not valid_declaration_name(name):
            raise Refusal(f"unsupported declaration name syntax: {name}")
    if len(set(declarations)) != len(declarations):
        raise Refusal("a declaration is listed twice")
    proof_path = proof if proof.startswith("proofs/") else f"proofs/{proof}"
    logical = logical_module(proof_path)
    modules = load_inventory(tree)
    if proof_path not in modules.values():
        raise Refusal("kernel witness proof is outside the active source inventory")
    ordered: list[str] = []
    project_dependencies(tree, proof_path, modules, set(), ordered)
    contents = {source: regular_file(tree, relative_source(source)).read_bytes() for source in ordered}
    project_sha256 = sha256_hex((tree / "_RocqProject").read_bytes())
    program = trusted_program()
    with tempfile.TemporaryDirectory(prefix="gororoba-rocq-replay-") as scratch_name:
        scratch = Path(scratch_name)
        (scratch / "theories").mkdir()
        (scratch / "verified").mkdir()
        for source in ordered:
            destination = scratch / relative_source(source)
            destination.parent.mkdir(parents=True, exist_ok=True)
            destination.write_bytes(contents[source])
            if sha256_hex(destination.read_bytes()) != sha256_hex(contents[source]):
                raise Refusal(f"source changed while preparing replay: {source}")
        flocq_objects: list[dict[str, str]] = []
        if uses_flocq([contents[source].decode("utf-8") for source in ordered]):
            copy_flocq_objects(configured_flocq_root(tree), scratch / "external/Flocq", Path(), flocq_objects)
            flocq_objects.sort(key=lambda entry: entry["path"])
        flocq = bool(flocq_objects)
        compilation = [
            run(program, scratch, external_arguments(compiler_arguments(relative_source(source), warning), flocq))
            for source in ordered
        ]
        object_path = (scratch / relative_source(proof_path)).with_suffix(".vo")
        proof_object = object_path.read_bytes()
        checker = run(program, scratch, external_arguments(checker_arguments(proof_path), flocq))
        query = f"Require Import {logical}.\n"
        for name in declarations:
            query += (
                f'Goal True.\nProof.\n  idtac "Declaration: {name}".\n  exact I.\nQed.\n'
                f"Print Assumptions {logical}.{name}.\n"
            )
        (scratch / "KernelReceiptAssumptions.v").write_text(query, encoding="utf-8")
        assumptions = run(
            program,
            scratch,
            external_arguments(compiler_arguments("KernelReceiptAssumptions.v", warning), flocq),
        )
        for entry in flocq_objects:
            if sha256_hex((scratch / entry["path"]).read_bytes()) != entry["sha256"]:
                raise Refusal("Flocq replay object changed during execution")
    for command in [*compilation, checker, assumptions]:
        validate_command(command)
    if "CONTEXT SUMMARY" not in command_log(checker):
        raise Refusal("trusted checker replay lacks its context summary")
    reports = labeled_assumption_reports(command_log(assumptions))
    if set(reports) != set(declarations):
        raise Refusal("trusted assumption replay has a different declaration set")
    reported = {name: reported_assumptions(reports[name]) for name in declarations}
    evidence: dict = {
        "schema_version": 1,
        "toolchain": TOOLCHAIN,
        "project_sha256": project_sha256,
        "sources": [{"path": source, "sha256": sha256_hex(contents[source])} for source in sorted(ordered)],
        "proof_object_sha256": sha256_hex(proof_object),
    }
    if flocq_objects:
        evidence["flocq_objects"] = flocq_objects
    evidence["compilation"] = compilation
    evidence["checker"] = checker
    evidence["assumptions"] = assumptions

    relative = relative_source(proof_path)
    stem = PurePosixPath(relative).stem
    outputs = {
        f"{stem}.compile.txt": (compilation[-1]["stdout"] + compilation[-1]["stderr"]).encode("utf-8"),
        f"{stem}.kernel.txt": (checker["stdout"] + checker["stderr"]).encode("utf-8"),
        f"{stem}.assumptions.txt": (assumptions["stdout"] + assumptions["stderr"]).encode("utf-8"),
        str(PurePosixPath(relative).with_suffix(".vo")): proof_object,
    }
    encoded = (json.dumps(evidence, indent=2) + "\n").encode("ascii")
    check_output(out, checkout, tree, identity)
    for name, data in outputs.items():
        target = out / name
        target.parent.mkdir(parents=True, exist_ok=True)
        target.write_bytes(data)
    evidence_path = out / f"{stem}.evidence.json"
    try:
        evidence_path.write_bytes(encoded)
    except BaseException:
        evidence_path.unlink(missing_ok=True)
        raise
    files = {name: sha256_hex(data) for name, data in outputs.items()}
    files[f"{stem}.evidence.json"] = sha256_hex(encoded)
    summary = {
        "proof_path": proof_path,
        "toolchain": TOOLCHAIN,
        "project_sha256": project_sha256,
        "sources": evidence["sources"],
        "files": files,
        "assumptions": reported,
    }
    return summary, evidence_path


def git_output(tree: Path, arguments: list[str]) -> subprocess.CompletedProcess:
    """One git command in the tree, with messages in the C locale so a refusal can read them.

    The caller's GIT_* variables are dropped: GIT_DIR or GIT_CEILING_DIRECTORIES can make git
    answer "not a git repository" inside the checkout that tracks the tree.
    """
    environment = {name: value for name, value in os.environ.items() if not name.startswith("GIT_")}
    environment["LC_ALL"] = "C"
    return subprocess.run(  # noqa: S603
        ["git", "-C", str(tree), *arguments],  # noqa: S607
        capture_output=True,
        check=False,
        env=environment,
    )


def checkout_of(tree: Path) -> Path | None:
    """The top level of the git repository that tracks the tree's `_RocqProject`, if any.

    Only git's two answers "no repository" and "path not tracked" give None; every other
    failure leaves the checkout unknown and refuses the run.
    """
    tracked = git_output(tree, ["ls-files", "--error-unmatch", "--", "_RocqProject"])
    message = tracked.stderr.decode("utf-8", errors="replace")
    if tracked.returncode == 1 and "did not match any file(s) known to git" in message:
        return None
    if tracked.returncode == 128 and "not a git repository" in message:
        return None
    if tracked.returncode != 0:
        raise Refusal(f"cannot tell whether git tracks the tree (git exit {tracked.returncode}): {trim(message)}")
    top = git_output(tree, ["rev-parse", "--show-toplevel"])
    location = top.stdout.decode("utf-8", errors="replace").strip()
    if top.returncode != 0 or not location:
        raise Refusal(f"cannot find the checkout that tracks the tree (git exit {top.returncode})")
    return Path(location).resolve()


def inside(path: Path, root: Path) -> bool:
    return path == root or root in path.parents


def check_output(out: Path, checkout: Path | None, tree: Path, identity: tuple[int, int] | None) -> tuple[int, int]:
    """Refuse an output directory that is unsafe to write; return its (device, inode).

    The directory must be a real directory that `out` reaches through no symbolic link, lie
    outside the checkout and disjoint from the tree, hold nothing, and, once `identity` is
    known, be the directory first seen.
    """
    found = out.lstat()
    if not stat.S_ISDIR(found.st_mode):
        raise Refusal("the output directory must be a directory and not a symbolic link")
    if out.resolve(strict=True) != out:
        raise Refusal("the output directory path contains a symbolic link")
    if checkout is not None and inside(out, checkout):
        raise Refusal("the output directory lies inside the checkout that holds the tree")
    if inside(out, tree) or inside(tree, out):
        raise Refusal("the output directory and the tree must be disjoint")
    if any(out.iterdir()):
        raise Refusal("the output directory must be absent or empty")
    if identity is not None and (found.st_dev, found.st_ino) != identity:
        raise Refusal("the output directory was replaced during the replay")
    return found.st_dev, found.st_ino


def prepare_output(name: str, checkout: Path | None, tree: Path) -> tuple[Path, tuple[int, int]]:
    """Create the output directory and return its resolved path and identity."""
    requested = Path(name)
    if requested.is_symlink():
        raise Refusal("the output directory must be a directory and not a symbolic link")
    out = requested.resolve()
    if checkout is not None and inside(out, checkout):
        raise Refusal("the output directory lies inside the checkout that holds the tree")
    if inside(out, tree) or inside(tree, out):
        raise Refusal("the output directory and the tree must be disjoint")
    out.mkdir(parents=True, exist_ok=True)
    return out, check_output(out, checkout, tree, None)


def terminate(signal_number: int, frame: object) -> None:
    """Unwind to the scratch directory's cleanup when SIGTERM arrives."""
    raise SystemExit(128 + signal_number)


def main(arguments: list[str]) -> int:
    signal.signal(signal.SIGTERM, terminate)
    parser = argparse.ArgumentParser(description="Produce the kernel replay evidence of one proof source.")
    parser.add_argument("--tree", help="proof tree directory, default $GOROROBA_MATH/rocq/open")
    parser.add_argument("--proof", required=True, help="proof source below the tree, such as theories/X.v")
    parser.add_argument("--declaration", action="append", required=True, help="declaration name; repeatable")
    parser.add_argument("--warning-policy", required=True, choices=sorted(WARNING_ARGUMENTS))
    parser.add_argument("--out", required=True, help="output directory, absent or empty, outside the checkout")
    try:
        options = parser.parse_args(arguments)
    except SystemExit as error:
        return 2 if error.code else 0
    tree_name = options.tree
    if tree_name is None:
        if not os.environ.get("GOROROBA_MATH"):
            print(
                "kernel_replay_evidence: pass --tree or set GOROROBA_MATH to a gororoba-math checkout", file=sys.stderr
            )
            return 2
        tree_name = str(Path(os.environ["GOROROBA_MATH"]) / "rocq/open")
    try:
        tree = Path(tree_name).resolve(strict=True)
        checkout = checkout_of(tree)
        out, identity = prepare_output(options.out, checkout, tree)
        summary, evidence_path = produce(
            tree, options.proof, options.declaration, options.warning_policy, out, checkout, identity
        )
    except (Refusal, OSError, UnicodeDecodeError) as error:
        print(f"kernel_replay_evidence: {error}", file=sys.stderr)
        return 1
    try:
        sys.stdout.write(json.dumps(summary, indent=2) + "\n")
        sys.stdout.flush()
    except BaseException as error:
        evidence_path.unlink(missing_ok=True)
        if not isinstance(error, OSError):
            raise
        print(f"kernel_replay_evidence: cannot print the summary: {error}", file=sys.stderr)
        return 1
    return 0


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
