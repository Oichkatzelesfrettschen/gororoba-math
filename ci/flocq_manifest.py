#!/usr/bin/env python3
"""Manifest of the Flocq objects of the rocq-9.3 switch.

Usage, under the opam switch that carries Rocq 9.3.0:

    opam exec --switch=rocq-9.3 -- "$PYTHON" -I ci/flocq_manifest.py [--check | --write]

--check (the default) recomputes the manifest from the switch and compares it
with ci/flocq-manifest.json. It exits 0 when the two are equal, 1 when they
differ (the first differing path is printed, or the manifest's shape is
invalid), and 2 when a refusal applies: the active opam switch is not
rocq-9.3, the Rocq version is not 9.3.0, the Flocq directory or a symbolic
link below it is refused, or FLOCQ_ROOT is empty. --write replaces
ci/flocq-manifest.json with the recomputed manifest through a temporary file
in the same directory; it refuses a manifest that is a symbolic link.

The Flocq directory is resolved as ci/kernel_replay_evidence.py resolves it:
FLOCQ_ROOT, else $OPAM_SWITCH_PREFIX/lib/coq/user-contrib/Flocq, else the
library that `opam var lib` reports. A relative FLOCQ_ROOT resolves below the
repository root. FLOCQ_ROOT is an input the caller names: a run with it set
hashes the directory it names, and the output names that directory. The
objects are the .vo files below that directory, recursively, sorted by their
path as external/Flocq/RELATIVE.vo, and each carries its sha256. Any other
file is not listed.
"""

import hashlib
import json
import os
import subprocess
import sys
from pathlib import Path

SCHEMA_VERSION = 1
SWITCH = "rocq-9.3"
PACKAGES = ("coq-flocq", "rocq-core")
ROCQ_CORE_VERSION = "9.3.0"
FLOCQ_SUFFIX = Path("lib/coq/user-contrib/Flocq")
REQUIRED_KEYS = ("schema_version", "switch", "packages", "flocq_objects")
REPOSITORY = Path(__file__).resolve().parent.parent
MANIFEST = REPOSITORY / "ci" / "flocq-manifest.json"


class Refusal(Exception):
    """A condition under which no manifest is produced or compared; the run exits 2."""


def run_opam(arguments: list[str]) -> str:
    try:
        output = subprocess.run(  # noqa: S603
            ["opam", *arguments],  # noqa: S607
            capture_output=True,
            check=False,
            text=True,
        )
    except OSError as error:
        raise Refusal(f"run opam {arguments[0]}: {error}") from error
    if output.returncode != 0:
        raise Refusal(f"opam {arguments[0]} failed")
    return output.stdout.strip()


def environment_value(name: str) -> str | None:
    value = os.environ.get(name)
    if value is not None and value == "":
        raise Refusal(f"{name} is set but empty")
    return value


def flocq_root() -> Path:
    named = environment_value("FLOCQ_ROOT")
    prefix = environment_value("OPAM_SWITCH_PREFIX")
    if named is not None:
        configured = Path(named)
    elif prefix is not None:
        configured = Path(prefix) / FLOCQ_SUFFIX
    else:
        library = run_opam(["var", "lib"])
        if not library:
            raise Refusal("the active opam library path is empty")
        configured = Path(library) / "coq/user-contrib/Flocq"
    if not configured.is_absolute():
        configured = REPOSITORY / configured
    if configured.is_symlink():
        raise Refusal(f"the Flocq directory is a symbolic link: {configured}")
    if not (configured / "Core/Core.vo").is_file():
        raise Refusal(f"Flocq Core/Core.vo is missing below {configured}")
    return configured


def switch_packages() -> dict[str, str]:
    active = run_opam(["switch", "show"])
    if active != SWITCH:
        raise Refusal(f"the active opam switch is {active or 'none'}, expected {SWITCH}")
    found: dict[str, str] = {}
    for line in run_opam(["list", "--installed", "--short", "--columns=name,version", "--color=never"]).splitlines():
        fields = line.split()
        if len(fields) == 2 and fields[0] in PACKAGES:
            found[fields[0]] = fields[1]
    missing = [name for name in PACKAGES if name not in found]
    if missing:
        raise Refusal(f"switch lacks installed packages: {', '.join(missing)}")
    if found["rocq-core"] != ROCQ_CORE_VERSION:
        raise Refusal(f"rocq-core is {found['rocq-core']}, expected {ROCQ_CORE_VERSION}")
    return {name: found[name] for name in PACKAGES}


def sha256_file(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def collect(root: Path, relative: Path, found: list[tuple[str, str]]) -> None:
    for entry in sorted((root / relative).iterdir()):
        child = relative / entry.name
        if entry.is_symlink():
            raise Refusal(f"symbolic link below the Flocq directory is refused: {child.as_posix()}")
        if entry.is_dir():
            collect(root, child, found)
        elif entry.suffix == ".vo":
            if not entry.is_file():
                raise Refusal(f"object is not a regular file: {child.as_posix()}")
            found.append((f"external/Flocq/{child.as_posix()}", sha256_file(entry)))


def build_manifest(root: Path) -> bytes:
    found: list[tuple[str, str]] = []
    collect(root, Path(), found)
    if not found:
        raise Refusal(f"no .vo file below {root}")
    found.sort(key=lambda item: item[0])
    document = {
        "schema_version": SCHEMA_VERSION,
        "switch": SWITCH,
        "packages": switch_packages(),
        "flocq_objects": [{"path": path, "sha256": digest} for path, digest in found],
    }
    return (json.dumps(document, indent=2) + "\n").encode("ascii")


def write_manifest(data: bytes) -> None:
    if MANIFEST.is_symlink():
        raise Refusal(f"{MANIFEST.relative_to(REPOSITORY)} is a symbolic link; it is not written")
    temporary = MANIFEST.with_name(f".{MANIFEST.name}.tmp")
    try:
        handle = temporary.open("xb")
    except FileExistsError as error:
        raise Refusal(f"{temporary.name} exists; remove it first") from error
    try:
        with handle:
            handle.write(data)
        os.replace(temporary, MANIFEST)
    except BaseException:
        temporary.unlink(missing_ok=True)
        raise


def manifest_problem(document: object) -> str | None:
    if not isinstance(document, dict):
        return "the top level is not a JSON object"
    missing = [key for key in REQUIRED_KEYS if key not in document]
    if missing:
        return f"the manifest lacks {', '.join(missing)}"
    objects = document["flocq_objects"]
    if not isinstance(objects, list):
        return "flocq_objects is not a list"
    for index, item in enumerate(objects):
        if (
            not isinstance(item, dict)
            or not isinstance(item.get("path"), str)
            or not isinstance(item.get("sha256"), str)
        ):
            return f"flocq_objects[{index}] lacks a string path and sha256"
    return None


def compare(expected: bytes, root: Path) -> int:
    try:
        actual = MANIFEST.read_bytes()
    except FileNotFoundError:
        print(f"flocq_manifest: {MANIFEST.relative_to(REPOSITORY)} is missing; run --write")
        return 1
    except OSError as error:
        print(f"flocq_manifest: refused: cannot read the manifest: {error}")
        return 2
    if actual == expected:
        print(f"flocq_manifest: equal, {len(json.loads(expected)['flocq_objects'])} objects, Flocq directory {root}")
        return 0
    try:
        have = json.loads(actual)
    except ValueError:
        print("flocq_manifest: the manifest is not valid JSON; first differing path: (file)")
        return 1
    problem = manifest_problem(have)
    if problem is not None:
        print(f"flocq_manifest: the manifest has an invalid shape: {problem}")
        return 1
    want = json.loads(expected)
    for key in ("schema_version", "switch", "packages"):
        if want[key] != have[key]:
            print(f"flocq_manifest: {key} differs; first differing path: {key}")
            return 1
    want_objects = want["flocq_objects"]
    have_objects = have["flocq_objects"]
    for index, entry in enumerate(want_objects):
        other = have_objects[index] if index < len(have_objects) else None
        if other != entry:
            print(f"flocq_manifest: first differing path: {entry['path']}")
            return 1
    if len(have_objects) > len(want_objects):
        print(f"flocq_manifest: first differing path: {have_objects[len(want_objects)]['path']}")
        return 1
    print("flocq_manifest: the bytes differ but the parsed content is equal; first differing path: (format)")
    return 1


def main(argv: list[str]) -> int:
    arguments = argv[1:]
    if arguments not in ([], ["--check"], ["--write"]):
        print("usage: flocq_manifest.py [--check | --write]", file=sys.stderr)
        return 2
    try:
        root = flocq_root()
        data = build_manifest(root)
        if arguments == ["--write"]:
            write_manifest(data)
            print(f"flocq_manifest: wrote {MANIFEST.relative_to(REPOSITORY)} from {root}")
            return 0
    except Refusal as error:
        print(f"flocq_manifest: refused: {error}", file=sys.stderr)
        return 2
    return compare(data, root)


if __name__ == "__main__":
    sys.exit(main(sys.argv))
