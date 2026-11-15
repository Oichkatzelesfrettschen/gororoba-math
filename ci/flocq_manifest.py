#!/usr/bin/env python3
"""Manifest of the Flocq objects of the rocq-9.3 switch.

Usage, under the opam switch that carries Rocq 9.3.0:

    opam exec --switch=rocq-9.3 -- "$PYTHON" -I ci/flocq_manifest.py [--check | --write]

--check (the default) recomputes the manifest from the switch and compares it
with ci/flocq-manifest.json. It exits 0 when the two are equal, 1 when they
differ (the first differing path is printed), and 2 when a refusal applies:
the switch, opam or the Flocq directory is missing, the Rocq version is not
9.3.0, or a symbolic link lies below the Flocq directory. --write replaces
ci/flocq-manifest.json with the recomputed manifest and exits 0.

The Flocq directory is resolved as ci/kernel_replay_evidence.py resolves it:
FLOCQ_ROOT, else $OPAM_SWITCH_PREFIX/lib/coq/user-contrib/Flocq, else the
library that `opam var lib` reports. A relative FLOCQ_ROOT resolves below the
repository root. The objects are the regular .vo files below that directory,
recursively, sorted by their path as external/Flocq/RELATIVE.vo, and each
carries its sha256. Any other file is not listed.
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
REPOSITORY = Path(__file__).resolve().parent.parent
MANIFEST = REPOSITORY / "ci" / "flocq-manifest.json"


class Refusal(Exception):
    """A condition under which no manifest is produced; the run exits 2."""


def flocq_root() -> Path:
    if os.environ.get("FLOCQ_ROOT") is not None:
        configured = Path(os.environ["FLOCQ_ROOT"])
    elif os.environ.get("OPAM_SWITCH_PREFIX") is not None:
        configured = Path(os.environ["OPAM_SWITCH_PREFIX"]) / FLOCQ_SUFFIX
    else:
        try:
            output = subprocess.run(  # noqa: S603
                ["opam", "var", "lib"],  # noqa: S607
                capture_output=True,
                check=False,
            )
        except OSError as error:
            raise Refusal(f"resolve active opam library: {error}") from error
        library = output.stdout.decode("utf-8").strip()
        if output.returncode != 0 or output.stderr or not library:
            raise Refusal("cannot resolve the active opam library")
        configured = Path(library) / "coq/user-contrib/Flocq"
    if not configured.is_absolute():
        configured = REPOSITORY / configured
    if not (configured / "Core/Core.vo").is_file():
        raise Refusal(f"Flocq Core/Core.vo is missing below {configured}")
    return configured


def switch_packages() -> dict[str, str]:
    try:
        output = subprocess.run(  # noqa: S603
            ["opam", "list", "--installed", "--short", "--columns=name,version", "--color=never"],  # noqa: S607
            capture_output=True,
            check=False,
            text=True,
        )
    except OSError as error:
        raise Refusal(f"run opam list: {error}") from error
    if output.returncode != 0:
        raise Refusal("opam list --installed failed")
    found: dict[str, str] = {}
    for line in output.stdout.splitlines():
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
        elif entry.is_file() and entry.suffix == ".vo":
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


def compare(expected: bytes) -> int:
    try:
        actual = MANIFEST.read_bytes()
    except FileNotFoundError:
        print(f"flocq_manifest: {MANIFEST.relative_to(REPOSITORY)} is missing; run --write", file=sys.stderr)
        return 1
    if actual == expected:
        print(f"flocq_manifest: equal, {len(json.loads(expected)['flocq_objects'])} objects")
        return 0
    want = json.loads(expected)
    try:
        have = json.loads(actual)
    except ValueError:
        print("flocq_manifest: the manifest file is not valid JSON; first differing path: (file)")
        return 1
    for key in ("schema_version", "switch", "packages"):
        if want[key] != have.get(key):
            print(f"flocq_manifest: {key} differs; first differing path: {key}")
            return 1
    for index, entry in enumerate(want["flocq_objects"]):
        other = have["flocq_objects"][index] if index < len(have["flocq_objects"]) else None
        if other != entry:
            print(f"flocq_manifest: first differing path: {entry['path']}")
            return 1
    if len(have["flocq_objects"]) > len(want["flocq_objects"]):
        extra = have["flocq_objects"][len(want["flocq_objects"])]["path"]
        print(f"flocq_manifest: first differing path: {extra}")
        return 1
    print("flocq_manifest: the bytes differ but the parsed content is equal; first differing path: (format)")
    return 1


def main(argv: list[str]) -> int:
    mode = argv[1:] or ["--check"]
    if mode not in (["--check"], ["--write"]):
        print("usage: flocq_manifest.py [--check | --write]", file=sys.stderr)
        return 2
    try:
        data = build_manifest(flocq_root())
    except Refusal as error:
        print(f"flocq_manifest: refused: {error}", file=sys.stderr)
        return 2
    if mode == ["--write"]:
        MANIFEST.write_bytes(data)
        print(f"flocq_manifest: wrote {MANIFEST.relative_to(REPOSITORY)}")
        return 0
    return compare(data)


if __name__ == "__main__":
    sys.exit(main(sys.argv))
