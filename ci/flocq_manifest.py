#!/usr/bin/env python3
"""Per-producer manifest of the Flocq objects of the rocq-9.3 switch.

Usage, under the opam switch that carries Rocq 9.3.0:

    opam exec --switch=rocq-9.3 -- "$PYTHON" -I ci/flocq_manifest.py [--check | --record]

A .vo records the md5 of each OCaml plugin it loads, and a library that requires
Ltac inherits the md5 of ltac_plugin.cmxs. Those plugin bytes depend on the install
prefix of the switch and on the native toolchain that built it (gcc, binutils,
glibc), so every producer of kernel replay evidence holds its own 35 Flocq digests.
ci/flocq-manifest.json (schema_version 2) holds one entry per producer: a name
derived from the toolchain, the toolchain identity, the package versions and the
sha256 of each Flocq .vo.

--check (the default) finds the entry whose ltac_plugin_md5 equals the md5 of the
ltac_plugin.cmxs of the running switch, recomputes the entry from the switch, and
compares the packages and the Flocq objects. It exits 0 when they are equal, 1 when
they differ (the first differing path is printed), when no entry names this
producer, or when the manifest's shape is invalid, and 2 when a refusal applies: the
active opam switch is not rocq-9.3, the Rocq version is not 9.3.0, the Flocq
directory or a symbolic link below it is refused, a toolchain program is missing, or
FLOCQ_ROOT is empty.

--record adds this producer's entry to ci/flocq-manifest.json, or replaces the entry
that has the same name or the same ltac_plugin_md5, and leaves every other entry
byte for byte as it was. A missing manifest or a schema_version 1 manifest (one
producer, no identity) starts a new document. The write goes through a temporary
file in the same directory; a manifest that is a symbolic link is refused.

The toolchain fields gcc, binutils and glibc are the versions that gcc, ld and ldd
report on the producer; they describe the entry and are not compared. The identity
that selects an entry is ltac_plugin_md5, resolved from the switch prefix
($OPAM_SWITCH_PREFIX, else opam's prefix) and never from FLOCQ_ROOT.

The Flocq directory is resolved as ci/kernel_replay_evidence.py resolves it:
FLOCQ_ROOT, else $OPAM_SWITCH_PREFIX/lib/coq/user-contrib/Flocq, else the
library that opam var lib reports. A relative FLOCQ_ROOT resolves below the
repository root. FLOCQ_ROOT is an input the caller names: a run with it set
hashes the directory it names, and the output names that directory. The
objects are the .vo files below that directory, recursively, sorted by their
path as external/Flocq/RELATIVE.vo, and each carries its sha256. Any other
file is not listed.
"""

import hashlib
import json
import os
import re
import subprocess
import sys
from pathlib import Path

SCHEMA_VERSION = 2
SWITCH = "rocq-9.3"
PACKAGES = ("coq-flocq", "rocq-core")
ROCQ_CORE_VERSION = "9.3.0"
FLOCQ_SUFFIX = Path("lib/coq/user-contrib/Flocq")
PLUGIN_SUFFIX = Path("lib/rocq-runtime/plugins/ltac/ltac_plugin.cmxs")
REQUIRED_KEYS = ("schema_version", "switch", "producers")
PRODUCER_KEYS = ("name", "toolchain", "packages", "flocq_objects")
TOOLCHAIN_KEYS = ("gcc", "binutils", "glibc", "ltac_plugin_md5")
NAME_PATTERN = re.compile(r"[a-z0-9][a-z0-9.-]*")
MD5_PATTERN = re.compile(r"[0-9a-f]{32}")
VERSION_PATTERN = re.compile(r"\d+\.\d+(\.\d+)?")
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


def plugin_md5() -> str:
    """The md5 of ltac_plugin.cmxs of the running switch, the digest a .vo records for the plugin."""
    prefix = environment_value("OPAM_SWITCH_PREFIX")
    if prefix is None:
        prefix = run_opam(["var", "prefix"])
    plugin = Path(prefix) / PLUGIN_SUFFIX
    if not plugin.is_file():
        raise Refusal(f"the Ltac plugin is missing below the switch prefix: {PLUGIN_SUFFIX.as_posix()}")
    return hashlib.md5(plugin.read_bytes(), usedforsecurity=False).hexdigest()  # noqa: S324 - the digest a .vo records


def tool_version(program: str, arguments: list[str]) -> str:
    """The version number that the first output line of the program ends with."""
    try:
        output = subprocess.run(  # noqa: S603
            [program, *arguments],
            capture_output=True,
            check=False,
            text=True,
        )
    except OSError as error:
        raise Refusal(f"run {program}: {error}") from error
    lines = output.stdout.splitlines()
    if output.returncode != 0 or not lines:
        raise Refusal(f"{program} {' '.join(arguments)} reports no version")
    for word in reversed(lines[0].split()):
        if VERSION_PATTERN.fullmatch(word.strip("()")):
            return word.strip("()")
    raise Refusal(f"{program} reports no version number: {lines[0]}")


def os_release() -> dict[str, str]:
    try:
        text = Path("/etc/os-release").read_text(encoding="utf-8")
    except OSError as error:
        raise Refusal(f"cannot read /etc/os-release: {error}") from error
    values: dict[str, str] = {}
    for line in text.splitlines():
        name, separator, value = line.partition("=")
        if separator and name in ("ID", "VERSION_ID"):
            values[name] = value.strip().strip('"').strip("'")
    return values


def producer_name(gcc: str) -> str:
    """The distribution id, its version when it has one, and the gcc version: cachyos-gcc-16.2.1."""
    release = os_release()
    parts = [release.get("ID", ""), release.get("VERSION_ID", ""), f"gcc-{gcc}"]
    name = "-".join(part.lower() for part in parts if part)
    if NAME_PATTERN.fullmatch(name) is None:
        raise Refusal(f"the derived producer name is not a plain name: {name}")
    return name


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


def flocq_objects(root: Path) -> list[dict[str, str]]:
    found: list[tuple[str, str]] = []
    collect(root, Path(), found)
    if not found:
        raise Refusal(f"no .vo file below {root}")
    found.sort(key=lambda item: item[0])
    return [{"path": path, "sha256": digest} for path, digest in found]


def build_entry(root: Path) -> dict:
    gcc = tool_version("gcc", ["--version"])
    return {
        "name": producer_name(gcc),
        "toolchain": {
            "gcc": gcc,
            "binutils": tool_version("ld", ["--version"]),
            "glibc": tool_version("ldd", ["--version"]),
            "ltac_plugin_md5": plugin_md5(),
        },
        "packages": switch_packages(),
        "flocq_objects": flocq_objects(root),
    }


def encode(document: dict) -> bytes:
    return (json.dumps(document, indent=2) + "\n").encode("ascii")


def refuse_linked_manifest() -> None:
    if MANIFEST.is_symlink():
        raise Refusal(f"{MANIFEST.relative_to(REPOSITORY)} is a symbolic link; it is not written")


def write_manifest(data: bytes) -> None:
    refuse_linked_manifest()
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


def object_problem(prefix: str, objects: object) -> str | None:
    if not isinstance(objects, list):
        return f"{prefix}flocq_objects is not a list"
    for index, item in enumerate(objects):
        if (
            not isinstance(item, dict)
            or not isinstance(item.get("path"), str)
            or not isinstance(item.get("sha256"), str)
        ):
            return f"{prefix}flocq_objects[{index}] lacks a string path and sha256"
    return None


def producer_problem(index: int, producer: object) -> str | None:
    prefix = f"producers[{index}]."
    if not isinstance(producer, dict):
        return f"producers[{index}] is not a JSON object"
    missing = [key for key in PRODUCER_KEYS if key not in producer]
    if missing:
        return f"producers[{index}] lacks {', '.join(missing)}"
    name = producer["name"]
    if not isinstance(name, str) or NAME_PATTERN.fullmatch(name) is None:
        return f"{prefix}name is not a plain name"
    toolchain = producer["toolchain"]
    if not isinstance(toolchain, dict) or any(not isinstance(toolchain.get(key), str) for key in TOOLCHAIN_KEYS):
        return f"{prefix}toolchain lacks a string {', '.join(TOOLCHAIN_KEYS)}"
    if MD5_PATTERN.fullmatch(toolchain["ltac_plugin_md5"]) is None:
        return f"{prefix}toolchain.ltac_plugin_md5 is not 32 lowercase hexadecimal digits"
    if not isinstance(producer["packages"], dict):
        return f"{prefix}packages is not an object"
    return object_problem(prefix, producer["flocq_objects"])


def manifest_problem(document: object) -> str | None:
    if not isinstance(document, dict):
        return "the top level is not a JSON object"
    if document.get("schema_version") != SCHEMA_VERSION:
        return f"schema_version is {document.get('schema_version')!r}, expected {SCHEMA_VERSION}"
    missing = [key for key in REQUIRED_KEYS if key not in document]
    if missing:
        return f"the manifest lacks {', '.join(missing)}"
    producers = document["producers"]
    if not isinstance(producers, list) or not producers:
        return "producers is not a non-empty list"
    for index, producer in enumerate(producers):
        problem = producer_problem(index, producer)
        if problem is not None:
            return problem
    names = [producer["name"] for producer in producers]
    digests = [producer["toolchain"]["ltac_plugin_md5"] for producer in producers]
    if names != sorted(set(names)):
        return "producers are not sorted by unique name"
    if len(set(digests)) != len(digests):
        return "two producers share one ltac_plugin_md5"
    return None


def read_manifest() -> tuple[bytes, object]:
    try:
        actual = MANIFEST.read_bytes()
    except FileNotFoundError as error:
        raise FileNotFoundError(MANIFEST.relative_to(REPOSITORY)) from error
    except OSError as error:
        raise Refusal(f"cannot read the manifest: {error}") from error
    try:
        return actual, json.loads(actual)
    except ValueError:
        return actual, None


def first_difference(want: dict, have: dict) -> str | None:
    if want["packages"] != have["packages"]:
        return "packages"
    want_objects = want["flocq_objects"]
    have_objects = have["flocq_objects"]
    for index, entry in enumerate(want_objects):
        other = have_objects[index] if index < len(have_objects) else None
        if other != entry:
            return entry["path"]
    if len(have_objects) > len(want_objects):
        return have_objects[len(want_objects)]["path"]
    return None


def compare(entry: dict, root: Path) -> int:
    try:
        actual, have = read_manifest()
    except FileNotFoundError:
        print(f"flocq_manifest: {MANIFEST.relative_to(REPOSITORY)} is missing; run --record")
        return 1
    if have is None:
        print("flocq_manifest: the manifest is not valid JSON; first differing path: (file)")
        return 1
    problem = manifest_problem(have)
    if problem is not None:
        print(f"flocq_manifest: the manifest has an invalid shape: {problem}")
        return 1
    if have["switch"] != SWITCH:
        print("flocq_manifest: switch differs; first differing path: switch")
        return 1
    identity = entry["toolchain"]["ltac_plugin_md5"]
    matches = [producer for producer in have["producers"] if producer["toolchain"]["ltac_plugin_md5"] == identity]
    if not matches:
        print(f"flocq_manifest: no producer has ltac_plugin_md5 {identity}; run --record on this producer")
        return 1
    recorded = matches[0]
    difference = first_difference(entry, recorded)
    if difference is not None:
        print(f"flocq_manifest: producer {recorded['name']}: first differing path: {difference}")
        return 1
    if actual != encode(have):
        print("flocq_manifest: the bytes differ but the parsed content is equal; first differing path: (format)")
        return 1
    count = len(entry["flocq_objects"])
    print(f"flocq_manifest: equal, {count} objects, producer {recorded['name']}, Flocq directory {root}")
    return 0


def existing_producers() -> list[dict]:
    try:
        _, have = read_manifest()
    except FileNotFoundError:
        return []
    if isinstance(have, dict) and have.get("schema_version") == 1:
        return []
    problem = "the manifest is not valid JSON" if have is None else manifest_problem(have)
    if problem is not None:
        raise Refusal(f"the manifest has an invalid shape: {problem}")
    return have["producers"]


def record(entry: dict, root: Path) -> int:
    refuse_linked_manifest()
    kept = []
    replaced = []
    for producer in existing_producers():
        same_name = producer["name"] == entry["name"]
        same_plugin = producer["toolchain"]["ltac_plugin_md5"] == entry["toolchain"]["ltac_plugin_md5"]
        (replaced if same_name or same_plugin else kept).append(producer)
    if len(replaced) > 1:
        names = ", ".join(producer["name"] for producer in replaced)
        raise Refusal(f"the name {entry['name']} and the plugin digest select two entries: {names}")
    producers = sorted([*kept, entry], key=lambda producer: producer["name"])
    document = {"schema_version": SCHEMA_VERSION, "switch": SWITCH, "producers": producers}
    write_manifest(encode(document))
    verb = "replaced" if replaced else "added"
    print(f"flocq_manifest: {verb} producer {entry['name']} in {MANIFEST.relative_to(REPOSITORY)} from {root}")
    return 0


def main(argv: list[str]) -> int:
    arguments = argv[1:]
    if arguments not in ([], ["--check"], ["--record"]):
        print("usage: flocq_manifest.py [--check | --record]", file=sys.stderr)
        return 2
    try:
        root = flocq_root()
        entry = build_entry(root)
        if arguments == ["--record"]:
            return record(entry, root)
    except Refusal as error:
        print(f"flocq_manifest: refused: {error}", file=sys.stderr)
        return 2
    try:
        return compare(entry, root)
    except Refusal as error:
        print(f"flocq_manifest: refused: {error}", file=sys.stderr)
        return 2


if __name__ == "__main__":
    sys.exit(main(sys.argv))
