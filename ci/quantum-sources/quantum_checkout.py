"""Locations that the generators of this directory share, and the rule that confines their writes.

ROOT is the gororoba-quantum checkout named by GOROROBA_QUANTUM: the generators read gororoba_quantum/cd_core.py,
gororoba_quantum/parallel.py and the evidence records there. ROCQ is the directory of the Rocq sources they render.

A write (`--write`, `--generate`, or the default mode of span_certificate.py) goes only to rocq/quantum of this
checkout and to the JSON record beside the generator: ROCQ is then that directory resolved, which must lie inside
this checkout and be no symbolic link, with no symbolic link among its `.v` files; QUANTUM_SOURCES_ROCQ, `--output`,
`--rocq`, `--record` and every other option end the run with status 2 (an option is accepted in a write only when it
is the write flag or an abbreviation of it, which argparse also reads as a write). Only `--check` and the other
read modes honor QUANTUM_SOURCES_ROCQ, which must name an
existing directory (ci/check_quantum_sources.sh points it at a scratch copy to calibrate the comparison), and a read
creates no file or directory. Importing the module ends the process with status 2 when GOROROBA_QUANTUM does not
name a checkout that holds gororoba_quantum/cd_core.py.
"""

from __future__ import annotations

import os
import sys
from pathlib import Path

MATH = Path(__file__).resolve().parents[2]
WRITE_FLAGS = ("--write", "--generate")


def refuse(message: str) -> SystemExit:
    print(f"quantum_checkout: {message}", file=sys.stderr)
    return SystemExit(2)


def _write_flag(token: str) -> bool:
    """True for a write flag and for each prefix of one that argparse accepts as its abbreviation."""
    return len(token) > 2 and any(flag.startswith(token) for flag in WRITE_FLAGS)


def _quantum_root() -> Path:
    value = os.environ.get("GOROROBA_QUANTUM", "")
    if not value or not (Path(value) / "gororoba_quantum" / "cd_core.py").is_file():
        raise refuse("set GOROROBA_QUANTUM to a gororoba-quantum checkout")
    return Path(value).resolve()


def _tracked_rocq() -> Path:
    path = MATH / "rocq" / "quantum"
    if path.is_symlink() or not path.is_dir() or not path.resolve().is_relative_to(MATH.resolve()):
        raise refuse(f"{path} is no plain directory of this checkout")
    for source in path.glob("*.v"):
        if source.is_symlink():
            raise refuse(f"{source} is a symbolic link")
    return path.resolve()


def _rocq() -> Path:
    override = os.environ.get("QUANTUM_SOURCES_ROCQ", "")
    if writing:
        loose = [token for token in sys.argv[1:] if token.startswith("-") and not _write_flag(token)]
        if override or loose:
            raise refuse(
                "a write goes to rocq/quantum of this checkout only; refused: "
                + " ".join([*(["QUANTUM_SOURCES_ROCQ"] if override else []), *loose])
            )
        return _tracked_rocq()
    if not override:
        return _tracked_rocq()
    scratch = Path(override)
    if not scratch.is_dir():
        raise refuse(f"QUANTUM_SOURCES_ROCQ={override} is no existing directory")
    return scratch.resolve()


def confine_record(path: Path, own: Path) -> None:
    """End the run with status 2 unless `path` is the record `own` that sits beside the generator, no link."""
    if own.is_symlink() or path.resolve() != own.resolve():
        raise refuse(f"a write of {path.name} goes to {own.name} beside the generator only")


writing = any(_write_flag(token) for token in sys.argv[1:])
ROOT = _quantum_root()
ROCQ = _rocq()
