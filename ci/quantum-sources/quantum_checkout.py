"""Locations that the generators of this directory share.

ROOT is the gororoba-quantum checkout named by GOROROBA_QUANTUM: the generators read gororoba_quantum/cd_core.py,
gororoba_quantum/parallel.py and the evidence records there. ROCQ is the directory of the Rocq sources they render,
rocq/quantum of this checkout, or the directory QUANTUM_SOURCES_ROCQ names (ci/check_quantum_sources.sh points it at
a scratch copy to calibrate the comparison). Importing the module ends the process with status 2 when
GOROROBA_QUANTUM does not name a checkout that holds gororoba_quantum/cd_core.py.
"""

from __future__ import annotations

import os
import sys
from pathlib import Path

MATH = Path(__file__).resolve().parents[2]


def _quantum_root() -> Path:
    value = os.environ.get("GOROROBA_QUANTUM", "")
    if not value or not (Path(value) / "gororoba_quantum" / "cd_core.py").is_file():
        print("quantum_checkout: set GOROROBA_QUANTUM to a gororoba-quantum checkout", file=sys.stderr)
        raise SystemExit(2)
    return Path(value).resolve()


ROOT = _quantum_root()
ROCQ = Path(os.environ.get("QUANTUM_SOURCES_ROCQ") or MATH / "rocq" / "quantum").resolve()
