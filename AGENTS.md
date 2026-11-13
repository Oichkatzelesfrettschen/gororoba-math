# gororoba-math agent guide

This repository is public. It holds the workspace's machine-checked
mathematics: Lean 4 under `lean/`, with `ci/check.sh` as the admission gate.
The workspace guide (`workspace/AGENTS.md` in gororoba-infrastructure, linked
as `AGENTS.md` in the directory above this checkout) holds the rules every
gororoba repository shares; this file governs where the two differ.

## Layout

- `lean/GororobaMath/` is the library; `lean/GororobaMath.lean` imports every
  module of it, and a new module is added there in the commit that creates
  it. A file sits under the directory of its subject
  (`CayleyDickson/`, `KernelMap/`) and declares its results in that subject's
  namespace.
- `lean/AxiomAudit.lean` defines `#audit_axioms`; `lean/AuditFixture.lean` is
  its known-bad input and no library module imports it; `lean/audit/` holds
  the files the gate and the on-demand checks run.
- `ci/check.sh` is the admission gate. `ci/compare_signs.sh` runs on demand
  and needs `GOROROBA_QUANTUM`.

## Statements and proofs

- A library declaration depends only on `propext`, `Classical.choice` and
  `Quot.sound`. A statement that waits on a proof stays on its branch; `main`
  holds no `sorry`, no `native_decide` and no declared axiom outside
  `lean/AuditFixture.lean`.
- A definition that mirrors code in another gororoba repository names that
  function in its docstring and has a comparison under `ci/` that runs both
  on the same inputs; `ci/compare_signs.sh` is the model.
- A module docstring states the convention the file fixes (the product, the
  index order, the sign) before its results, because the workspace's
  Rocq, Python and Rust code each carry one and a theorem reads on another
  repository only through it.
- State a theorem at the generality its proof has: every level `k`, every
  ring, every characteristic-zero field. A statement about `A_5` alone is the
  instance `k = 5` of a tower theorem where one exists.
- The library builds with warnings as errors (`lake build --wfail`).

## Toolchain and build tree

- `lean/lean-toolchain` and the Mathlib tag in `lean/lakefile.toml` move
  together: set both, run `lake update` and `lake exe cache get` in `lean/`,
  and commit `lean/lake-manifest.json` with them.
- On the workstations `lean/.lake` is a symbolic link to a directory outside
  the checkout (`ln -s /srv/data/build/gororoba-math/lake lean/.lake` before
  the first `lake` command), since the Mathlib build tree is about 7 GB and
  build trees stay outside checkouts. A session worktree makes the same link
  to the same directory, so the worktrees share one Mathlib.

## Landing

Edit in a session worktree under `~/worktrees/gororoba-math/<branch>`,
commit, run `sh ci/check.sh`, and land by pull request with the review chain
of the workspace guide ("Reviews and merges"). The `lean` workflow runs the
same gate on the pull-request head.

## Text

Checked-in text is emoji-free American English. Lean sources use the
Unicode notation of Mathlib; Markdown and shell stay ASCII where a symbol
has an ASCII spelling.
