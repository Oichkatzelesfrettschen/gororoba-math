# gororoba-math agent guide

This repository is public. It holds the workspace's machine-checked
mathematics: Lean 4 under `lean/` and Rocq under `rocq/`, with `ci/check.sh`
and `ci/check_rocq.sh` as the admission gate.
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
  the files the gate and the on-demand checks run. The gate takes the module
  list from `git ls-files`, so it builds and audits a module the root file
  omits and then fails on the omission.
- `rocq/open/` is the proof tree that gororoba-open held under `proofs/`
  (imported at its commit 604b7e74 with history): `theories/` under the
  logical root `OpenGororoba`, `verified/` under `OpenGororobaVerified`, its
  own `Makefile` and `_RocqProject`, and `opam/`, an opam repository of the
  ports its switch needs.
- `rocq/quantum/` is the set of proof files that gororoba-quantum held under
  `proofs/` (imported at its commit a3237e3dc with history), compiled under
  the empty logical root, so `Require Import CdTowerDomain.` carries no
  prefix; `StiefelWitnessInvertible.v` imports `OpenGororobaVerified` from
  `rocq/open/verified`. The retained replay of that one file in
  gororoba-quantum compiles it as `GororobaQuantum.StiefelWitnessInvertible`
  (`-Q quantum GororobaQuantum`); no source imports it, so both names
  compile the same source, and the object this gate builds carries the
  unprefixed name.
- `ci/check.sh` is the Lean half of the admission gate and
  `ci/check_rocq.sh` the Rocq half; `ci/install_rocq.sh` builds the opam
  switch the Rocq half needs. `ci/compare_signs.sh` runs on demand and needs
  `GOROROBA_QUANTUM`.
- `ci/quantum-sources/` holds the generators of eight `rocq/quantum` sources
  (`CdSignPythonSemantics.v`, `CdSignSourceCertificate.v`, `TargetFlipN21.v`,
  `CdTowerCanonicalKernels.v`, `CdTowerG2Derivations.v`,
  `A5W8ArcMatrixRanks.v`, `CdTowerG2DerivationSpan.v` and
  `StiefelWitnessInvertible.v`), the JSON records three of them render
  (`certificates.json`, `left-inverses.json`, `span.json`), and the helpers of
  the span certificate. A generator reads `gororoba_quantum/cd_core.py`,
  `parallel.py` and evidence records of the checkout `GOROROBA_QUANTUM`
  names, so no admission check runs it. `ci/check_quantum_sources.sh` renders
  each source again, requires it to equal the tracked file, rejects a copy
  with one digit changed and a `cd_core.py` with one changed shift, refuses
  unsafe writes, and compares the Stiefel package cross-check with the retained
  record; `ci/replay_quantum_bundles.sh` compares the
  ledgers of the retained bundles of gororoba-quantum with `rocq/quantum`
  (`--ledgers-only` stops there and needs no Rocq) and runs their replays.
  Both run on demand. The generator files here are the live ones: a source
  of `rocq/quantum` that a generator renders changes through its generator,
  in the same commit. A write (`--write`, `--generate`, and the default mode
  of `span_certificate.py`) goes only to `rocq/quantum` of this checkout and
  to the JSON record beside the generator: the generators refuse
  `QUANTUM_SOURCES_ROCQ` and every option but the write flag in a write, and
  refuse a `rocq/quantum` that is a link or holds a linked `.v`; only
  `--check` honors `QUANTUM_SOURCES_ROCQ` (an existing directory, nothing
  created), which the calibration of `ci/check_quantum_sources.sh` uses. The
  helper scripts `make_mutants.py` and `make_span_mutants.py` write to the
  directory named on their command line, a scratch directory by use. A
  replay script of a retained bundle runs from a shadow root: it holds copies
  of the bundle and of `rocq/quantum`, and symbolic links to the entries of
  the gororoba-quantum checkout that the bundle's ledgers name, which the
  script could write; it is not given `GOROROBA_QUANTUM`. A generator that a
  retained ledger of gororoba-quantum binds (`cd_sign_rocq_ast.py`,
  `cd_sign_source_ast.py`, `target_flip_certificate.py`,
  `kernel_certificates.py` with `certificates.json`; and
  `span_certificate.py`, `render_span.py` and `span.json`, which row A5-500 of
  the findings ledger of gororoba-quantum cites, with `gaussian_certificates.py`,
  which both import, and `left-inverses.json`, which they read) keeps its bytes
  there, as the record of the commit that ledger names or cites, and no gate
  there renders a source from it. The rendered
  sources keep their header and marker lines, which name the path of the
  generator in gororoba-quantum, because the retained records cite those bytes.

## Statements and proofs

- A declaration of the Lean library depends only on `propext`,
  `Classical.choice` and `Quot.sound`. A statement that waits on a proof
  stays on its branch; under `lean/`, `main` holds no `sorry`, no
  `native_decide` and no declared axiom outside `lean/AuditFixture.lean`.
- A definition that mirrors code in another gororoba repository names that
  function in its docstring and has a comparison under `ci/` that runs both
  on the same inputs and rejects a mutated reference: `ci/compare_signs.sh`
  for `Tower.sign`, `ci/compare_estimator.sh` for the nullity estimator.
- A module docstring states the convention the file fixes (the product, the
  index order, the sign) before its results, because the workspace's
  Rocq, Python and Rust code each carry one and a theorem reads on another
  repository only through it.
- State a theorem at the generality its proof has: every level `k`, every
  ring, every characteristic-zero field. A statement about `A_5` alone is the
  instance `k = 5` of a tower theorem where one exists.
- The library builds with warnings as errors (`lake build --wfail`).

## Rocq sources

- A new source of `rocq/open/theories`, `rocq/open/verified` or
  `rocq/quantum` is listed in the `_RocqProject` of its tree in the commit
  that adds it; `ci/check_rocq.sh` fails on a tracked source the project
  file omits and on a listed source without a compiled object. A source
  anywhere else under `rocq/` is named in one of the two lists at the top
  of `ci/check_rocq.sh` (compiled by a make target of `rocq/open` or by
  the script, or held uncompiled), and the script fails on a tracked source
  neither names.
- `rocq/open` compiles its project-listed sources, checkpoints and plugin
  fixtures with `-w +default`, which makes each warning of Rocq's default
  set an error; its `extract` recipe passes no warning option.
  `rocq/quantum` compiles with `-w @all`, the
  flag of its retained replays, under which `rocq` prints a warning and
  exits 0; the gate fails on a warning line in the build log. No source of
  `rocq/open/theories`, `rocq/open/verified` or `rocq/quantum` holds
  `Admitted` or `admit` (`rocq/open/admission_check.rs`).
- `ci/check_rocq.sh` re-checks every project-listed module with the kernel
  checker (`rocq check -silent -o`) and compares the axioms it reports with
  `rocq/open/kernel-assumptions.txt` and
  `rocq/quantum/kernel-assumptions.txt`. A change that adds or removes an
  axiom a tree rests on changes that tree's ledger in the same commit.
- Retained records in gororoba-open and gororoba-quantum cite sources of
  these trees by sha256. Before editing a source, `git grep` its digest in
  both repositories; a cited source keeps its bytes, and a change lands in a
  successor file.
- `ci/check_rocq.sh` builds in an export of `HEAD` outside the checkout, so
  commit before running it; `ROCQ_BUILD_DIR` names the parent directory of
  that export.

## Toolchain and build tree

- `lean/lean-toolchain` and the Mathlib tag in `lean/lakefile.toml` move
  together: set both, run `lake update` and `lake exe cache get` in `lean/`,
  and commit `lean/lake-manifest.json` with them.
- On the workstations `lean/.lake` is a symbolic link, made before the first
  `lake` command, to a Lake tree outside the checkout, since the Mathlib
  build tree is about 7 GB and build trees stay outside checkouts. The
  primary checkout's tree holds the packages, fetched there first with
  `lake exe cache get`. Each session worktree has a tree of its own, made
  in three steps, with `TREE` a new directory outside every checkout and
  `PRIMARY_TREE` the primary checkout's tree: `mkdir -p "$TREE"`,
  `ln -s "$PRIMARY_TREE/packages" "$TREE/packages"`, and, from the
  worktree root, `ln -s "$TREE" lean/.lake`. The worktrees then share one
  Mathlib and each keeps its own `build/`. `ci/check.sh` builds the library
  and then audits the compiled objects in a second step, and a `build/`
  that two worktrees share lets a build in one replace the objects the
  other audits or elaborates against.
- The shared `packages` link holds only while the worktree's
  `lean/lean-toolchain` and `lean/lake-manifest.json` equal the primary
  checkout's. A worktree that changes either, the toolchain bump above
  included, replaces the link with a `packages` directory of its own before
  `lake update` or `lake exe cache get`, since both rewrite the packages.
- `git worktree remove` deletes the `lean/.lake` link and leaves the tree
  it pointed at; the tree is removed with its worktree. The build-host
  record of gororoba-infrastructure names the directories.

- The root `Makefile` builds the working tree: `make lean`, and `make rocq`,
  which copies `rocq/` into `BUILD_DIR/rocq` (default `build`, ignored)
  and compiles both trees there with the options of their `_RocqProject`
  files. On a workstation `build` is a symbolic link to a directory
  outside the checkout, or `BUILD_DIR` names one, one per worktree; the
  targets refuse any other path inside the checkout, and `make clean`
  removes only a tree that carries the marker file `rocq-sync` wrote. A
  compile inside `rocq/` leaves objects beside the sources; git ignores
  them, and `ci/check_rocq.sh` never reads them, since it exports `HEAD`.

## Landing

Edit in a session worktree under `~/worktrees/gororoba-math/<branch>`,
commit, run `sh ci/check.sh`, and `sh ci/check_rocq.sh` when the change
touches `rocq/` or the Rocq scripts, and land by pull request, merged by
merge commit so that an imported history stays, with the review chain of
the workspace guide ("Reviews and merges"). The `lean` workflow runs the
first script and the `rocq` workflow the second on every pull request.

## Text

Checked-in text is emoji-free American English. Lean sources use the
Unicode notation of Mathlib; Markdown and shell stay ASCII where a symbol
has an ASCII spelling. The Rocq trees keep the ASCII convention of
gororoba-open.
