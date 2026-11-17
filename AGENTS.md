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
- `lean/ReplayFixture.lean` is the known-bad input of the kernel replay:
  a declaration of type `False` added under `debug.skipKernelTC`, which
  the build and the axiom audit both accept and `leanchecker` rejects. No
  library module imports it.
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
- `rocq/delegation/` is the delegation model (`Model.v`, logical root
  `GororobaDelegation`) and three sources that
  `ci/delegation-sources/render_inventory.py` renders from the statement
  inventories of gororoba-open (`curated/01_theory_frameworks/
  confine_theorems_N.v`); a rendered source changes through the generator,
  and `ci/check_delegation_sources.sh` renders them again from the checkout
  `GOROROBA_OPEN` names, on demand.
- `ci/check.sh` is the Lean half of the admission gate and
  `ci/check_rocq.sh` the Rocq half; `ci/install_rocq.sh` builds the opam
  switch the Rocq half needs. `ci/compare_signs.sh` runs on demand and needs
  `GOROROBA_QUANTUM` and `ROCQ_BUILD_TREE`, the `rocq` directory of a tree
  that `make rocq` compiled; `ci/audit/SignTable.v` is its Rocq source,
  kept outside `rocq/` because the gate admits there only project-listed
  sources.
  `ci/flocq_manifest.py` checks `ci/flocq-manifest.json`, which holds one entry
  per producer of kernel replay evidence (schema_version 2): its name, its
  toolchain identity (gcc, binutils, glibc, and the md5 of the switch's
  `ltac_plugin.cmxs` that selects the entry) and the sha256 of each Flocq
  `.vo` of its rocq-9.3 switch. `ci/check_flocq_manifest.sh` calibrates it.
  Both run on demand on a producer: a `.vo` records the md5 of each OCaml plugin
  it loads, and the plugin bytes depend on the install prefix and the native
  toolchain (measured: the same opam export gives other object bytes on the
  hosted runner, first at `Calc/Bracket.vo`, and under another prefix), so
  each producer holds its own 35 digests and no admission check compares a
  switch with the manifest. `ci/flocq_manifest.py --record` adds or replaces
  the entry of the producer it runs on.
  `ci/kernel_replay_evidence.py` produces the kernel replay evidence that
  gororoba-open ingests for a theorem receipt, and
  `ci/check_kernel_replay_evidence.sh` calibrates it; `ci/check_rocq.sh` runs
  that calibration from its export of `HEAD`.
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
  `native_decide` and no declared axiom outside `lean/AuditFixture.lean`
  (a challenge module, below, holds `sorry` by design),
  and no `debug.skipKernelTC` outside `lean/ReplayFixture.lean`. The
  gate replays every tracked module through `leanchecker`, one call per
  module, and keeps `lean/GororobaMath.lean` to `module` and its imports
  of the library, since `leanchecker` reads its argument as a module-name
  prefix and replays every matching module at once, so a call on the root
  name replays the whole library concurrently (30.5 to 32.1 GB measured
  with Lean 4.35.0 on the eight-module library of an earlier commit,
  against 6.4 GB for one module); a
  metaprogram can add a declaration that the build and the axiom audit
  accept and the kernel rejects. The replay assumes what a module
  imports, so a library module imports only the library and the package's
  dependencies (Mathlib and what it requires), and
  `lean/lakefile.toml` sets no `srcDir`; the gate checks both.
- A definition that mirrors code in another gororoba repository names that
  function in its docstring and has a comparison under `ci/` that runs both
  on the same inputs and rejects a mutated reference: `ci/compare_signs.sh`
  for `Tower.sign`, which it also compares with both Rocq sign functions of
  `rocq/quantum/SignBridge.v`, `ci/compare_estimator.sh` for the nullity
  estimator and `ci/compare_estimator_rocq.sh` for its Rocq partner in
  `rocq/quantum/KernelMapEstimator.v`, `ci/compare_dot.sh` for `Tower.dot` and `Tower.re`,
  `ci/compare_alignment.sh` for `Tower.partner`, `Tower.alignedAdd` and
  `Tower.alignedSub`, which it compares with the integer instance of
  `rocq/quantum/CdTowerTwoTermBridge.v`,
  `ci/compare_aligned_pair_count.sh` for `Tower.alignedPairCount` against
  `aligned_pair_count` of `rocq/quantum/CdTowerTwoTermRecursion.v`, and
  `ci/compare_aligned_pair_forms.sh` for `Tower.alignedPairCountMultiplicity`,
  `Tower.closedForm`, `Tower.clearedXorBit`, `Tower.DegenerateSplit`,
  `Tower.clearedXorParity` (at every `t` from 0 to `k`), `Tower.associates` and `KernelMap.binContract` against their partners in
  `rocq/quantum/CdTowerAlignedPairSpectrum.v`,
  `CdTowerAlignedPairClosedForm.v`, `CdTowerAssociatorSpace.v` and
  `CdTowerTwoTermBins.v`.
  `ci/compare_kernel_map_bins.sh` evaluates `KernelMap.binContract`,
  the hypothesis of `KernelMap.nullity_eq_alignedPairCount_of_binContract`,
  on `pathion_kernel_map.kernel_map_circuit` for every two-term operand at
  level 5, 6 or 7, and on the coset-block circuits of the wide runs.
- A new result, a statement that the README or a record cites, is placed
  on two axes, checked in this order; a helper lemma goes where its result
  is.
  - Pinned bytes. A source that a retained record cites by sha256 keeps its
    bytes and its tree ("Rocq sources").
  - Statement. A statement quantified over a class of rings, fields or
    modules, or over every level `k`, and a statement of real or complex
    analysis are proved in Lean on Mathlib. The Lean
    tower over `NonAssocRing` with `StarRing` is the general carrier:
    Mathlib holds no Cayley-Dickson or octonion development, and MathComp's
    rings are associative. A statement about one fixed algebra or one fixed
    coefficient type (a fixed level, the integers, the rationals) that
    instances a Lean theorem stays beside that theorem, also where its
    proof evaluates a finite table (as the fixed-level counts of
    `TwoTerm.lean` do). Any other such statement is proved in the prover
    that holds every definition it mentions; when both hold them, in Lean
    when its proof is symbolic and in Rocq when it is a decision by
    evaluation. A finite group or combinatorial structure goes
    to the prover whose library holds it: MathComp's finite groups in Rocq,
    Mathlib's group theory in Lean.
  - Evidence. A certificate that a proof evaluates (a rendered table, a
    rank, a kernel basis, a sign table), a definition that is extracted or
    compiled to running code, a statement about floating-point behavior,
    and a statement that a theorem receipt of gororoba-open rests on are
    Rocq artifacts: gororoba-open runs no prover and admits the kernel
    replay evidence that `ci/kernel_replay_evidence.py` writes from a Rocq
    build, and `vm_compute` evaluates certificates. Evaluation is faster in
    Rocq and the kernel re-check slower: on the sign-anticommutativity table
    of level `k`, `vm_compute` ran 3.4 to 8.5 times faster than Lean's
    `decide +kernel` for `k` from 5 to 8, and `rocq check` of the level-8
    object took 51 s against 19 s for Lean's kernel decision (measured
    2026-11-16, Rocq 9.3.0, Lean 4.35.0, one 4-vCPU host;
    `docs/archive/measurements/h1-vm-compute-decide-kernel.md`), so a large
    certificate states both costs. Built-in `Extraction`
    and CertiRocq (on its Rocq 9.1 switch) tie running code to Gallina
    terms within the trusted base that the skill `extract-verified-rocq-code`
    records, and Lean's compiled code carries no such tie. Flocq is the
    IEEE 754 model in which a floating-point statement is written.
  - A claim that lands on both axes has both artifacts, joined by an
    instance bridge: the general theorem in Lean, the certificate or
    receipt statement in Rocq, and a Rocq theorem whose comment names the
    Lean theorem by path and name and the values substituted for its
    parameters, and whose statement is the substituted proposition. Neither
    artifact replaces the other.
- A headline result is a row of `ci/headline-results.tsv` (prover, path,
  theorem, partner, tracking issue). Its rows are the theorems the "Lean
  library" table of `README.md` names, and further rows by pull request;
  the generated inventories of `rocq/delegation` are never rows. A
  headline result is proved in both provers: the same claim, read through
  each side's convention docstring. The second proof is a bridge theorem in
  a new file whose comment names the first by path and theorem name, and
  the row's `partner` names it as `PATH:NAME` (`NAME` with the modules
  that enclose it), followed by ` narrower: REASON` when the other prover
  states less (the Rocq tower is a functor over commutative rings); until
  it lands the row reads `owed` and its tracking column holds the issue
  that orders the backlog, and a row with a partner holds `-` there.
  `ci/check_headline_results.py`, which `ci/check.sh` runs, checks that
  each row names a theorem of the library, that the rows are the theorems
  the README table names, and that each partner names a theorem of a
  project-listed Rocq source. Every identifier-shaped token of a Result
  cell of that table resolves to a declaration of its module or is listed,
  with its reason, in the script's `NON_DECLARATION_TOKENS`, so a prose
  edit that adds such a token adds its entry. A new row lands with its partner. A definition that both provers
  hold lands with a comparison under `ci/` as in the item above. Any other
  claim is proved once. A result already in either tree stays where it is,
  and its translation to the other prover is a bridge in a new file, never
  an edit of a cited source.
- Each Lean row of `ci/headline-results.tsv` has a challenge module: a
  short file that restates its statement and the definitions it needs, with `sorry` as the proof, and
  a JSON configuration beside it (challenge module, solution module,
  theorem names, permitted axioms). `lake comparator --config FILE`
  checks on demand that the library theorem has that statement (measured
  on a theorem over Mathlib's quaternions: 7.4 s). Challenge modules form
  a library of their own outside `lean/GororobaMath/`, which no library
  module imports and the admission gate does not build; their `sorry`
  is the one use the rule above allows beside `lean/AuditFixture.lean`.
  A challenge module that restates a definition clashes with any module of
  the same environment that imports the solution module declaring it, so
  `lean/Challenge.lean` imports the challenge modules among which no such
  clash arises, and the `Challenge.*` glob of `lean/lakefile.toml`
  builds every module. `ci/check_headline_results.py` requires each Lean
  row to have a tracked configuration that names its theorem and solution
  module, permits exactly `propext`, `Quot.sound` and `Classical.choice`,
  and names a tracked challenge module.
- A module docstring states the convention the file fixes (the product, the
  index order, the sign) before its results, because the workspace's
  Rocq, Python and Rust code each carry one and a theorem reads on another
  repository only through it.
- State a theorem at the generality its proof has: every level `k`, every
  ring, every characteristic-zero field. A statement about `A_5` alone is the
  instance `k = 5` of a tower theorem where one exists.
- The library builds with warnings as errors (`lake build --wfail`), with
  Mathlib's standard linter set on (`lean/lakefile.toml`); its header
  linter, which checks Mathlib's copyright and authors header, is off,
  since each file here carries one SPDX line.

## Rocq sources

- A new source of `rocq/open/theories`, `rocq/open/verified`,
  `rocq/quantum` or `rocq/delegation` is listed in the `_RocqProject` of its tree in the commit
  that adds it; `ci/check_rocq.sh` fails on a tracked source the project
  file omits and on a listed source without a compiled object. A source
  anywhere else under `rocq/` is named in one of the two lists at the top
  of `ci/check_rocq.sh` (compiled by a make target of `rocq/open` or by
  the script, or held uncompiled), and the script fails on a tracked source
  neither names.
- The three trees compile their project-listed sources, and `rocq/open`
  its checkpoints, plugin fixtures and `extraction/ExtractQuaternion.v`,
  with `-w all,+default`, and so does the script's compile of
  `checkpoints/schur-geometry/NullityTwelveCoefficientCertificate.v`:
  each warning of Rocq's default set is an error and every other warning
  prints (measured, Rocq 9.3.0). Three compiles of the gate stay outside
  the comparison below: the ratchet's own calibration fixtures; the
  mutation harnesses of `rocq/open/tests`, which compile the unaltered
  law and each mutant under `-w +default` into logs of their own (a
  retained record of gororoba-open cites
  `schur_acceleration_mutations.rs` by digest, so its options keep their
  bytes, and the unaltered law is a checkpoint the gate also compiles
  under the policy); and `ci/check_kernel_replay_evidence.sh`, whose
  producer keeps the warning options of its evidence contract with
  gororoba-open. The on-demand scripts (`ci/compare_dot.sh`,
  `ci/compare_alignment.sh`, `ci/compare_signs.sh`, `ci/replay_quantum_bundles.sh`) and the
  CertiRocq targets run outside the gate.
  `ci/rocq_warning_pairs.py` reads the build logs of each tree and compares
  the (source, warning) pairs they print with `ci/rocq-warnings/allowed.tsv`,
  and `ci/rocq-warnings/causes.tsv` gives each listed warning its cause and
  the condition that removes it. The gate fails on a pair the list lacks
  and on a listed pair that no log prints: a fix removes its rows in the
  same commit. A new source adds rows only for warning names that
  `causes.tsv` already lists, so the set of tolerated names only shrinks,
  and a new name in `causes.tsv` is the owner's decision (owner,
  2026-11-16). A source that a retained record cites keeps its bytes, so
  its warnings leave the list through a successor file.
  The retained replays of gororoba-quantum keep their own `-w @all`, which
  names no warning set (measured, Rocq 9.3.0: a warning that is off by
  default stays silent under it and prints under `-w all`). No source of
  `rocq/open/theories`, `rocq/open/verified`, `rocq/quantum` or
  `rocq/delegation` holds `Admitted` or `admit` (`rocq/open/admission_check.rs`).
- `ci/check_rocq.sh` re-checks every project-listed module with the kernel
  checker (`rocq check -silent -o`) and compares the axioms it reports with
  `rocq/open/kernel-assumptions.txt`,
  `rocq/quantum/kernel-assumptions.txt` and
  `rocq/delegation/kernel-assumptions.txt` (empty).
  A change that adds or removes an
  axiom a tree rests on changes that tree's ledger in the same commit.
- Kernel replay evidence for a gororoba-open receipt comes from
  `ci/kernel_replay_evidence.py`, which compiles, kernel-checks and writes the
  evidence file and the retained logs and object into a directory outside
  the checkout that tracks the tree; gororoba-open ingests the file and never runs Rocq.
  Evidence that lists Flocq objects names its producer in `flocq_producer`, the
  manifest entry whose objects equal the copied ones, and the run is refused
  when no entry matches. A
  change to the compile or checker argument vectors, the closure order or
  the Flocq handling of the script changes the evidence contract that
  `theorem_replay.rs` of gororoba-open validates, so both land together, and
  `ci/check_kernel_replay_evidence.sh` runs before the script lands.
  Whether a source imports Flocq is decided by one rule in both
  repositories, `command_imports_flocq` here and in `theorem_replay.rs`,
  and both read `ci/flocq-import-corpus.tsv`: the calibration here, and a
  vendored copy in gororoba-open pinned by sha256 and the gororoba-math
  commit. A change to the rule changes the corpus and the pin together.
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
- `lake comparator` materializes the Mathlib dependency again and stops
  on a `packages` symbolic link (`error: already exists (error code: 17,
  file already exists)` on `lean/.lake/packages`; measured with Lean
  4.35.0 and Mathlib v4.35.0 on Linux, `docs/archive/reviews/challenge-modules/record.md`),
  so a worktree that runs it holds a `packages` directory of its own, a
  copy or a hard-linked copy of the primary checkout's.
- `git worktree remove` deletes the `lean/.lake` link and leaves the tree
  it pointed at; the tree is removed with its worktree. The build-host
  record of gororoba-infrastructure names the directories.

- The root `Makefile` builds the working tree: `make lean`, and `make rocq`,
  which copies `rocq/` into `BUILD_DIR/rocq` (default `build`, ignored)
  and compiles the three trees there with the options of their `_RocqProject`
  files. On a workstation `build` is a symbolic link to a directory
  outside the checkout, or `BUILD_DIR` names one, one per worktree; the
  targets refuse any other path inside the checkout, and `make clean`
  removes only a tree that carries the marker file `rocq-sync` wrote. A
  compile inside `rocq/` leaves objects beside the sources; git ignores
  them, and `ci/check_rocq.sh` never reads them, since it exports `HEAD`.

## Skills

The shared skills `write-lean-proofs`, `write-rocq-proofs` and
`extract-verified-rocq-code`
(`agent-config/skills/` in gororoba-infrastructure) hold the toolchain,
trust, tactic, performance, version and library references for Lean 4.35
and Rocq 9.3, and the extraction routes with their trusted bases. Load the matching one before proof work here. Each carries
`scripts/check-examples.sh`, which replays its measured rows on the
installed toolchain; run it after a toolchain bump, and send the row it
names to the gororoba-infrastructure session, since the skills land
there.

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
