# Kernel replay of the alpo.ge Lean archive

Measured 2026-11-20 to 2026-11-23 on the Windows compute workstation (WSL, 16 cores, 32 threads, 54 GB) and four Google Cloud
VMs (n2d-highmem-16, two c2d-highmem-16, c2d-highmem-8), with one c2d-highmem-32 (251 GiB) for the closure export.
The full record, each host's result files, the replay driver and the calibrated verifier are public in
[gororoba-alpoge-replay](https://github.com/Oichkatzelesfrettschen/gororoba-alpoge-replay), commit a7c327c, file
`CERTIFICATION.md`. The archive itself is Levent Alpöge's work, published at https://alpo.ge/ with a note stating a
proof of the Riemann hypothesis; it carries no license, and this repository holds none of it.

## Subject

`lean.tar.gz`, the concatenation of `https://alpo.ge/lean.tar.gz.part01..14`, sha256
9631b4f020199e580ba86178cb56c6e9b09f690c2369a80dc4334aa93f49c7fc: 175,187 modules on Lean 4.33.1 and Mathlib
0df444a360eaa60ab8c11dca51a86af692955474, and five theorems in `Main.lean` that state Mathlib's `RiemannHypothesis`,
its zeros-on-the-line form, and three Dirichlet L-function forms.

## Results

| Check | Method | Result |
|---|---|---|
| Build | `lake build`, 12 jobs | "Build completed successfully (183903 jobs)" |
| Statements | each theorem's type equals its standard form by `Iff.rfl`; `#print axioms` | the five use Mathlib's own `riemannZeta`, `DirichletCharacter.LFunction` and `RiemannHypothesis`; axioms propext, Classical.choice, Quot.sound |
| Kernel replay | Lean 4.33.1's `replayFromImports` on every module, through `leanchecker` and then a driver that calls the function directly; calibrated on `ReplayFixture.bogus` and on agreement with `leanchecker` | 175,187 of 175,187 modules pass on some host; no kernel rejection; the compiled .olean files hash identically on all five hosts |
| Independent kernels | lean4export 4.33.1 of the five theorems' dependency closure (61,571,290,481 bytes, 1,460,445 declarations, axioms propext, Classical.choice, Quot.sound), checked with the Lean 4.35.0 toolchain's checkers after calibration on the same host | `nanoda_bin` (strict, three axioms) accepts, 3,420.6 s, 80 GB peak; `con-leche --verified` stops without a verdict (exit 3, below); `con-ron --verified` declines inputs of this size (exit 2, below) |

What a pass establishes: the five theorems follow, in Lean's logic with the three standard axioms, from Mathlib's
definitions at the pinned commit, by Lean's kernel and by an independently written kernel. It rests on those kernels,
on lean4export, and on Mathlib's definitions meaning what the statements say. It is not a mathematical review.

## Readings for this repository's checks

- **`leanchecker` per module walks the whole search path.** Each call resolves its argument as a module-name prefix by
  listing every .olean on the search path before it replays anything: 117 of 123 s per module on the archive's
  search path of about 184,000 files (175,187 archive .olean files plus Mathlib's and its dependencies'; timing from
  the replay's running record, `CERTIFICATION.md` of the evidence repository). `ci/check.sh` makes one `leanchecker` call per module over about 8,600 Mathlib .olean files (8,643 at
  Mathlib v4.35.0), so the same
  walk repeats per module there; a driver that calls `replayFromImports` on the named module removes it.
- **`con-leche` has a fixed normalization budget.** It exits 3 ("internal error: fuel exhausted: whnf loop") on a
  theorem proved by `decide +kernel` over a 131,070-step evaluation, in 2.6 s on that theorem's 15,000-line closure,
  in both `--verified` and `--trusted` mode; `nanoda_bin` accepts the same closure in 42 s. Its `--help` offers no
  option to raise the budget. `ci/check_external_kernels.sh` maps a `con-leche` or `con-ron` status other than accept
  or reject to its exit 2 ("a checker failed to run"), so a headline theorem whose closure holds a large
  `decide +kernel` proof would stop that script there rather than fail it; it folds every nonzero `nanoda_bin` status,
  a crash included, into a rejection (exit 1); two library files use `decide +kernel`
  (`CayleyDickson/AlignedPairEndpoints.lean`, `Clifford/ZeroEight.lean`).
- **`con-ron` addresses terms with 32-bit handles.** On a 13.3 GB export (867,348 declarations) it declines with exit 2,
  "arena: expr constructor at capacity", where `con-leche` accepts in 599 s at 14.6 GB.
- **Calibration exports must be dependency closures.** A whole-environment export declares `sorryAx` and
  `Lean.trustCompiler`, so a strict `nanoda_bin` configuration refuses it at the axiom gate before any type check;
  closure exports of `ReplayFixture.bogus` (rejected at the type check, exit 101) and of a good theorem calibrate it.
- **Both `nanoda_bin` and `con-leche` exit 0 on an empty export.** An export gate (exporter exit 0, a final line that
  parses as JSON, the requested theorems declared, as `ci/external_kernel_export.py` checks) has to precede a verdict.
- **Memory.** lean4export of the closure peaked at 162.5 GB resident (69.7 GB private plus the mapped .olean files);
  `nanoda_bin` needed 1.3 GB per GB of export (80.4 GB on 61.6 GB) and `con-leche` 1.1 (14.6 GB on 13.3 GB). A cold page cache on a standard persistent disk held the export at
  one faulting thread (about 0.7 MB/s, running record) until 64 parallel readers prewarmed every file the import maps
  (94 GB in 589 s).
