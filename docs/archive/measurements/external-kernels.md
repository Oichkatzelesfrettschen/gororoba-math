# External kernels for the Lean library

Measured 2026-11-20 on the Windows compute workstation (WSL, 32 threads, 54 GB).

## Bundled checkers

The Lean 4.35.0 toolchain ships external checkers in its `bin` directory, beside `lean` and `leanchecker`:
- `leanexport`, which writes named declarations and their dependency closure in NDJSON format 3.1.0;
- `con-leche`, a checker written in Lean. By its `--help`, its `--verified` mode is the one its main theorem covers: no file that declares a theorem of type `False` is accepted (`ConLeche.no_False_declaration`, `ConLeche/MainTheorem.lean`);
- `con-ron`, a Rust arena checker with the same command line and exit codes. By its `--help`, the same statements are proved about its pipeline on an Aeneas model of the Rust, using only `propext`, `Classical.choice` and `Quot.sound`. They still assume, as hypotheses, that the driver runs the extracted stages in the order it does on the file's bytes (its `OVERVIEW.md`, section 3.1);
- `nanoda_bin` 0.4.19, a type checker for Lean written independently in Rust;
- `lean4lean` and `leanchecker-paranoid`.

The 4.33.1 toolchain ships none of them. `ci/check_external_kernels.sh` uses `leanexport`, `con-leche`, `con-ron` and `nanoda_bin` from the toolchain of `lean/lean-toolchain`. They match its Lean version, and the script needs no separate build.

## Calibration

The bad inputs are exports of exactly `ReplayFixture.bogus` and its dependencies, a 36-line file. That declaration has type `False` and value `True.intro`, and was added with `debug.skipKernelTC`. The 4.35.0 checkers also read the exports of lean4export 4.33.1.

| Export | con-leche --verified | con-ron --verified |
|---|---|---|
| 4.35.0 `ReplayFixture.bogus` | status 1: `invalid: type mismatch in theorem ReplayFixture.bogus [at theorem ReplayFixture.bogus, fold position 12]` | status 1: `rejected: type mismatch in theorem [at theorem ReplayFixture.bogus, fold position 12]` |
| 4.33.1 fixture, the same declaration | status 1, the same message | status 1, the same message |
| 4.33.1 fixture, a theorem of type `True` | status 0: `accepted 3 declarations` | status 0: `accepted 3 declarations` |

`ci/external_kernel_export.py` adds three checks: each requested theorem is declared as a theorem in the export, the export declares no axiom outside the allow list, and it declares something.

On the export of `AuditFixture.usesDeclaredAxiom`, which rests on the declared `AuditFixture.declaredAxiom`, the four refusals differ:
- the export check exits 1, naming the axiom;
- con-leche exits 2: `not implemented yet: non-standard axiom (AuditFixture.declaredAxiom)`;
- con-ron exits 2: `declined: non-standard axiom`;
- nanoda exits 1: `export file declares unpermitted axiom`.

The axiom rule therefore rests on the export check rather than on any one checker, and the calibration requires that refusal.

On a real 4.33.1 closure, lean4export 4.33.1 exported `GroundTheory.Automorphic.contDiff_integral_of_iteratedFDeriv` of the alpo.ge archive in 64 s at 6.5 GB peak: 4,053,366 lines, 219 MB, 36,631 declarations, with the three standard axioms. All four checkers accepted it:

| Checker | Wall time | Peak memory |
|---|---|---|
| con-leche --verified | 14.6 s | 0.30 GB |
| con-ron --verified | 11.5 s | 0.58 GB |
| bundled nanoda_bin | 10.8 s | 0.33 GB |
| nanoda master | 14.9 s | 0.35 GB |

## Run over the headline theorems

At 91c7746, `ci/check_external_kernels.sh` passed calibration, and con-leche, con-ron and nanoda accepted all 108 Lean rows of `ci/headline-results.tsv` (33 solution modules). Each export declares exactly the three standard axioms.


At gororoba-math b00bb43 (pull request 89's head), nanoda (built from its master branch, commit 0da9f98f) accepted all 110 Lean rows of `ci/headline-results.tsv`. The rows fall in 34 solution modules. The exports came from lean4export v4.35.0, and only the three standard axioms were permitted. The closures ran from 26,034 export lines (`CayleyDickson.Basic`) to 3,207,192 (`CayleyDickson.HalfFold`).

## Upstream builds

Earlier the same day, before the bundled checkers were found, the tools were built from upstream:
- **nanoda v0.3.2:** it rejects the configuration key `stack_size_bytes`, and its help names an older lean4export fork as its format, so its master commit was used.
- **lean4lean master 67f63b0:** its toolchain is v4.33.0-rc2. It builds on 4.33.1, rejects the bogus fixture with `(kernel) declaration type mismatch`, and accepts archive modules in 22 to 30 s each. Moved to 4.35.0 it fails to build: `Lean.reduceBool` and `Lean.reduceNat` are gone from core, and its primitive check rejects 4.35's `Nat.div`. The toolchain's bundled `lean4lean` is the 4.35 build.

A first calibration on whole-module exports misled, which is why the script exports only named theorems and reads each checker's own verdict line:
- nanoda v0.3.2 "rejected" the bad fixture because of its configuration error.
- lean4lean printed a pretty-printer panic before its kernel error.
- The good fixture failed in nanoda because `Lean.reduceBool`, exported with all of `Init`, depends on the axiom `Lean.trustCompiler`.
