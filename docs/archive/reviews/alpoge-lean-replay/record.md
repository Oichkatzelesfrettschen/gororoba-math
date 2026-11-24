# Review record: gororoba-math PR 101 (docs/archive/measurements/alpoge-lean-replay.md)

Owner's selection (2026-11-23): no local reviewer; red-teamer opencode on opencode-go/glm-5.3 (one attempt, report
returned); the Advisor last; then the
hosted Codex round.

## Red-team findings and dispositions (round 1, head 789f23e88)

| # | Finding | Disposition |
|---|---|---|
| 1 | "the archive's 185,000 files" has no source in the evidence repository | Fixed in 83ed499bc: "about 184,000 files (175,187 archive .olean files plus Mathlib's and its dependencies')", timing marked as running record |
| 2 | ci/check_external_kernels.sh folds every nonzero nanoda_bin status into a rejection, so "any checker status other than accept or reject maps to exit 2" is false for nanoda | Fixed in 83ed499bc (the reading names con-leche and con-ron and states the nanoda folding), after reading the script's `check` function. The script behavior itself is a defect (a nanoda crash reads as a rejection): issue #103 |
| 3 | "32 threads" contradicts "16 cores" | Fixed: "16 cores, 32 threads" (the workstation has 16 cores and 32 hardware threads) |
| 4 | "0.7 MB/s" unsourced | Fixed: marked running record, with the sourced prewarm figure (94 GB in 589 s) beside it |
| 5 | lean4export 4.33.1 label attested only by the record; the exporter is not the 4.35.0 leanexport | Accepted in part: on the workstation the exporter binary hashes to the record's 805ab4cc...; its checkout is lean4export at tag v4.33.0 (commit 15f6055e299a) with lean-toolchain set to v4.33.1, so "lean4export 4.33.1" was imprecise. Corrected in the evidence repository (175b23d) and in the note |
| 6 | "1.3 GB per GB" generalizes one checker | Fixed: nanoda 1.3, con-leche 1.1, each with its numbers |
| 7 | "about 8,000 Mathlib files" unsourced | Fixed: "about 8,600 ... (8,643 at Mathlib v4.35.0)"; recounted on the build host (8,643 Mathlib .olean files, 9,049 over all packages) |
| 8 | "117 of 123 s" rests on the running record | Fixed: the note now says so |

Claims 2 (no host names or local paths), 4 (two files use decide +kernel) and 5 (scope) held.
| 9 | The con-ron table cell implies a verdict on the closure, which con-ron never received | Fixed: the cell says it was not run on the closure and why |
| 10 | The export-gate parenthetical attributes the final-line JSON check to `ci/external_kernel_export.py` | Fixed: the stage script holds the exit and final-line checks, the Python checker the theorem and axiom checks |
| 11 | Rounding (80 vs 80.4 GB, 599 vs 599.39 s, 42 vs 42.25 s, 15,000 vs 14,965 lines) | No change: each rounds its source |
| - | The walk "repeats per module" in ci/check.sh is an inference (Advisor) | Fixed: marked as inference, with the separate one-call profile of this library (2.9 of 5.1 s) |

The pin of the evidence repository moved from a7c327c to 175b23d with the exporter correction.
