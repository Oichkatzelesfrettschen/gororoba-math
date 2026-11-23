# Review record: gororoba-math PR 101 (docs/archive/measurements/alpoge-lean-replay.md)

Owner's selection (2026-11-23): no local reviewer; red-teamer opencode on opencode-go/glm-5.3 (one attempt, report
returned; allowance warning at or above 60 percent of the five-hour and weekly windows); the Advisor last; then the
hosted Codex round.

## Red-team findings and dispositions (round 1, head 789f23e88)

| # | Finding | Disposition |
|---|---|---|
| 1 | "the archive's 185,000 files" has no source in the evidence repository | Fixed in 83ed499bc: "about 184,000 files (175,187 archive .olean files plus Mathlib's and its dependencies')", timing marked as running record |
| 2 | ci/check_external_kernels.sh folds every nonzero nanoda_bin status into a rejection, so "any checker status other than accept or reject maps to exit 2" is false for nanoda | Fixed in 83ed499bc (the reading names con-leche and con-ron and states the nanoda folding). The script behavior itself is a defect (a nanoda crash reads as a rejection) and stays open as a separate change |
| 3 | "32 threads" contradicts "16 cores" | Fixed: "16 cores, 32 threads" (the workstation has 16 cores and 32 hardware threads) |
| 4 | "0.7 MB/s" unsourced | Fixed: marked running record, with the sourced prewarm figure (94 GB in 589 s) beside it |
| 5 | lean4export 4.33.1 label attested only by the record; the exporter is not the 4.35.0 leanexport | Refuted as an error: the exporter was built from lean4export at 4.33.1 for the archive's toolchain (sha256 805ab4cc..., the record's digest); the reviewer's own computation confirms it is not 4.35.0's. Kept |
| 6 | "1.3 GB per GB" generalizes one checker | Fixed: nanoda 1.3, con-leche 1.1, each with its numbers |
| 7 | "about 8,000 Mathlib files" unsourced | Fixed: "about 8,600 ... (8,643 at Mathlib v4.35.0)", the reviewer's count |
| 8 | "117 of 123 s" rests on the running record | Fixed: the note now says so |

Claims 2 (no host names or local paths), 4 (two files use decide +kernel) and 5 (scope) held.
