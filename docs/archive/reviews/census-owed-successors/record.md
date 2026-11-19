# Review: successors of the C1468, C018 and C959 overclaim rows

Branch `rocq/census-owed-successors` of gororoba-math (issue 44), based on `census/file-local-verdicts`. Reviewers by the owner's ruling of 2026-11-18: the `codex` command-line agent (gpt-daybreak-blue, high effort, read-only, run with `--ignore-user-config` after startup hangs under the user configuration) and the Advisor, last.

## Findings and reconciliation

| Finding (codex, 8519286) | Check | Resolution |
|---|---|---|
| P3: the subject of commit 41bec82 runs onto a second line. | Confirmed. | The commit stays. It was pushed to the transfer repository before review, and the rules forbid rewriting pushed history; the merge commit carries a well-formed subject. |
| Claim 1 (C1468): justified. | The counts, the dimension-32 equivalence and the dimension-64 preservation match the header. | - |
| Claim 2 (C018): unsettled. Codex had no copy of Carlstrom's Definition 1.1. | The worker read Definition 1.1 (page 146) from the held copy of Carlstrom 2004. The model's tables and the four counterexamples are internally correct. | The header names its source, the definition and the page. |
| Claim 3 (C959): justified. | - | - |
| Claim 4 (census and project rows): justified. The census holds 395 rows with 44 overclaims; the five owed rows name their successors. | - | - |

## Validation

`sh ci/check_rocq.sh` exits 0 on a remote host at 8519286. 372 modules are kernel-checked, the axioms match the ledger (135), and 789 warning pairs are allowed. `Print Assumptions` gives closed theorems, or only the Stdlib reals axioms of `rocq/open/kernel-assumptions.txt`.

## Advisor

The final verdict is recorded at the last call before the merge.
