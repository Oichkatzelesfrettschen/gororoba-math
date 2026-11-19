# Review: verdicts for the file-local census candidates

Pull request 81 of gororoba-math (issue 44, item 1). Reviewers by the owner's ruling of 2026-11-18 for new pull requests: the `codex` command-line agent (gpt-daybreak-blue, high effort, read-only) and the Advisor, last; no hosted review round.

## Brief

Codex read head b6d889d. It checked four claims: the verdicts follow the README criterion (it sampled 81 of the 228 rows marked `statement is the claim`, and read all five overclaim rows); each location points at its declaration; the C010 and citation rows are accurate; the counts agree.

## Findings and reconciliation

| Finding (codex, b6d889d) | Check against the source | Resolution |
|---|---|---|
| P1: the 13 C1469 rows miss an overclaim. The header says the checks establish the architecture "at all CD levels"; the statements cover dimensions 16 to 256. | Confirmed. `C1469_TowerTrilinearity.v` lines 7 to 10 make that claim, and the README criterion classes an unmentioned every-dimension quantifier as an overclaim. | Fixed in 93051fe. The 13 rows read `header overclaims` and name `Tower.negSign_zero_right`, `Tower.negSign_zero_left`, `Tower.e_mul_self` and `Tower.e_mul_e_anticomm` of `lean/GororobaMath/CayleyDickson/Tower.lean`, which state these laws at every level. The README counts read 215 and 18, 44 overclaims, in 18 files. |
| P2: four locations point at `Example`, not at `Theorem` or `Lemma`. | Confirmed. `C1636_ScheduleProgramCount.v` lines 264 to 274; `ci/theorem_census.py` accepts `Example` as a declaration keyword. | The rows stand. The brief's wording was too narrow, and the PR body names the census keywords. |
| P3: the Crossref and zbMATH evidence of the Brown correction cannot be reproduced from the repository. | Confirmed: the evidence was read from the indexes on 2026-11-19 and is not retained. | Narrowed in 93051fe. The cell leads with the in-tree corroboration (`BrownGeneralizedCD.v` cites the Pacific J. Math. paper) and dates the two index reads. |
| Claims 3 and 4 | Codex found the C010 rows correct and the counts consistent before the P1 fix. | Recounted after the fix: 44 overclaim rows, in 18 files. |

## Advisor

The Advisor read 93051fe and confirmed every finding and its resolution:
- P1: confirmed against header lines 7 to 10. The 13 rewritten rows, their Lean names and the recount (215 and 18; 44 rows in 18 files) are right, and no census rerun is needed, because only cells of existing rows changed.
- P2: confirmed; the rows stand.
- P3: confirmed, and the narrowing is enough. The index reads come from the issue 57 intake.
- Claims 3 and 4: justified after the recount.

It required two further steps. The PR body now carries the new counts, the sample and the census keywords. The digests of C018, C959, C1468 and C1469 each appear in a retained record of gororoba-open (`data/output/audit/vacuum-composition/proof-source-SHA256SUMS`; C1469 also in `data/output/audit/boolean-permutation-evidence/provenance-port.txt`), so the README's statement that these files keep their bytes holds.
