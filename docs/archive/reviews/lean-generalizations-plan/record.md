# Review record: dependency-ordered ledger of Lean generalizations

Pull request 73, issue 55. The owner chose `codex` on gpt-daybreak-blue and no red-team. The Advisor reviewed last.

Advisor column: "confirmed" means the Advisor read the finding, its reconciliation and the resolution as stated; "requested" means the Advisor required the change named in the row, which landed after its verdict and reaches the hosted review.

Codex read e41cf01. Its brief asked for a verdict on the pull request's stated claims, with findings by severity, and forbade builds and writes.

| # | Round | Finding | Severity | Resolution | Advisor |
|---|---|---|---|---|---|
| 1 | 1 | Row 100 drops the premise `Hbackward` that the Rocq theorem assumes | P2 | Confirmed at `rocq/open/theories/Schafer1954.v` (`schafer1954_theorem4_octonion_sedenion_identification`). Fixed in dad665a: the Lean statement keeps the premise as a hypothesis and the star clause of the Rocq derivation record; it depends on row 10 alone, effort S. | confirmed |
| 2 | 1 | Row 101 has no dependency path to `finrank = 14` | P2 | Confirmed: `derivations_spanned` gives a scalar multiple in the span and independence is a separate theorem. Fixed in dad665a: row 101 is the linear-algebra step (independent derivations and a spanning relation with a nonzero scalar give the dimension), with no dependency; the value 14 stays with the Rocq tables and is owed as an instance bridge. | confirmed |
| 3 | 1 | Rows 118 to 121 omit the instance bridge the two-axis rule requires | P3 | Confirmed; no bridge theorem exists at origin/main (the four sources hold no reference to a Lean theorem). Fixed in dad665a: each row names its Lean partner (rows 44, 43, 48, 47), the substitution, and that the bridge is owed with the partner row. The layer lists follow; a column, dependency, layer and name-resolution check of the 122 rows passes. | confirmed |
| 4 | Advisor | Rows 75, 76, 81 and 85 describe comparisons the two scripts do not make: no Python, a degree function, an open-tree spelling | - | Fixed in 1726a1a: the cells state what `ci/compare_anf.sh` and `ci/compare_assoc_phase.sh` compare and mark the open-tree part owed with its condition; `Tower.weight` and `Tower.anfDegree` move to row 77, which row 80 now depends on; a table lists the ten proved rows. | requested |

Codex rated the conventions justified, the Rocq references unsettled (rows 1 and 2) and the dependency order and the no-reading rows falsified (rows 2 and 3).
