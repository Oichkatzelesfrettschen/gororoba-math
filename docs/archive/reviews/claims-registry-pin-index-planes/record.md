# Review record: registry pin at the sedenion index-plane supersessions (pull request 102)

Brief: `brief-redteam.md` beside this file. The round read commit 01ae7fccf. The owner chose no local reviewer and one red team: `opencode` on opencode-go/glm-5.3 (the first model of the attempts list; exit 0), read-only, with git and grep only. The Advisor ran last.

| Finding | Seat | Check | Resolution |
|---|---|---|---|
| The C-1792 row reads `proved` for a statement about the 16D (sedenions), and `basis_units_alternate` decides the two alternative laws on the integer tower; the row leaves out the theorem that carries a decision to the real tower | opencode (P2) | Confirmed: `associates_at` is defined on `tz_mul`, and `associates_at_tower` states that `associates_at n a b c = true` holds exactly when the three units associate under `tower_mul` | Fixed: the row lists `associates_at_tower` and its note names it |
| The note of row C-581 cites `C029_octonion_subalgebra_iff` for the pairs that violate left alternativity; that theorem states an isomorphism with the octonions | opencode (P3) | Confirmed | Fixed: the note cites `not_left_alt_9` to `not_left_alt_15` |
| The reason of row C-1469, "one line, not 3", depends on a reading: two octets share one quaternion index set and its 3 nonzero units | opencode (P3) | True; the source map of gororoba-open records the same reading, and the count 3 that survives is the number of octets through a line | Boundary: the note says "share one line" in the terms of `plane_line_incidence`; unchanged |
| `docs/archive/reviews/claims-ledger/record.md` says 500 claims among 1597 | opencode (P3) | True | Refuted as a defect: a review record keeps the counts of its commit |

Survived: `proved` for C-1787, C-1789 and C-1793, each clause read against a listed declaration, with the ring hypotheses of the three Lean theorems; `partial` for C-1794 with the formula evaluation as its one open clause; the clause, placement and successor of the four Superseded rows; the quantifier and clause of each new row; the exclusion of C-1785, C-1786, C-1788, C-1790 and C-1791, whose predecessors C-871, C-029, C-1130, C-1233 and C-1236 the ledger does not hold; the counts 1607, 505 and 194.

## Advisor

The Advisor confirmed the four resolutions and returned one finding of the first finding's kind: `not_left_alt_N` states the inequality for two elements `emb tabN (...)` and no listed declaration states that they lie in the span `in_sub N`, which the statements of C-1787 and C-1792 assert. Confirmed: `emb_in_sub_N` states the membership. Fixed: both rows list `emb_in_sub_9` to `emb_in_sub_15`.
