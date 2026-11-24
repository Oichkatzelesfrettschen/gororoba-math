# Review record: right Bol identity (pull request 106)

Brief: `brief-redteam.md` beside this file. The round read commit 4ac802b0d. The owner chose no local reviewer and one red team: `opencode` on opencode-go/glm-5.3 (exit 0), read-only, with git and grep only. The Advisor ran last.

| Finding | Seat | Check | Resolution |
|---|---|---|---|
| The clause "L/R symmetric violations that grow with dimension" of C-119 is read as a measurement; read as mathematics, the row is `partial` | opencode (P3, hypothesis) | True as a reading: no declaration states a symmetry or a growth | Boundary: the note of the row names both sentences as measurements, the reading that `ci/claims/README.md` ("Rules") gives a sentence that reports the size of observed violations; the row before this change carried the same reading |

Survived: the two statements are the right and left Bol identities up to renaming; `rw [flexible_of_le_three hk x y]` matches only the right side and the goal is `moufang_right_of_le_three hk z x y`; with `y = 1` the identity is right alternativity, which `exists_right_alternative_ne` refutes; the hypotheses equal those of the left partners; levels `k <= 3` and `k >= 4` are dimension 8 and below and 16 and above; the reals satisfy both hypothesis sets; subject, body wrap and line lengths.

## Advisor

The Advisor confirmed the boundary and returned one finding: the row C-119 moved from `partial` to `proved`, and `ci/claims/expected_sources.py` rejects a `proved` row whose registry claim is Refuted, Superseded or Closed, a check that no hosted workflow runs. Checked: the script, run on this branch against gororoba-open 3c04c2eb, reports 1287 listed sources matching and exits 0. No file changed.
