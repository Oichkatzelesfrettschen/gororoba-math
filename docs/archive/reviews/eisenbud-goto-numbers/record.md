# Review record: gororoba-math PR 130

Head under review: 3978afe34. Reviewers chosen by the owner on 2026-11-25: codex on gpt-daybreak-blue (brief.md, codex-report.md) and agy on gemini-4-neon-medium as red team (brief-red.md, agy-neon-report.md); the Advisor runs last. Fixes after the round: e5f2aa814 and its parents on this branch.

| Finding | Reviewers | Parent check | Outcome |
|---|---|---|---|
| "for every c" overstates alternating_betti and eisenbudGoto_numbers_two (need 1 <= c; false at c = 0) | codex, agy | read the statements | docstring states the hypotheses (e5f2aa814) |
| hilbertFn docstring off by one | codex, agy | read the definition | fixed |
| degree-0 coefficient missing | agy | - | coeff_hilbertSeries_zero added |
| e8_ names unexplained, index convention unclear | codex, agy | - | documented (E8-bar -> VB quadric ring; n = 0..7 is degrees 1..8) |
| convention docstring omits the minimal-multiplicity hypotheses | agy | - | added |
| "graded depth missing" overstated: Mathlib v4.35.0 has Ideal.depth and regular sequences | agy (git grep of Mathlib) | - | list corrected |
| public import Mathlib | agy | - | replaced by eight modules, build green |
| p = 2 specialization of Proposition 1.7 and Corollary 1.11 | codex (algebra only; it could not see the paper), agy | the parent read the page images of journal pp. 100 and 104 (Eisenbud and Goto 1984) | justified on the parent's page-image reading |
| e8 instances evaluate shared definitions rather than instantiating the theorems | codex, agy | - | documented, not changed |

The Advisor ran last on 2026-11-25 over both reviewers' findings and the parent's checks.
