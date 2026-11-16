# Review: header verdicts of the census-listed theorems and their successor modules (pull request 42)

## Local reviewers

The owner chose none for this pull request.

## Advisor, on 8cbb407 and the commits before it

| Finding | Reconciliation |
|---|---|
| C010 and C1463 statements match their scope paragraphs | Confirmed; no change. |
| C1636: `sparse_correction_table` closes by `ring`, so it equates values; the count of products that `r16_sparse_correction` forms is read from its definition, and the scope paragraph exempted only the Hadamard stages | Fixed in 8cbb407: the header scope names the sparse correction as read from its definition, and the body bullet follows. |
| The title said eight successor modules | Fixed in the title. |
| The body said the hosted workflows rerun on the merged head | Fixed in the body with the run numbers of the final head. |
| The other eight successors and the TSV were unread | Read: each theorem statement matches its body bullet, and every overclaim row names a successor that the project file lists. |
| `_CoqProject` sits beside `_RocqProject` | It is deprecated, and the Makefile prefers `_RocqProject`; it is outside this change. |
| "No cited file was edited" | Confirmed on the base bytes: the sha256 values of README.md and `rocq/open/_RocqProject` at origin/main have no match in gororoba-open or gororoba-quantum. |
| Issue 40 needs its follow-up | Filed as issue 44. |

## Hosted Codex, round 1 on 8cbb407

| Finding | Severity | Reconciliation |
|---|---|---|
| The every-level non-associativity of `C956_TowerAssociatorPersistence.v` belongs in Lean (AGENTS.md, placement rule) | P1 | Fixed in 0832cb0. `lean/GororobaMath/CayleyDickson/NonAssociative.lean` proves `Tower.exists_mul_assoc_ne` over every ring with a star in which 2 is nonzero, and `Challenge/NonAssociative` restates it. The Rocq successor is removed and the census row names the Lean theorem. |
| `C1463_MatrixColumnIdeal` should be stated over every field | P1 | Refuted. The generality rule sits in the "Lean library" section, and a field-general statement goes to Lean by the placement rule. The module proves the real M(16, R) claim of the C1463 header, and its general-n lemmas are helpers. The field-general statement is item 3 of issue 44. |

## Hosted Codex, round 2 on 0832cb0

| Finding | Severity | Reconciliation |
|---|---|---|
| The README row names `Tower.mk_zero_mul_mk_zero`, which the challenge did not restate | P1 | Fixed in 6bd6a4d. `lake comparator` accepts the solution and rejects a calibration whose product reads `mk (c * a) 0`. |

## Hosted Copilot

The comment `@Copilot review` on 6bd6a4d started a Copilot agent run that changed nothing and posted no review, and a request through the requested-reviewers endpoint did not register. The round is open.

## Validation summary

`make rocq-open`, the census and `ci/check_rocq.sh` passed on an Azure build VM at 731d2b7. The hosted `rocq` and `lean` workflows passed on 8cbb407 and later heads. `lake build --wfail` and `lake comparator` (two calibrations) passed on the Windows workstation for the Lean module.
