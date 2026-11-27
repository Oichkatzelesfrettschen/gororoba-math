# Review record: rank of block-diagonal, Kronecker and graded block matrices (pull request 142)

Branch lean/block-rank. Heads: 96cd03e80 under local review, 53c9c26a1 after the fixes.

## Reviewers (owner's selection, 2026-11-27)
- agy gemini-4-neon-medium, red team; the Advisor last.

## Findings and resolutions
| Finding | Class | Resolution |
|---|---|---|
| Apache-2.0 section 4(b): the ported and modified lemmas carry no notice of modification | read from source (math/LICENSE) | Fixed in 53c9c26a1: the module docstring names the two source files, the changes (namespace Matrix, Finite rows) and the date |
| Non-terminal simp in rank_fromBlocks_diagonal | read from source | Fixed in 53c9c26a1: two simp only lists from simp? |
| Redundant finiteness hypotheses | read from source | Fixed in 53c9c26a1: Module.Finite K (ψ k) dropped from finrank_range_piMap, Finite (m' k) from rank_blockDiagonal', Finite m from rank_eq_sum_rank_gradedBlock; rank_kronecker keeps Finite m and Finite p, which Pi.basisFun needs |
| Docstrings: finrank_range_piMap missing from Main results, D for B, mechanisms, "characters" | read from source | Fixed in 53c9c26a1 |
| rank_eq_sum_rank_gradedBlock applies to a 16-value grading with an empty class (a 0 x k block has rank 0) | read from source | Note, no change |
| Conjecture: for a poset grading (block triangular A), the sum of the diagonal block ranks is at most rank A | hypothesis | Open item |

## Validation on 53c9c26a1
- lake build --wfail exit 0 on the workstation (Lean 4.35.0, Mathlib v4.35.0); axioms propext, Classical.choice, Quot.sound for all five theorems; leanchecker replay exit 0.
