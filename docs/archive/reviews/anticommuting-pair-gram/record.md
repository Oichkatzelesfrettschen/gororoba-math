# Review record: Gram identity and kernel of an anticommuting skew pair (pull request 138)

Branch lean/anticommuting-pair-gram. Heads: c0da8c9c3 under local review, 5b180cb47 after the fixes; the commit that adds this record also corrects the pair counts of the module docstring against row A5-629 (63, 171 and 435 pairs in all at dimensions 16, 32 and 64).

## Reviewers (owner's selection, 2026-11-26)
- agy gemini-4-neon-medium, red team, read-only on c0da8c9c3: no blocker; three fixes, two notes, one conjecture.
- The Advisor last.

## Findings and resolutions
| Finding | Class | Resolution |
|---|---|---|
| Module docstring called the file "the content of" row A5-629; the row also states the traceless Hermitian involution, the complement law, the A_5 slice kernel and the half-dimension kernel | read from source | Fixed in 5b180cb47: the docstring lists every unproved part of A5-629 |
| genMat_mulVec_eq_zero_iff grouped under i ≠ j, but it holds for all i, j | read from source | Fixed in 5b180cb47 |
| gram_eq docstring said "diagonal" and "off it" for the same-factor and cross terms | read from source | Fixed in 5b180cb47 |
| Five theorems lacked a one-sentence mechanism | read from source | Fixed in 5b180cb47 |
| Hypotheses minimal and satisfiable; no hidden convention | read from source | Note, no change |
| Conjecture: with 2 a unit, H = ι A B is an involution anticommuting with A, so A maps ker(A + ιB) onto ker(A - ιB) and 2 dim ker = n over a field of characteristic other than 2 | hypothesis | Open item: the half-dimension statement of A5-629, recorded in the module docstring as unproved |

## Validation on 5b180cb47
- lake build --wfail of the module: exit 0 (workstation, Lean 4.35.0, Mathlib v4.35.0); axioms propext, Classical.choice, Quot.sound; leanchecker replay exit 0.
