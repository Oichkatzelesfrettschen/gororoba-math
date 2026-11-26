# Review record: A_5 Stiefel zero divisors over fields with a square root of -1 (pull request 139)

Branch lean/stiefel-transport. Heads: d69e83b09 under local review, b7f1115f5 after the fixes.

## Reviewers (owner's selection, 2026-11-26)
- agy gemini-4-neon-medium, red team, read-only on d69e83b09: no blocker; four fixes, two notes, one conjecture.
- opencode on opencode-go/hy4-flash-free (the free model the owner named), read-only: no blocker; one fix, five notes, one structural statement falsified by the reviewer.
- The Advisor last.

## Findings and resolutions
| Finding | Reviewer | Class | Resolution |
|---|---|---|---|
| Three non-terminal simp calls before ring in phi_coord | agy | read from source | Fixed in b7f1115f5: the simp only lists that simp? printed |
| Four decide +kernel lemmas without their measured cost | agy | read from source | Fixed in b7f1115f5: 0.66 to 0.68 s each (profiler, Lean 4.35.0), a fixed overhead |
| Dead have/simp only in stiefel_zero_divisor | agy | read from source | Fixed in b7f1115f5; the proof builds without it |
| phi_mk without a docstring; stiefel_zero_divisor without its mechanism | agy | read from source | Fixed in b7f1115f5 |
| phi_mul_mk's docstring states φ(mk p q * mk r s) but the theorem is the expanded right side; phi is defined later | opencode | read from source | Fixed in b7f1115f5: the docstring names the chain Tower.mk_mul_mk and phi_mk |
| The Lean and Rocq theorems agree in hypotheses and in the side x multiplies; the Rocq one is constructive (eq_dec) | both | read from source | Note, no change |
| TrivialStar K excludes Mathlib's ℂ (star is conjugation), so the real corollary needs a trivial-star type synonym | both | hypothesis | Open item for issue 99 step 5 (real statement) |
| Conjecture: Q(z) divides Pf(borderedBV_k z w) for every k >= 3, extending the theorem to Tower K (k + 1) | agy | hypothesis | Open item; falsifier: a pure Stiefel pair at k = 5 over F_5 with det borderedBV_5 z w nonzero |
| Purity of p is essential: for y = mk 1 e_1, L_y is invertible when 2 != 0 (L_e^2 = -1 for a basis unit), so y has no nonzero annihilator at level 5 | opencode | read from source | Note: the statement keeps re p = re q = 0 |

## Validation on b7f1115f5
- lake build --wfail of PureDoublingTransport and StiefelZeroDivisor: exit 0 (workstation, Lean 4.35.0, Mathlib v4.35.0); axioms within propext, Classical.choice, Quot.sound; leanchecker replay exit 0.
