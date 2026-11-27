# Review record: complex form of the nullity of a doubly pure element (pull request 140)

Branch lean/cz-bordered-kernel. Heads: 7e41d9991 under local review, 2c15e5fe0 after the fixes.

## Reviewers (owner's selection, 2026-11-26)
- agy gemini-4-neon-medium, red team; opencode on opencode-go/hy4-flash-free (free model); the Advisor last.

## Findings and resolutions
| Finding | Reviewer | Class | Resolution |
|---|---|---|---|
| The A5-356 note said Theorem 1 (every zero divisor doubly pure) stays open; re_halves_eq_zero_of_mk_mul_eq_zero (ScaledPairAnnihilator.lean:92) proves it | agy | read from source | Fixed in 2c15e5fe0: doublyPure_of_mk_mul_eq_zero, zeroDivisor_doublyPure_nullity_level_five; the row moves to proved |
| Sign convention z = p - i q against A5-356's p + i q, no lemma relating the ranks | agy, opencode | read from source | Fixed in 2c15e5fe0: czComplexPlus, rank_czComplexPlus; the module docstring names the flip |
| repr_zero_mk cited for coordinate 2^k, which it does not prove | agy, opencode | read from source | Fixed in 2c15e5fe0: repr_mk_inr, toNat_cons_true_zero |
| repr_e_mul_zero docstring required purity the theorem does not use | agy | read from source | Fixed in 2c15e5fe0 |
| "over the reals and complex numbers" overstates the generality | opencode | read from source | Fixed in 2c15e5fe0: "in the real tower with complex matrices" |
| k = 0 vacuity of three level-indexed theorems | agy | read from source | Note: non-vacuous from k = 1; recorded in the pull-request body |
| Conjecture: the nullity and rank identities hold over every ordered field with its quadratic extension K[i] | agy | hypothesis | Open item |
| Placement: the row stayed rocq ("decided by evaluation: Rocq") with Lean entries only | worker, Advisor | read from source | Resolved by the guide's statement axis: a fixed-dimension statement that instances a Lean every-level theorem stays beside it; the row reads lean, "Fixed algebra instancing a Lean theorem: stays beside it" (as rows 247 and 248), and the tally reads 1 lean, proved and 2 rocq, proved |
| No Rocq partner holds DoublyPure, czComplex or czComplexPlus (the doubly-pure files of rocq/open concern Moreno's unit-norm octonion statements under other definitions) | parent | read from source | No cross-prover comparison owed |

## Validation on 2c15e5fe0
- lake build --wfail exit 0 on the workstation (Lean 4.35.0, Mathlib v4.35.0); axioms propext, Classical.choice, Quot.sound; leanchecker replay exit 0. ci/check_claims_ledger.py runs in the hosted quick tier.
