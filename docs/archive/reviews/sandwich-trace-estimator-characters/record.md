# Review record: sandwich trace, estimator in a character basis, two-term scalar kernel (pull request 95)

Brief: `brief.md` beside this file. Both local seats read commit f3bb5ed0a. Reviewer: the `codex` command-line agent on gpt-daybreak-blue at high effort. Red-teamer: `opencode` on opencode-go/beam-free, on the red-team paragraph of the brief. The Advisor reviewed last with every finding and its resolution. The fixes are in 78af42c58 and in the commit that files this record.

| Finding | Seats | Check | Resolution |
|---|---|---|---|
| `KernelMap.coeff` and `KernelMap.walshChar` mirror `coefficients` and `walsh_matrix` of `nhat_spectral.py` of gororoba-quantum, so they owe a named source and a comparison that rejects a mutated reference | opencode (P1), codex (P2) | Confirmed against `AGENTS.md` ("Statements and proofs") | Fixed: the docstrings name the functions, and `ci/compare_walsh.sh` compares 64 character values and 32 coefficients as exact fractions and rejects a reference with one negated entry (measured: agreement at gororoba-quantum 05f99ece3) |
| The zero reading and the spectral form hold at `vHat = 0` only by `x / 0 = 0`, where the source estimator is undefined | codex (P2), opencode (P2) | Confirmed against `nhat_bias.py` | Fixed: both docstrings and the note of A5-238 say that the identities are readings of the estimator for `vHat != 0`; the statements keep their generality as algebraic identities |
| Row A5-467 stays `owed` although `Matrix.skew_mul_mul_skew` proves its expansion | codex (P2) | Confirmed | Fixed: the row reads `partial` with the theorem named and its open clauses listed; the tally reads 347 rocq owed, 5 rocq partial |
| The order context of `TwoTermScalar` is one route to anisotropy | codex (P3) | Confirmed | Fixed: `Tower.sub_one_mul_dot_self_eq_zero_of_e_add_smul_e_mul_eq_zero` holds over every commutative ring with the identity as star, and `Tower.eq_zero_of_e_add_smul_e_mul_eq_zero_of_anisotropic` takes a non-zero-divisor and an anisotropic trace form; the ordered statement is its corollary |
| `hD` is droppable from `Matrix.trace_mul_skew_mul_skew_eq_zero_iff` | codex (P3) | True of the mathematics; the proof as written applies the symmetric trace lemma | Boundary: the hypothesis stays, since the proof uses it; a proof from `hd` alone is a later refinement |
| `[CharZero K]` is stronger than most of `EstimatorWalsh` needs; `[DecidableEq A]` could be local | codex (P3), opencode (P2) | True | Boundary: the module keeps the context of `KernelMap/Estimator.lean`; `DecidableEq A` is in the statement of the orthogonality hypothesis |

Survived both seats: the signs and index order of the expansion and trace identity against rows A5-467 and A5-470; the hypothesis `hl` of the equivalence is needed and satisfiable; no counterexample to the scalar kernel theorem at `i = j`, `i = 0` or `t = 0`; the Lean tally of the findings rows.

Both seats proposed a closure of the counts of row A5-262, recorded as a hypothesis: with `Z k` the number of ordered pairs of nonzero distinct indices of aligned-pair count 0, `Z (k + 1) = 2 Z k + 6 (2^k - 1)` and the multiplicity of the maximum `2^k - 4` at level `k + 1` equal to `2 Z k`, from `Tower.alignedPairCount_succ_cases`, with base `Z 3 = 42`.

## Advisor

The Advisor agreed with every row above, the three boundary rows and the reading of the `vHat = 0` identities as algebraic statements included. It required the root build as evidence that the helper lemmas declared in namespace `Matrix` clash with no Mathlib name, which the hosted `lean` workflow gives on f3bb5ed0a and on the final head. On its item, `KernelMap.nHat_eq_zero_of_expansion_coeff_zero` states the zero reading at the generality of its proof (`gamma a0 = 0`), and the channel form is its corollary.
