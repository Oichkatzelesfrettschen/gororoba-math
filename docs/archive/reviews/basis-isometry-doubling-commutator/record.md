# Review record: basis-unit isometry, doubling commutator and estimator readings (pull request 93)

Brief: `brief.md` beside this file. All local seats read commit d49f4e468. Reviewers: the `codex` command-line agent on gpt-daybreak-blue at high effort and `agy` on gemini-4-hydrogen-high. Red-teamers: `agy` on gemini-4-neon-high and `agy` on gemini-3.8-flash-high, each on the red-team paragraph of the brief. The Advisor reviewed last, at e2d5feded, with every finding and its resolution. The fixes are in e2d5feded and in the commit that files this record.

| Finding | Seats | Check | Resolution |
|---|---|---|---|
| `Tower.dot_mul_dot_eq_of_mul_eq_mul_polar` carries a droppable hypothesis `IsLeftRegular (2 : R)` | Hydrogen (P2), Neon (P2); Flash stated that it cannot be dropped | Confirmed: at levels up to 3, `dot (x * a) (y * a) = dot x y * dot a a` and its mirror follow from `Tower.dot_mul_adjoint` with `Tower.mul_mul_star_of_le_three` and `Tower.star_mul_mul_of_le_three`; the proof without the hypothesis builds and replays, which refutes the Flash statement | Fixed in e2d5feded: `Tower.dot_mul_mul_right_of_le_three`, `Tower.dot_mul_mul_left_of_le_three`, and the quadratic identity as the diagonal of the polarized one |
| Row A5-228 is overstated as `proved` | codex (P2), Neon (P2) | Confirmed: no declaration links the nullity of an 8-bin coset block to its aligned-pair count `N_b`, and the source sentence on exactness carries no qualifier for a block with an empty class | Fixed in e2d5feded: the row reads `partial` and its note names both |
| The notes of A5-229 and A5-472 omit open links | Hydrogen (P3), Neon (P2), codex (P3) | Confirmed against the source rows | Fixed in e2d5feded: A5-229 names the unstated link from `N_b` below 4 to a bin in each class; A5-472 names the absent definition of `K(z)` and of the forms `N1` and `N2 + N3` |
| `ci/claims/README.md` gives a stale tally of the findings rows | Hydrogen (P3) | Confirmed by count | Fixed in e2d5feded: 14 lean owed, 5 lean partial |
| Docstrings: "is not multiplicative from level 4 on" is false over the zero ring; the herald probability of A5-371 is called a device statement; the reading of `N1` omits that `a` and `c` are pure | codex (P3), Neon (P3), Hydrogen (P3) | Confirmed | Fixed in e2d5feded |
| `BasisIsometry.lean` lacks the left companion of `Tower.dot_mul_e_self` | Flash (P3) | A convenience, not a defect | Added in e2d5feded: `Tower.dot_e_mul_self` |
| `[CharZero K]` is stronger than three lemmas of `EstimatorReadings.lean` need | Neon (P3), codex (P3, hypothesis) | True: characteristic other than 2 suffices for the scale identities | Boundary: the module keeps the context of `KernelMap/Estimator.lean`, whose statements it reads; a weaker context is a change to both modules |

Claims 1, 2, 3, 5 and 6 of the brief survived every seat: the statements match rows A5-371, A5-472, A5-228 and A5-229 under the product convention of `CayleyDickson/Basic.lean`, no headline row or challenge module is owed, and `TrivialStar` and the bound `k <= 3` are needed (counterexamples over the complex numbers with conjugation and at level 4 in the Neon and Hydrogen reports).

The seats proposed statements for the rows still owed, recorded here as hypotheses: the determinant `1 - s t^2` of each XOR-pair block of `L_(e_i + t e_j)` for row A5-177, the Walsh form of the estimator for A5-238, the recursion `Z(k + 1) = 2 Z(k) + 3 (2^k - 1)` with `M(k + 1) = 2 Z(k)` for the counts of A5-262, and the trace identity of A5-470 over every commutative ring.

## Advisor

The Advisor agreed with every resolution above, the `partial` reading of A5-228 and the `CharZero` boundary included. It asked for three corrections, applied in the commit that files this record: the note of A5-228 says that the source sentence carries no qualifier for an empty class, since the class mean is undefined there in the source; the pull-request body states the final ledger statuses and reports the local `ci/check.sh` run as not completed; and this record and its brief carry repository-relative paths only.
