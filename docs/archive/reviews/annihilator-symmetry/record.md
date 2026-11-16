# Review: left and right annihilators coincide at every level (pull request 47)

## Brief (path-free)

Read the workspace AGENTS.md and the repository AGENTS.md first; work read-only. Claims, at head db919fe: (1) the
statements hold at every level over every commutative ring with the identity as star and a compatible linear order,
and these hypotheses are satisfiable; (2) `Tower.dot` and `Tower.re` match the Rocq `dot` and `re` under the shared
product convention; (3) the Lean theorems generalize the integer theorems `kernel_equality`, `purity_left` and
`direct_finiteness`; (4) the theorem fails without an order (complex coefficients, characteristic 2); (5) the PR
follows the placement, docstring, challenge and commit rules; (6) the validation meets the verdict rule. Questions:
a lemma narrower than its proof, a misleading name, what is missing.

## Local reviewers

The owner chose codex (gpt-daybreak-blue, high effort) and no red-teamer.

### codex, on db919fe

| # | Finding | Severity | Reconciliation |
|---|---|---|---|
| 1 | `rocq/quantum/CdTowerDomain.v` already proves `kernel_equality`, `purity_left` and `direct_finiteness` over an abstract `OrderedDomain` (a relation with nonnegative squares, nonnegative sums vanishing termwise, no zero divisors, 1 ≠ 0), so the Lean theorems are its bridge, not a generalization of the integer file, and a linear order is more than the proof needs | P2 | Confirmed at CdTowerDomain.v:44 (signature) and :538, :562, :647 (theorems). 6fadf1a moved the hypotheses to `StarOrderedRing`, which the Advisor showed to be the sum-of-squares order (it excludes ℚ(√2) with its usual order), so it narrowed rather than widened. Fixed in c43061e: the theorems take the fields of `OrderedDomain`, a partial order compatible with addition (`IsOrderedAddMonoid`), `NoZeroDivisors` and the explicit hypothesis `hsq : ∀ x, 0 ≤ x * x`; examples over ℤ, ℚ, ℝ and every ordered field apply them through `mul_self_nonneg`. The docstrings and README name the functor as the original and the integer file as an instance; neither statement contains the other, since the Rocq relation needs no partial order and no Lean theorem needs 1 ≠ 0. |
| 2 | The challenge omits `Tower.re_eq_zero_of_mul_eq_zero`, which the README row advertises | P2 | Fixed in 6fadf1a and restated in c43061e: the challenge copies `Tower.re` and restates the theorem; the comparator accepts and rejects a copy whose conclusion reads `re k a = 0 ∧ re k a = 0`. |
| 3 | Lemma 9.5 of Biss, Dugger and Isaksen is orthogonality to the adjoined unit, which the PR does not prove | P2 | Confirmed at CdTowerDomain.v:574. Fixed in 6fadf1a: the module and README cite Lemma 9.4 and Corollary 9.3 only. |
| 4 | Characteristic 2 is no counterexample: `two_zero_commutative` makes every level commutative, and `kernel_swap_iff_two_zero` (rocq/quantum/CdTowerRing.v) ties failure to a square root of -1 with 2 ≠ 0 | P2 | Confirmed at CdTowerRing.v:327 and :556. Fixed in 6fadf1a (module docstring) and in the pull-request body. |

codex justified claims 1 and 2, and judged claim 3 narrow, claim 4 half false, and claims 5 and 6 falsified through findings 1 and 2; it found no name collision for the `rev` names.

## Advisor, on 918ef0c

| Finding | Reconciliation |
|---|---|
| Codex findings 2, 3 and 4 are confirmed and fixed | No change. |
| `StarOrderedRing` is the sum-of-squares order, so 6fadf1a narrowed the hypotheses | Fixed in c43061e (row 1 above). |
| A definition both provers hold lands with a comparison under `ci/` (AGENTS.md); `Tower.dot` and `Tower.re` were compared by reading only | Boundary: issue 48 owes `ci/compare_dot.sh`, evaluating both sides on the same integer vectors with a mutated reference. |
| The third calibration's rejection named another theorem; the body's axiom line was garbled; ℚ had no example | The calibration run now logs the diff of each altered copy, and each is rejected on the theorem it alters; `#print axioms` was rerun at c43061e; a ℚ example is added. |
| The first verification launch ran `rm -rf` on the workstation | It removed the session's own output directory; the owner is told, and later runs write fresh directories. |

## Validation of c43061e

Lean 4.35.0, Mathlib v4.35.0, on the Windows workstation: `lake build --wfail GororobaMath` exit 0; `#print axioms` of the three headline theorems: `propext`, `Classical.choice`, `Quot.sound`; `lake env leanchecker GororobaMath.CayleyDickson.AnnihilatorSymmetry` exit 0; the module builds under `--wfail` with Mathlib's standard linter set on (the setting of the warnings pull request); `lake comparator --config Challenge/AnnihilatorSymmetry.json` accepts and rejects three copies, each differing from the challenge in one line (the logged diffs) and each rejected on the theorem it alters.
