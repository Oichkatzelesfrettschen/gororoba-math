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
| 1 | `rocq/quantum/CdTowerDomain.v` already proves `kernel_equality`, `purity_left` and `direct_finiteness` over an abstract `OrderedDomain` (a relation with nonnegative squares, nonnegative sums vanishing termwise, no zero divisors, 1 ≠ 0), so the Lean theorems are its bridge, not a generalization of the integer file, and a linear order is more than the proof needs | P2 | Confirmed at CdTowerDomain.v:44 (signature) and :538, :562, :647 (theorems). Fixed in 6fadf1a: the hypotheses are a partial order under which `star x * x ≥ 0` (`StarOrderedRing`), the identity as star and no zero divisors; the docstrings and README name the functor as the original and the integer file as an instance, and record that the Rocq signature, which asks no antisymmetry of its relation, is the wider. Two examples check that the integers and the reals satisfy the hypotheses. |
| 2 | The challenge omits `Tower.re_eq_zero_of_mul_eq_zero`, which the README row advertises | P2 | Fixed in 6fadf1a: the challenge copies `Tower.re` and restates the theorem; the comparator accepts and rejects a copy whose conclusion reads `re k a = 0 ∧ re k a = 0`. |
| 3 | Lemma 9.5 of Biss, Dugger and Isaksen is orthogonality to the adjoined unit, which the PR does not prove | P2 | Confirmed at CdTowerDomain.v:574. Fixed in 6fadf1a: the module and README cite Lemma 9.4 and Corollary 9.3 only. |
| 4 | Characteristic 2 is no counterexample: `two_zero_commutative` makes every level commutative, and `kernel_swap_iff_two_zero` (rocq/quantum/CdTowerRing.v) ties failure to a square root of -1 with 2 ≠ 0 | P2 | Confirmed at CdTowerRing.v:327 and :556. Fixed in 6fadf1a (module docstring) and in the pull-request body. |

codex justified claims 1 and 2, and judged claim 3 narrow, claim 4 half false, and claims 5 and 6 falsified through findings 1 and 2; it found no name collision for the `rev` names.

## Validation of 6fadf1a

Lean 4.35.0, Mathlib v4.35.0, on the Windows workstation: `lake build --wfail GororobaMath` exit 0; the module also builds under `--wfail` with Mathlib's standard linter set on (the setting of the warnings pull request); `lake env leanchecker GororobaMath.CayleyDickson.AnnihilatorSymmetry` exit 0; `lake comparator --config Challenge/AnnihilatorSymmetry.json` accepts and rejects three altered statements.
