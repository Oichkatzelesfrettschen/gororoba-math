# Review record: Lean corollaries for findings rows A5-622, A5-649 and A5-661

Branch `lean/partial-row-corollaries`. Local reviewer: `codex` (gpt-daybreak-blue, high effort,
read-only) on head `577abfab8`, with the brief and report beside this file. The Advisor reviews last.

## Reconciliation of the local round

| Claim | Verdict | Resolution |
|---|---|---|
| 1. Each statement holds at the generality of its proof | falsified | Fixed in `beee3e4fd`: `SquareZero` reads over a commutative ring without zero divisors (the cancellation `Tower.eq_zero_of_smul_eq_zero` replaces the inverse in `eq_re_smul_one_of_smul_eq`), and `associator_add_associator_swap_of_anticomm` over `NonUnitalNonAssocRing`. |
| 2. The field hypothesis is necessary | falsified | Fixed in `beee3e4fd`: the docstring now says that zero divisors break the result, by the example `ε • 1` over `ℚ[ε]/(ε²)`, and claims no necessity of a field. |
| 3. `associator` names `CayleyDickson.associator` | justified | The import of `Associator` into `AnticommutingAssociator.lean` landed in `a302405c2`. |
| 4. A5-649 reads proved | justified | The source row is `char0`; the Lean count needs only `2 ≠ 0`. |
| 5. A5-622 and A5-661 stay partial with the named open clauses | justified | - |
| 6. README counts and proof entries | justified | `check_claims_ledger` accepts the 1,384 rows. |
| 7. Proof hygiene | justified | - |
| Further defect 1: docstring sentence of `AssociatorPhaseNonzero` | accepted | Fixed in `beee3e4fd`: "every triple with a nonzero associator is a triple of imaginary units". |
| Further defect 2: field-necessity sentence | accepted | As claim 2. |
| Further defect 3: replay predates the import | accepted | The full gate on `beee3e4fd` replays all 100 tracked modules. |

## Validation on the amended head

`sh ci/check.sh` at `beee3e4fd` on an aarch64 host (Lean 4.35.0, Mathlib v4.35.0, ruff 0.14.11,
actionlint 1.7.12), in a scope capped at 20 GiB with swap off: passed in 577 s, the kernel replay
accepting 100 tracked modules and rejecting the fixture. `#print axioms` of each new theorem lists
`propext`, `Classical.choice` and `Quot.sound` at most. `sh ci/check_rocq.sh`: not run, no
Rocq source changes.

## Reviewer conjectures, kept open

1. A5-662 over every odd finite field: for `q` odd, `q^(2^n - 2)` square-zero elements and
   `q^(2^n - 2) + q^(2^(n-1) - 1)` nontrivial idempotents for `n ≥ 2`. Falsifier: `A_2` over
   `F_9` with counts other than 81 and 90; cheapest test: enumerate its 6,561 elements.
2. Iterated squaring: `x^(2^m) = 0` for some `m ≥ 1` exactly when `x * x = 0`. Cheapest test:
   induction on `mul_self_eq_zero_of_mul_self_mul_mul_self_eq_zero`.
3. A nonzero basis associator has pairwise distinct nonzero indices with `p ^^^ q ≠ x`. Cheapest
   test: combine `associator_e_e_e_ne_zero_iff` with `assocPhase_eq_false_of_dependent`.
