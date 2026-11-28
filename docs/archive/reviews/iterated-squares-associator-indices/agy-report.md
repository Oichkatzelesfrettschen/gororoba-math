# Review: `gororoba-math` branch `lean/iterated-square-associator-indices` (`7dba38efe`)

## Ranked findings and defects

1. **Avoidable hypothesis `h2 : (2 : F) ≠ 0` in `iterate_mul_self_eq_zero_iff` and `mul_self_eq_zero_of_mul_self_mul_mul_self_eq_zero`** ([SquareZero.lean](lean/GororobaMath/CayleyDickson/SquareZero.lean#L107-L135)) — **falsifies Claim 1 (`proved`)**.
   - When `(2 : F) = 0`, `Tower.mul_self_eq_smul_sub` gives `x * x = (-dot k x x) • 1`, so `x * x * (x * x) = ((-dot k x x) * (-dot k x x)) • 1` (`smul_one_mul_smul_one`); applying `re k` and `NoZeroDivisors F` gives `-dot k x x = 0`, hence `x * x = 0`.
   - Verified in Lean 4.35.0 on the lab host (`the review scratch directory, check_lean.lean` via `lake env lean`): both `mul_self_eq_zero_of_four_no_h2` and `iterate_mul_self_eq_zero_iff_no_h2` compile with zero warnings without `h2` (`proved`). `2 ≠ 0` is required only for `mul_self_eq_zero_iff` (in char 2, `1 + e 1` has `re = 1 ≠ 0` and `(1 + e 1)^2 = 0`).
   - `NoZeroDivisors F` is needed for the forward direction (`ℚ[ε]/(ε³)` at `k = 0, m = 2` has `ε² ≠ 0, ε⁴ = 0`, though `IsReduced F` suffices); the backward direction needs neither `NoZeroDivisors F` nor `2 ≠ 0`.

2. **Control in `quaternion_prime_power_counts.py` misses antisymmetric and split-quaternion mutations** ([quaternion_prime_power_counts.py](docs/archive/reviews/iterated-squares-associator-indices/quaternion_prime_power_counts.py#L93-L129)) — **partially falsifies Claim 5 (`computed`)**.
   - `x * x` reads only the symmetric sum `s(i, j) + s(j, i)` for `i ≠ j`. Negating **both** `s(1, 2)` and `s(2, 1)` produces a non-associative algebra (`(e₁e₂)e₃ = +e₀ ≠ -e₀ = e₁(e₂e₃)`) with unchanged `F_9` output `{'nil2': 81, 'nil4': 81, 'idempotents': 90, 'predicate_mismatches': 0}` (`computed`, `the review scratch directory, verify_counts.py`).
   - Split quaternions (`(a, b)(c, d) = (ac + d* b, da + b c*)`) also keep `nil2 = 81, idempotents = 90` at `F_9` (isomorphic to `M_2(F_q)`), changing only `predicate_mismatches = 128`, which `main()` lines 126–129 do not assert.

3. **Line-length and commit-hygiene violations** — **falsifies Claim 6 (`measured`)**.
   - [quaternion_prime_power_counts.py](docs/archive/reviews/iterated-squares-associator-indices/quaternion_prime_power_counts.py#L53) is 106 columns (over the 100-column limit). Both Lean files stay ≤ 100 columns, have no non-terminal `simp`, no file-wide `set_option`, and list both new theorems in their module headers ([SquareZero.lean](lean/GororobaMath/CayleyDickson/SquareZero.lean#L29), [AssociatorPhaseNonzero.lean](lean/GororobaMath/CayleyDickson/AssociatorPhaseNonzero.lean#L32)).
   - Commit `0c6d1d38b` modifies two proof modules without the required build/audit/replay evidence sentence in its commit body ([AGENTS.md](AGENTS.md#L390-L391)).

4. **Minor docstring inaccuracies** (`measured`):
   - [AssociatorPhaseNonzero.lean](lean/GororobaMath/CayleyDickson/AssociatorPhaseNonzero.lean#L14-L15) states "The results read over every nonassociative ring with a star in which `2 ≠ 0`", though `independent_of_associator_e_e_e_ne_zero` (and three other theorems in the file) do not assume `2 ≠ 0`. Line 33 writes `x ≠ p ^^^ q` while line 102 states `p ^^^ q ≠ x` (equivalent by `ne_comm`).
   - [SquareZero.lean](lean/GororobaMath/CayleyDickson/SquareZero.lean#L125-L126): the mathematical claim that the iterated square equals `x^(2^m)` is true (`span_F {1, x}` is a quotient of the commutative associative ring `F[t]/(t^2 - 2(re x)t + N(x))` via `mul_self_eq_smul_sub`, `smul_mul_assoc'`, `mul_smul_comm'`), though `Tower F k` has no `Pow` instance in Lean.

## Claim-by-claim verdicts

| Claim | Verdict | Evidence |
|---|---|---|
| 1. `iterate_mul_self_eq_zero_iff` strength, hypotheses, power-associativity | **Falsified (hypothesis)**; strength & power-associativity **justified** | `∀ m ≥ 1` implies the existential in [record.md](docs/archive/reviews/proof71-corollaries/record.md#L34) (`proved`), but `h2 : (2 : F) ≠ 0` is avoidable (`proved`, `check_lean.lean`). `#print axioms`: `[propext, Classical.choice, Quot.sound]` (`measured`). |
| 2. `independent_of_associator_e_e_e_ne_zero` no `2 ≠ 0`, exact `F_2`-independence | **Justified** (`proved`) | [AssociatorPhaseNonzero.lean](lean/GororobaMath/CayleyDickson/AssociatorPhaseNonzero.lean#L100-L106) uses only `associator_e_e_e_eq_ite` and `assocPhase_eq_false_of_dependent`; the 7 conjuncts match the `2^3 - 1 = 7` nonzero `F_2`-combinations of `(p, q, x)`. `#print axioms`: `[propext, Classical.choice, Quot.sound]` (`measured`). |
| 3. Script product vs `Tower.lean` at level 2 | **Justified** (`computed`) | Formula matches `Tower.mk_mul_mk`/`star_mk` ([Tower.lean](lean/GororobaMath/CayleyDickson/Tower.lean#L66-L69)). `Tower.sign 2` and `sign_table(2)` agree entry-for-entry: `[[1,1,1,1],[1,-1,1,-1],[1,-1,-1,1],[1,1,-1,-1]]`. A non-CD diagonal sign change `s(1,1) = +1` (norm `-x₁² + x₂² + x₃²`) shifts `idempotents` at `F_27` to `702 = q² - q` (`computed`). |
| 4. Field tables and A5-662 counts at `n = 2` | **Justified** (`computed`) | Exhaustive field-axiom check and `m(t) = 0` at `t = index p` pass for `F_9, F_25, F_27`; independent direct quadric recount (`re x = 0, N = 0` and `2 re x = 1, N = 0`) gives `(81, 90)`, `(625, 650)`, `(729, 756)` (`the review scratch directory, verify_counts.py`). |
| 5. Control can fail | **Partially falsified** (`computed`) | Single-entry flip `s(1,2)` changes counts (`33, 14`), but flipping both `s(1,2)` and `s(2,1)` breaks associativity with identical counts and 0 mismatches (`verify_counts.py`). |
| 6. Proof hygiene | **Falsified** (`measured`) | Python line 53 is 106 chars; commit `0c6d1d38b` omits proof-evidence line. Lean files pass all hygiene rules. |

## Answers to open questions

### Claims ledger ([ci/claims/ledger.tsv](ci/claims/ledger.tsv))
- **A5-661** (`ledger.tsv:1216`): keep `status = partial` (the seven enumerated counts remain open); append `lean/GororobaMath/CayleyDickson/SquareZero.lean:CayleyDickson.Tower.iterate_mul_self_eq_zero_iff` to `proof` (col 7) and mention iterated squaring in `notes` (col 8).
- **A5-649** (`ledger.tsv:1202`): stays `proved`; optionally append `AssociatorPhaseNonzero.lean:CayleyDickson.Tower.independent_of_associator_e_e_e_ne_zero` to `proof` (col 7) (not strictly required since A5-649 states only the count).
- **A5-662** (`ledger.tsv:1217`): stays `owed` (a Python enumeration at `n = 2, q ∈ {9, 25, 27}` is computed evidence, not a Lean proof for all odd `p` and `n ≥ 2`).

### Lean route for A5-662 over every odd finite field `F_q`
- **Existing `gororoba-math` bridge**: `Tower.mul_self_eq_zero_iff`, `Tower.mul_self_eq_self_iff` ([SquareZero.lean](lean/GororobaMath/CayleyDickson/SquareZero.lean#L82)), `Tower.re_eq_repr_zero` ([PureDoublingTransport.lean](lean/GororobaMath/CayleyDickson/PureDoublingTransport.lean#L114)), `Tower.dot_eq_sum_repr` ([TraceForm.lean](lean/GororobaMath/CayleyDickson/TraceForm.lean#L336)), and `Tower.borderEquiv` ([BorderedLeftMul.lean](lean/GororobaMath/CayleyDickson/BorderedLeftMul.lean#L47)) reduce both counts to `N_m(c) = #{v : Fin m → F | ∑ i, v i ^ 2 = c}` at `m = 2^n - 1` for `c = 0` and `c = -1/4`.
- **Mathlib v4.35.0 declarations found** (under `the lab host's Mathlib package tree`):
  - `quadraticChar_card_sqrts` (`Mathlib/NumberTheory/LegendreSymbol/QuadraticChar/Basic.lean:213`): `N_1(c) = χ(c) + 1`.
  - `quadraticChar_sum_zero`, `quadraticChar_sq_one`, `quadraticChar_isQuadratic`, `quadraticChar_ne_one` (`Basic.lean:238, 144, 198, 206`).
  - `jacobiSum_nontrivial_inv` (`Mathlib/NumberTheory/JacobiSum/Basic.lean:140`): since `χ⁻¹ = χ`, gives `∑ u, χ(u) χ(1 - u) = -χ(-1)` directly in `ℤ`, yielding `N_2(0) = q + χ(-1)(q - 1)` and `N_2(c ≠ 0) = q - χ(-1)` without `AddChar` or Gauss sums (`gaussSum_sq` also exists in `Mathlib/NumberTheory/GaussSum.lean:222` as an alternative).
- **Missing ("not found" in Mathlib v4.35.0)**: the diagonal-quadric point-count theorem for `N_m(c)`. Inducting by pairs `m = 2r + 1` (convolving `N_{2r+1}` with `N_2`) gives `N_{2r+1}(0) = q^(2r)` and `N_{2r+1}(c ≠ 0) = q^(2r) + χ((-1)^r * c) * q^r`. For `n ≥ 2`, `r = 2^(n-1) - 1` is odd, so `(-1)^r * (-1/4) = (1/2)^2`, `χ = 1`, giving `q^(2^n - 2)` and `q^(2^n - 2) + q^(2^(n-1) - 1)`.

### Conjectures (`hypothesis`)
1. **Characteristic-2 dichotomy**: Over `F_q` with `q = 2^e`, `x * x = (∑ x_i)^2 • 1`, so square-zero elements form a hyperplane of size `q^(2^n - 1)`, `iterate_mul_self_eq_zero_iff` holds, and there are `0` nontrivial idempotents. Falsifier: any nontrivial idempotent or non-`256/4 = 64` square-zero count in `A_2(F_4)`; cheapest test: enumerate the 256 elements of `A_2(F_4)` (or prove in Lean from `mul_self_eq_smul_sub`).
2. **Signature invariance of A5-662**: Over odd `F_q` (`n ≥ 2`), every split Cayley-Dickson signature `γ ∈ (F_q^×)^n` has the same counts `q^(2^n - 2)` and `q^(2^n - 2) + q^(2^(n-1) - 1)`, because the product of the `2^n - 1` imaginary norm coefficients is `∏_i (-γ_i)^(2^(n-1))`, always a square. Falsifier: a split signature on `A_3(F_3)` with counts other than `729` and `756`; cheapest test: enumerate `F_3^7` (`2,187` points) for all `2^3` sign choices.
3. **Associating independent triples for `k ≥ 4`**: The fraction of `F_2`-independent triples `(p, q, x)` in `BitVec k` with zero associator is `0` at `k = 3` and `(D - 8) / (2(D - 1))` for `D = 2^k ≥ 8` (from `card_associator_e_e_e_ne_zero` divided by `(D - 1)(D - 2)(D - 4)`). Falsifier: a different count at `k = 4` (`8/30 = 4/15` of independent triples associating); cheapest test: `decide` on `BitVec 4`.
