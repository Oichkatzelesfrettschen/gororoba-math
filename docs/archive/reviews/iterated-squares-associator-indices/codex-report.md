The read-only sandbox blocked creation of `docs/archive/reviews/iterated-squares-associator-indices/codex-report.md`. The repository remains unchanged at `7dba38efe`. The report follows inline.

# Review report

## Findings ranked by consequence

1. **Serious — proved:** [`iterate_mul_self_eq_zero_iff`](lean/GororobaMath/CayleyDickson/SquareZero.lean:127) retains an avoidable `(2 : F) ≠ 0` hypothesis.

   The reverse implication at line 134 needs neither `NoZeroDivisors` nor `2 ≠ 0`. For the forward implication in characteristic two, `mul_self_eq_smul_sub` gives
   `x² = -N(x) • 1`. Thus `x⁴ = 0` implies `N(x)² • 1 = 0`; applying `re` and scalar square cancellation gives `N(x) = 0`, hence `x² = 0`. A case split on `2 = 0` removes `h2` from the existing induction.

   Some anti-nilpotence assumption remains necessary. At level zero over `F₃[t]/(t⁴)`, the class of `t` has nonzero square and zero fourth power. `NoZeroDivisors` excludes this counterexample, although reducedness may be sufficient.

2. **Serious — proved:** A5-661 understates the new formal coverage at [`ci/claims/ledger.tsv:1216`](ci/claims/ledger.tsv:1216).

   - Add `CayleyDickson.Tower.iterate_mul_self_eq_zero_iff` to the `proof` cell.
   - Replace the fourth-power-only sentence in the `note` cell with the all-`m ≥ 1` result.
   - Keep `status = partial`; the seven enumerated counts remain open.
   - A5-649 needs no change because independence is a new corollary, not part of its count claim.
   - A5-662 remains `owed`; three `n = 2` computations do not prove its universal statement.

3. **Moderate — proved:** The power sentence at [`SquareZero.lean:125`](lean/GororobaMath/CayleyDickson/SquareZero.lean:125) is true, but its stated mechanism is incomplete.

   `mul_self_eq_smul_sub` closes the span of `1` and `x` under squaring, while [`associator_span_one_self`](lean/GororobaMath/CayleyDickson/Associator.lean:189) makes that span associative. Together they identify repeated squaring with `x^(2^m)`. Span closure alone does not justify reassociation. Add a formal equality lemma or cite both mechanisms.

4. **Cosmetic — measured:** [`quaternion_prime_power_counts.py:53`](docs/archive/reviews/iterated-squares-associator-indices/quaternion_prime_power_counts.py:53) is 106 columns.

   `rg -n '.{101}'` reports only this line. The brief’s 100-column hygiene claim is therefore false. `git diff --check origin/main...HEAD` exits successfully.

## Claim decisions

1. **Iterated squares — partially falsified, proved.** The theorem covers every fixed `m ≥ 1`, and the existential statement follows. Its power interpretation is valid. The restriction `2 ≠ 0` is avoidable. The reverse implication needs neither disputed hypothesis.

2. **Independent indices — proved.** [`assocPhase_eq_false_of_dependent`](lean/GororobaMath/CayleyDickson/AssociatorPhase.lean:162) lists exactly the zero, repeated, and `p xor q = x` cases. These are precisely dependence of three vectors over `F₂`. The proof uses the zero branch of the associator formula, so it needs no hypothesis on two.

3. **Product convention — proved.** [`Tower.mk_mul_mk`](lean/GororobaMath/CayleyDickson/Tower.lean:66) is exactly
   `(a,b)(c,d) = (ac - star(d)b, da + b star(c))`. The script implements this recursively and extends the resulting basis table bilinearly.

4. **Fields and counts — proved and computed.**

   - `t² + 1` has no root over `F₃`.
   - `t² - 2` has no root over `F₅`.
   - `t³ - t - 1` has no root over `F₃`, hence is irreducible.
   - The corrected digit order makes index one the unit at [`quaternion_prime_power_counts.py:38`](docs/archive/reviews/iterated-squares-associator-indices/quaternion_prime_power_counts.py:38).

   For the three-variable form, the odd-dimensional finite-field formula gives `q²` points at zero and `q² + q` points at `-1/4`, because `quadraticChar((-1)(-1/4)) = quadraticChar(1/4) = 1`. The supplied computation reports `(81,90)`, `(625,650)`, and `(729,756)`, with zero predicate mismatches.

5. **Mutation control — computed.** Negating `s(1,2)` changes the F₉ counts from `(81,90)` to `(33,14)`. The planted control is effective. Flipping both `s(1,2)` and `s(2,1)` would leave all squares unchanged by antisymmetric cancellation; a square-only census cannot detect that paired mutation, and the record does not claim otherwise.

6. **Proof hygiene — falsified only by line length, measured.** The new nonterminal simplification uses `simp only`; the files set no global option; both theorem names appear in their module headers.

## A5-662 Lean route

`quadraticChar_card_sqrts` belongs to `Mathlib/NumberTheory/LegendreSymbol/QuadraticChar/Basic.lean`. It converts a one-variable square fiber into a quadratic-character value.

Mathlib v4.35.0 also contains `Mathlib/NumberTheory/LegendreSymbol/QuadraticChar/GaussSum.lean`, but:

- Direct diagonal-quadric cardinality declaration: **not found**.
- Required Jacobi-sum convolution evaluator: **not found**.
- Gauss-sum theorem already packaged as the required point count: **not found**.

The missing bridge proves, for odd `m`:

- `#{v | Σ vᵢ² = 0} = q^(m-1)`;
- for `c ≠ 0`,  
  `#{v | Σ vᵢ² = c} = q^(m-1) + χ((-1)^((m-1)/2)c) q^((m-1)/2)`.

At `m = 2^n - 1` and `c = -1/4`, the character equals one. A practical Lean route inducts on the variables, applies `quadraticChar_card_sqrts`, proves the missing character convolution, and then applies the two `SquareZero` characterizations.

Fresh lab grep and compilation are **not run**: the sandbox rejected the remote socket. The Mathlib source location is corroborated by the local v4.35 compiled-cache path; the “not found” results remain bounded by that execution gap.

## New conjectures

1. **Characteristic-two counts — hypothesis.** Over even `F_q`, level `n` has `q^(2^n-1)` square-zero elements and zero nontrivial idempotents. Here `x² = N(x)1` and `N(x) = (Σxᵢ)²`.

   Falsifier: `A₂(F₄)` differs from `(64,0)`. Cheapest test: add `F₄` to the enumerator.

2. **Associating independent triples — hypothesis.** For `D = 2^n ≥ 8`, the independent ordered triples with zero basis associator number
   `(D-2)(D-4)(D-8)/2`.

   This subtracts the proved nonzero count from `(D-1)(D-2)(D-4)`. Falsifier: the level-four count differs from 672. Cheapest test: enumerate the 4,096 triples of `BitVec 4`.

## Validation boundary

The supplied build, axiom reports, and full gate at `0c6d1d38b` are measured evidence for the Lean commit. The final commit adds a tracked Python file, while [`ci/check.sh:172`](ci/check.sh:172) checks every tracked Python file. A current-head quick gate and full gate remain **not run**.

**Verdict:** revise before merge. Remove the avoidable characteristic restriction, update A5-661’s proof and note cells, wrap the 106-column line, and run the gates on the final head.