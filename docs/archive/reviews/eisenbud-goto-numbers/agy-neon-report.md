# Red-Team Review: `gororoba-math` PR 130 (`lean/eisenbud-goto`, head `3978afe34`)

Diff scope (`computed`: `git -C  diff --stat origin/main...3978afe34`): 2 files, 216 insertions — [MinimalMultiplicity.lean](lean/GororobaMath/EisenbudGoto/MinimalMultiplicity.lean) (+215) and [GororobaMath.lean](lean/GororobaMath.lean#L82) (+1).

---

## Claim Verdicts and Attempted Breaks

### Claim 1 — **Falsified (quantifier overstatement and missing degree 0)**

The claim states that [MinimalMultiplicity.lean](lean/GororobaMath/EisenbudGoto/MinimalMultiplicity.lean) proves all six results "for every `c` and `d`".

1. **Break attempt: `c = 0` in `alternating_betti` and `eisenbudGoto_numbers_two` — SUCCEEDED (breaks Claim 1).**
   - `proved` ([MinimalMultiplicity.lean](lean/GororobaMath/EisenbudGoto/MinimalMultiplicity.lean#L188-L189)): `alternating_betti` carries the hypothesis `(hc : 1 ≤ c)`. At `c = 0`, `1 + (-1)^0 * betti 0 0 = 1 ≠ 0` (codimension `0` has rank `1`, not `0`).
   - `proved` ([MinimalMultiplicity.lean](lean/GororobaMath/EisenbudGoto/MinimalMultiplicity.lean#L195-L196)): `eisenbudGoto_numbers_two` carries `(hc : 1 ≤ c)`. At `c = 0`, Lean's truncated subtraction makes `(0 + 1).choose (0 - 1) = 1.choose 0 = 1`, while `betti 0 1 = 1 * 1.choose 2 = 0`, so the first conjunct `0 = 1` is false.
2. **Break attempt: degree `0` in `coeff_hilbertSeries` — SUCCEEDED (partial gap in Claim 1).**
   - `proved` ([MinimalMultiplicity.lean](lean/GororobaMath/EisenbudGoto/MinimalMultiplicity.lean#L78-L79)): `coeff_hilbertSeries` proves `(hilbertSeries S c d).coeff (n + 1) = (hilbertFn c d n : S)` for all `c d n : ℕ` and `[CommRing S]`, covering degrees `k = n + 1 ≥ 1` only. The degree-`0` coefficient `(hilbertSeries S c d).coeff 0 = 1` is absent.
3. **Break attempt: sign or off-by-one in `numerator_eq` and `betti_identity` — FAILED (statements hold for all `c, j : ℕ`).**
   - `proved` ([MinimalMultiplicity.lean](lean/GororobaMath/EisenbudGoto/MinimalMultiplicity.lean#L106-L116)): `betti_identity` proves `(j : ℤ) * C(c + 1, j + 1) = c * C(c, j) - C(c, j + 1)` for all `c j : ℕ` (including `j = 0`, `j = c`, and `j > c`).
   - `proved` ([MinimalMultiplicity.lean](lean/GororobaMath/EisenbudGoto/MinimalMultiplicity.lean#L156-L184)): `numerator_eq` proves `1 + ∑_{q=0}^c (-1)^q betti c q t^{q+1} = (1 - t)^c (1 + c t)` in `ℤ[X]` for all `c : ℕ` (checked at `c = 0`: `1 = 1`; `c = 1`: `1 - t^2`; `c = 2`: `1 - 3t^2 + 2t^3`; `c = 3`: `1 - 6t^2 + 8t^3 - 3t^4`). The `q = 0` summand vanishes because `betti c 0 = 0`, and `q = 1` carries `(-1)^1 = -1`, matching the sign of `F_1 = S(-2)^{β_1}` in the resolution of `R = S / I`.
4. **Break attempt: `eval_hilbertPoly` agreement for `n ≥ 2` — FAILED (statement holds as written, though threshold is non-optimal).**
   - `proved` ([MinimalMultiplicity.lean](lean/GororobaMath/EisenbudGoto/MinimalMultiplicity.lean#L94-L102)): for all `[Field F] [CharZero F]` and `c d n : ℕ`, `eval_hilbertPoly` evaluates `hilbertPoly (hilbertNumerator F c) (d + 1)` at `n + 1 + 1 = n + 2 ≥ 2` and equates it to `hilbertFn c d (n + 1)` (the degree-`(n + 2)` coefficient). The bound `≥ 2` is weaker than optimal: `preHilbertPoly_eq_choose_add_sub` ([HilbertPoly.lean](file://lean/.lake/packages/mathlib/Mathlib/RingTheory/Polynomial/HilbertPoly.lean#L90-L91)) gives agreement already at `m = 1` for all `c, d`, and at `m = 0` whenever `d ≥ 1` or `c = 0`.

---

### Claim 2 — **Justified (at `p = 2`, for `c ≥ 1` on generator count)**

Algebraic specialization of Eisenbud-Goto (1984) Proposition 1.7 and Corollary 1.11 at `p = 2`:

| Quantity | General `p` formula | `p = 2` specialization | Lean statement | Match |
|---|---|---|---|---|
| Multiplicity | `C(c + p - 1, c)` | `C(c + 1, c) = c + 1` | `1 + c = (c + 1).choose c` ([MinimalMultiplicity.lean](lean/GororobaMath/EisenbudGoto/MinimalMultiplicity.lean#L196)) | Exact (`proved`, all `c ≥ 0`) |
| Generator count `μ(I)` | `C(c + p - 1, c - 1)` | `C(c + 1, c - 1) = C(c + 1, 2)` (`c ≥ 1`) | `betti c 1 = (c + 1).choose (c - 1)` ([MinimalMultiplicity.lean](lean/GororobaMath/EisenbudGoto/MinimalMultiplicity.lean#L196)) | Exact (`proved`, `1 ≤ c`) |
| Betti numbers `β_q` | `C(c + p - 1, q + p - 1) C(q + p - 2, p - 1)` | `C(c + 1, q + 1) C(q, 1) = q C(c + 1, q + 1)` | `betti c q := q * (c + 1).choose (q + 1)` ([MinimalMultiplicity.lean](lean/GororobaMath/EisenbudGoto/MinimalMultiplicity.lean#L70)) | Exact (`proved`, all `c, q : ℕ`) |

Attempted breaks:
1. **Break attempt: inequality directions in Corollary 1.11 docstring ([MinimalMultiplicity.lean](lean/GororobaMath/EisenbudGoto/MinimalMultiplicity.lean#L19-L21)) — FAILED.**
   - Test case: non-Cohen-Macaulay `R = k[x, y, z] / (x^2, xy, xz)` has `c = 1`, `p = 2` (2-linear Koszul resolution of `x(x,y,z)`), `μ(I) = 3 > 1 = C(2, 0)`, and `H_R(t) = (1 + t(1 - t)^2)/(1 - t)^2`, so `e(R) = 1 < 2 = C(2, 1)`. Both inequalities in the docstring (`μ(I) ≤ C(c + p - 1, c - 1)` and `e(R) ≥ C(c + p - 1, c)` iff CM) point in the right direction.
2. **Break attempt: general `p` parameterization — NOTED SCOPE BOUNDARY.**
   - `proved` ([MinimalMultiplicity.lean](lean/GororobaMath/EisenbudGoto/MinimalMultiplicity.lean#L61-L204)): `p` is hardcoded to `2` throughout; the file contains no general-`p` definition or theorem specializing to `p = 2`.

---

### Claim 3 — **Partially falsified (shared definitions, not theorem instances)**

1. **Break attempt: arithmetic mismatch in the literal lists — FAILED (all 14 numbers are exact).**
   - `proved` ([MinimalMultiplicity.lean](lean/GororobaMath/EisenbudGoto/MinimalMultiplicity.lean#L207-L213)):
     - `hilbertFn 6 3 n = C(n + 4, 3) + 6 C(n + 3, 3)` for `n = 0 .. 7` evaluates to `[10, 34, 80, 155, 266, 420, 624, 885]`.
     - `betti 6 (q + 1) = (q + 1) C(7, q + 2)` for `q = 0 .. 5` evaluates to `[21, 70, 105, 84, 35, 6]`, with `1 - 21 + 70 - 105 + 84 - 35 + 6 = 0` and `34 + 21 = 55 = C(11, 2)`.
2. **Break attempt: "instances of the general theorems" — SUCCEEDED (narrow break on phrasing).**
   - `proved` ([MinimalMultiplicity.lean](lean/GororobaMath/EisenbudGoto/MinimalMultiplicity.lean#L207-L213)): `e8_hilbertFn` and `e8_betti` are `decide` evaluations of the shared definitions `hilbertFn` and `betti`, not instantiations of `coeff_hilbertSeries`, `eval_hilbertPoly`, or `numerator_eq`. Because they evaluate the exact definitions appearing in those theorems, they cannot disagree with the general theorems; however, neither theorem's statement mentions `hilbertSeries`, `hilbertPoly`, or `numerator`.

---

### Claim 4 — **Falsified (depth and regular-sequence theory exist in Mathlib v4.35.0)**

Environment note (`computed`): `lean/.lake/packages/mathlib` does not exist in this worktree (`ls -ld` returned `No such file or directory`). The primary checkout's Mathlib at `lean/.lake/packages/mathlib` is present and verified at tag `v4.35.0` (`computed`: `git -C ... describe --tags --always` -> `v4.35.0`), matching [lakefile.toml](lean/lakefile.toml#L16).

Audit of [MinimalMultiplicity.lean](lean/GororobaMath/EisenbudGoto/MinimalMultiplicity.lean#L42-L51) against Mathlib `v4.35.0`:

1. **Break attempt: "no depth or regular-sequence theory over graded rings" / missing "graded depth" — SUCCEEDED (breaks Claim 4).**
   - `proved` + `computed` (`git grep` on Mathlib `v4.35.0`): Mathlib `v4.35.0` contains:
     - General ideal depth `Ideal.depth (I : Ideal R) (M : ModuleCat R)` and `ModuleCat.depth` ([Depth/Basic.lean](file://lean/.lake/packages/mathlib/Mathlib/RingTheory/Depth/Basic.lean#L66-L79)), plus `Ideal.depth_eq_sSup_length_isRegular` ([Depth/Basic.lean](file://lean/.lake/packages/mathlib/Mathlib/RingTheory/Depth/Basic.lean#L42-L44)) and Rees's theorem `ModuleCat.exists_isRegular_tfae` ([Depth/Rees.lean](file://lean/.lake/packages/mathlib/Mathlib/RingTheory/Depth/Rees.lean#L25-L33)).
     - Regular sequences `RingTheory.Sequence.IsRegular` / `IsWeaklyRegular` for arbitrary commutative rings ([RegularSequence.lean](file://lean/.lake/packages/mathlib/Mathlib/RingTheory/Regular/RegularSequence.lean#L1-L60)) and `projectiveDimension` behavior on regular-element quotients ([ProjectiveDimension.lean](file://lean/.lake/packages/mathlib/Mathlib/RingTheory/Regular/ProjectiveDimension.lean#L23-L25)).
     - The irrelevant ideal `𝒜₊` of any graded ring ([Homogeneous/Ideal.lean](file://lean/.lake/packages/mathlib/Mathlib/RingTheory/GradedAlgebra/Homogeneous/Ideal.lean)).
   - While `git grep -i "graded" Mathlib/RingTheory/Depth/ Mathlib/RingTheory/Regular/` returns 0 matches (so *homogeneous* regular-sequence lemmas and graded Auslander-Buchsbaum are genuinely absent), `Ideal.depth (𝒜₊.toIdeal) M` already defines depth at the irrelevant ideal and links it to regular sequences over any Noetherian graded ring. Listing "graded depth" as a missing definition overstates the gap.
2. **Remaining docstring claims — CONFIRMED ACCURATE (`computed` via `git grep` on Mathlib `v4.35.0`, 0 matches):**
   - `IsCohenMacaulay` / `CohenMacaulay`: 0 matches.
   - Castelnuovo-Mumford regularity (`Castelnuovo`, `Mumford`, `regularity` in `RingTheory/`): 0 matches (only regular-sequence prose).
   - Minimal graded free resolutions, graded Betti table (`Betti`, `MinimalResolution`, `FreeResolution`, `Auslander`, `Buchsbaum`): 0 matches.
   - Eagon-Northcott complex (`Eagon`, `Northcott`): 0 matches (only Northcott height/order property).
   - Multiplicity of a graded module (`HilbertSamuel`, `hilbertSeries`, `poincareSeries`): 0 matches; [Multiplicity.lean](file://lean/.lake/packages/mathlib/Mathlib/RingTheory/Multiplicity.lean#L16-L27) is divisor multiplicity only, and [HilbertPoly.lean](file://lean/.lake/packages/mathlib/Mathlib/RingTheory/Polynomial/HilbertPoly.lean#L38-L40) explicitly lists graded-module Hilbert polynomials under `## TODO`.

---

## Defects Beyond the Claims

1. **Monolithic `public import Mathlib` (`proved` + `computed`)**: [MinimalMultiplicity.lean](lean/GororobaMath/EisenbudGoto/MinimalMultiplicity.lean#L4) uses `public import Mathlib` (only 3 other files out of 80 in `lean/GororobaMath/` do so: `git grep -n "^public import Mathlib$" lean/GororobaMath/`). This pulls the full Mathlib environment into `.olean` elaboration and `leanchecker` replay on shared hosts that already hit OOM twice today, when only `Mathlib.RingTheory.Polynomial.HilbertPoly`, `Mathlib.Data.Nat.Choose.Sum`, and basic tactics are used.
2. **Self-contradictory docstring on `hilbertFn` (`proved`)**: [MinimalMultiplicity.lean](lean/GororobaMath/EisenbudGoto/MinimalMultiplicity.lean#L72-L74) reads ``The Hilbert function `C(d + n, d) + c C(d + n - 1, d)` at `n + 1` ``, overloading `n` as both the degree and `degree - 1` in one sentence. The definition computes `C(d + n + 1, d) + c C(d + n, d)`.
3. **Asymmetric index convention in `e8_hilbertFn` docstring (`proved`)**: [MinimalMultiplicity.lean](lean/GororobaMath/EisenbudGoto/MinimalMultiplicity.lean#L206-L208) states `at n = 1 .. 8` while mapping `n` over `List.range 8` (`0 .. 7`), whereas `e8_betti` on [line 212](lean/GororobaMath/EisenbudGoto/MinimalMultiplicity.lean#L212) explicitly writes `betti 6 (q + 1)` over `List.range 6`.
4. **Unexplained `e8_` prefix (`proved`)**: [MinimalMultiplicity.lean](lean/GororobaMath/EisenbudGoto/MinimalMultiplicity.lean#L36-L38) and [lines 207-213](lean/GororobaMath/EisenbudGoto/MinimalMultiplicity.lean#L207-L213) name the `(c = 6, d + 1 = 4)` instance `e8_hilbertFn` / `e8_betti` without explaining what `e8` refers to or citing the source of `(c = 6, d + 1 = 4)`.
5. **Missing Cohen-Macaulay hypothesis in Convention docstring (`proved`)**: [MinimalMultiplicity.lean](lean/GororobaMath/EisenbudGoto/MinimalMultiplicity.lean#L9-L10) asserts that "a graded algebra of codimension `c` and Krull dimension `d + 1` with minimal multiplicity has Hilbert series `(1 + c t) / (1 - t) ^ (d + 1)`", omitting the required hypotheses (Cohen-Macaulay, standard graded over a field, no linear relations in `I`).
6. **Incomplete `## Main results` list (`proved`)**: [MinimalMultiplicity.lean](lean/GororobaMath/EisenbudGoto/MinimalMultiplicity.lean#L24-L38) omits `eisenbudGoto_numbers_two`, `betti_identity`, and `coeff_one_sub_X_pow`.
7. **Repo gate hygiene (`proved`)**: No `sorry`, `axiom`, `native_decide`, or `debug.skipKernelTC` appears in [MinimalMultiplicity.lean](lean/GororobaMath/EisenbudGoto/MinimalMultiplicity.lean); [GororobaMath.lean](lean/GororobaMath.lean#L82) imports the new module; `README.md` and `ci/headline-results.tsv` are consistently untouched (not declared a headline result).

---

## Conjectures Suggested by the Material

1. **General `p`-linear numerator identity (`hypothesis`)**: For every `c ≥ 0` and `p ≥ 1`, defining `h_{c, p}(t) = ∑_{i=0}^{p-1} C(c + i - 1, i) t^i` and `β_{c, p}(q) = C(c + p - 1, q + p - 1) C(q + p - 2, p - 1)`, the identity
   `1 + ∑_{q=1}^c (-1)^q β_{c, p}(q) t^{q + p - 1} = (1 - t)^c h_{c, p}(t)`
   holds in `ℤ[t]`, generalizing `numerator_eq` from `p = 2` to all `p ≥ 1` (Eisenbud-Goto Proposition 1.7).
   - **Falsifier**: Any `(c, p, k)` with `c ≥ 0, p ≥ 1` where the `t^k` coefficient of `(1 - t)^c h_{c, p}(t)` differs from `(-1)^{k - p + 1} C(c + p - 1, k) C(k - 1, p - 1)` for `p ≤ k ≤ c + p - 1` or is nonzero for `1 ≤ k < p`.

2. **Sharp `hilbertPoly` agreement threshold (`hypothesis`)**: Over every `[Field F] [CharZero F]`, `(hilbertPoly (hilbertNumerator F c) (d + 1)).eval (m : F) = (hilbertSeries F c d).coeff m` holds for all `m ≥ 1` and all `c, d : ℕ`, and at `m = 0` if and only if `d ≥ 1 ∨ c = 0`.
   - **Falsifier**: Any `(c, d, m)` with `m ≥ 1` (or `m = 0` and `d ≥ 1`) where the two sides differ, or `(c ≥ 1, d = 0, m = 0)` where they agree.

3. **Direct reuse of Mathlib's `Ideal.depth` for graded rings (`hypothesis`)**: For any finitely generated graded module `M` over a Noetherian `ℕ`-graded ring `R` with `𝒜₊ • M ≠ M`, the maximal length of a *homogeneous* `M`-regular sequence in `𝒜₊` equals Mathlib's existing `Ideal.depth (𝒜₊.toIdeal) M`, so graded Cohen-Macaulayness can be defined directly from `Ideal.depth` and `ringKrullDim` without re-building depth.
   - **Falsifier**: A finitely generated graded module `M` over a Noetherian `ℕ`-graded ring `R` with `𝒜₊ • M ≠ M` whose maximal homogeneous `M`-regular sequence in `𝒜₊` is strictly shorter than `Ideal.depth (𝒜₊.toIdeal) M`.

4. **Scoped imports cut `leanchecker` peak memory (`hypothesis`)**: Replacing `public import Mathlib` at [MinimalMultiplicity.lean](lean/GororobaMath/EisenbudGoto/MinimalMultiplicity.lean#L4) with the minimal Mathlib module imports preserves compilation under `lake build --wfail` and reduces `leanchecker` peak RSS for `GororobaMath.EisenbudGoto.MinimalMultiplicity`.
   - **Falsifier**: `lake build --wfail` fails to elaborate under the scoped imports, or measured `leanchecker` peak RSS does not drop relative to `public import Mathlib`.
AGY-DONE
