### Verification (commit `b947d1e36`, clean tree)

- `lake build --wfail GororobaMath.CayleyDickson.DoublingUnit` on `the compute workstation`: `Build completed successfully (9048 jobs)` (exit 0).
- `#print axioms` on `the compute workstation`: `doublingUnit_mul_doublingUnit_mul` uses `[propext, Quot.sound]`; `doublingUnit_mul_mul_add_mul_doublingUnit_mul` and `mul_doublingUnit_mul_eq_zero` use `[propext, Classical.choice, Quot.sound]`.
- `lake env lean --run ../ci/replay_modules.lean GororobaMath.CayleyDickson.DoublingUnit` on `the compute workstation`: `PASS GororobaMath.CayleyDickson.DoublingUnit` (exit 0).
- `sh ci/check.sh --quick` locally: exit 0 (`check_headline_results`: 110 rows; `check_claims_ledger`: 1384 rows; shellcheck, ruff, actionlint pass).

### Findings (ranked by consequence)

1. **Proof-hygiene violation — non-terminal `simp` (Claim 3 fails).** DoublingUnit.lean writes `ext <;> simp [star_sub, star_add, ha, hb] <;> abel`. Because `abel` follows `simp`, this violates AGENTS.md, which requires every non-terminal `simp` to be pinned as `simp only [...]`. Replace with `simp only [...]` (as in ScaledPairAnnihilator.lean).
2. **Missing commit-body evidence (Claim 3 fails).** `git log -1` shows commit `b947d1e36` carries only the subject line `lean: doubling unit anticommutes with doubly pure elements` and an empty body, violating AGENTS.md ("Give the body of a commit that changes a proof one sentence of evidence: the build, audit or replay").
3. **Docstring overstates theorem scope and hypotheses (Claim 2 partial fail).**
   - DoublingUnit.lean states "the identities hold at every level of the tower". `Tower R 0 = R` (Tower.lean) is not a `CayleyDickson` double and has no doubling unit; the theorems apply at every **doubled** level `Tower R (k + 1)` (`k ≥ 1`).
   - DoublingUnit.lean states "Only distributivity and the reversal `star (x y) = star y star x` enter". Both proofs also rely on `star_involutive` (`star (star c) = c`, `star (star d) = d`), additive `star` (`star_add`, `star_neg`), and the unit/zero laws (`one_mul`, `mul_one`, `zero_mul`, `mul_zero`).
   - DoublingUnit.lean equates `star a = -a ∧ star b = -b` with "orthogonal to `1` and to `h`". Orthogonality requires a trace form and `2` regular (char ≠ 2); over a ring of characteristic 2, `1` and `h` themselves satisfy `star a = -a ∧ star b = -b`.
4. **BDI attribution gaps (Claim 3 partial fail).** Against math_0511691.pdf:
   - `doublingUnit_mul_doublingUnit_mul` proves **Lemma 5.2** (`[i_n, i_n, x] = 0`, i.e., `i_n (i_n x) = -x`), not **Proposition 5.3** (the `C_n`-vector-space `Module` law `α (β x) = (α β) x` for all `α, β ∈ C_n`).
   - `doublingUnit_mul_mul_add_mul_doublingUnit_mul` proves the `α = i_n` case of **Lemma 5.7** (`α (x y) = x (α* y)`), omitted from DoublingUnit.lean; **Lemma 6.4** is BDI's one-line restatement of Lemma 5.7 for `L_x`.
   - `mul_doublingUnit_mul_eq_zero` proves the `α = i_n` case of **Lemma 9.6** (`Ann(x)` is `C_n`-invariant), also uncited.
   - The reference to ledger row `A5-671` (DoublingUnit.lean) matches line 649 of `gororoba-quantum/docs/evidence/a5-exceptional-fibers/ledger.tsv`.
5. **Existing API and tower-level overlap (maintainability).** Basic.lean already defines `CayleyDickson.unit := ⟨0, 1⟩`, whereas `DoublingUnit.lean` writes `(⟨0, 1⟩ : CayleyDickson A)` literally. Separately, AnnihilatorBound.lean (`Tower.iota_mul_iota_mul`) and ScaledPairAnnihilator.lean (`Tower.mk_mul_iota_mul`, `Tower.mul_cs_mul_eq_zero`) already prove the `[Field K] [StarRing K]` `Tower` specializations; `DoublingUnit.lean` strictly generalizes them to `[NonAssocRing A] [StarRing A]` and can later replace their bodies.

### Claim verdicts and natural generality

- **Claim 1 (`h (h z) = -z`): CONFIRMED.** No hidden hypotheses beyond `[NonAssocRing A] [StarRing A]`; matches Basic.lean (`h * (c, d) = (-star d, star c)`).
- **Claim 2 (`h (x z) + x (h z) = 0`): THEOREM AND HALF FORMULAS CONFIRMED; DOCSTRING OVERSTATES SCOPE.** Direct expansion confirms both halves in DoublingUnit.lean: `-(star a + a) * star d - c * (star b + b)` and `star c * (star a + a) - (star b + b) * d`.
- **Claim 3 (attribution and repository rules): FAILS** on items 1, 2, and 4 above. SPDX header, `module`, `@[expose] public section`, namespace `CayleyDickson`, convention docstring, and GororobaMath.lean import all conform.
- **Natural generality:** `star a = -a` and `star b = -b` cannot be weakened. Setting `z = (1, 0)` gives `h (x · 1) + x (h · 1) = (-(star b + b), star a + a)`, so `(∀ z, h (x z) + x (h z) = 0) ↔ star a = -a ∧ star b = -b`. Requiring only `star a + a` central fails for `x = (1, 0)` over `ℤ` (`star 1 + 1 = 2` is central, `h (x z) + x (h z) = 2 (h z) ≠ 0`). `[NonAssocRing A] [StarRing A]` is the exact minimal binder of `Basic.lean`. (An unconditional two-half identity without `ha, hb` would expose both sufficiency and necessity.)

### Next step: parity of `ker L_p ∩ ker L_q` and BDI Lemma 9.9

The cheapest Lean route avoids `ℝ`, `ℂ`, and `Module ℂ V` entirely and works over every ordered field `K` with `hsq : ∀ x : K, 0 ≤ x * x` (the exact binder of AnnihilatorBound.lean):

1. **7-line determinant parity lemma** (verified against Mathlib on `the compute workstation`, exit 0): for any `[Field K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]`, `(hnsq : ∀ c : K, c * c ≠ -1)`, and `J : Module.End K V` with `hJ : J * J = -1`, `Even (Module.finrank K V)` follows from `map_mul`, `(-1 : Module.End K V) = (-1 : K) • 1`, `LinearMap.det_smul`, `map_one`, and `Odd.neg_one_pow`. Under `hsq`, `c * c ≠ -1` is 2 lines from `0 ≤ c * c` and `0 < (1 : K)`.
2. **Common-kernel parity at every doubled level `k + 1`:** Let `V := ker (mulLeft K (k + 1) p) ⊓ ker (mulLeft K (k + 1) q)`. If `V = ⊥`, `finrank K V = 0` is even. If `V ≠ ⊥`, pick nonzero `z ∈ V`; for each of `p, q`, either it is `0` (trivially doubly pure) or `Tower.re_halves_eq_zero_of_mk_mul_eq_zero hsq` (ScaledPairAnnihilator.lean) plus `star_eq_neg_of_re_eq_zero` shows it is doubly pure. Then `mul_doublingUnit_mul_eq_zero` makes `V` invariant under `mulLeft K (k + 1) (mk 0 1)`, `LinearMap.restrict` produces `J : Module.End K V` with `J * J = -1` by `doublingUnit_mul_doublingUnit_mul`, and step 1 gives `Even (finrank K V)`.
3. **Complete BDI Lemma 9.9 over `K`:** Applying step 2 to `ker (mulLeft K (k + 1) (mk a b))` (with `p = q`) and to `ker (mulLeft K k a) ⊓ ker (mulLeft K k b)` (for `k ≥ 1`) makes both dimensions even in `Tower.finrank_ker_mulLeft_mk_le_add_inf` (AnnihilatorBound.lean), sharpening `2 ^ k - 1` to `2 ^ k - 2` by `omega`.
