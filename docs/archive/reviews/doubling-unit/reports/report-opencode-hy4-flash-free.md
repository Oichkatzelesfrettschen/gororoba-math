I'll start by reading the governing instructions and the diff under review.

Now the diff and the relevant source files.

Let me verify the citation against the paper and check the repo's records, while confirming the worktree state.

The algebra checks out by hand. Now I'll verify the build on the remote host and inspect related library theorems.

A prior theorem in `ScaledPairAnnihilator.lean` looks related. Let me examine it and run the remote build in parallel.

The build passes. I found an existing twin theorem; let me check gate rules and the parity follow-up infrastructure.

Let me test the cheapest parity lemma in scratch on the remote host.

# Red-team report - PR 153 (doubling unit anticommutes)

Verdict: both mathematical claims survive; one repo-rule breach falls; attribution holds. Read-only review, no files changed locally or remotely except a scratch file under `SCRATCH` on `the compute workstation`.

Build context: `the compute workstation '... git -C .. log -1 --format="%H %s"; git -C .. status --short; lean --version'` -> `b947d1e360f3b66d639f8fde3be2d9b2c6c0a573 lean: doubling unit anticommutes with doubly pure elements`, clean tree, Lean 4.35.0, `.lake` linked to a Lake tree outside the checkout.

## Ranked findings

1. **Claim 3 partially falls: proof hygiene at `DoublingUnit.lean:56`.** The line `simp [star_sub, star_add, ha, hb]` is followed by `<;> abel`, so it is a non-final `simp` and must be the `simp only [...]` that `simp?` prints (`AGENTS.md:366-369`). Compliant precedent: `ScaledPairAnnihilator.lean:188-195` (`simp only [mk_mul_mk, ...] <;> abel`). `:48` (`ext <;> simp`) is fine because `simp` closes there. This is not a math failure; the gate misses it (`ci/check.sh` has no `simp only` lint, verified by grep), so `--wfail` passing is not evidence of compliance. Fix: run `simp?` on that goal on `the compute workstation` and paste the printed `simp only` list.

2. **Claim 1 survives.** `doublingUnit_mul_doublingUnit_mul` (`:46-48`). With the product of `Basic.lean:12,175-183`, `h*(c,d)=(-star d,star c)` and `h*(h*(c,d))=(-c,-d)=-z` by `star_star`. No hidden hypothesis, no convention mismatch: the literal `⟨0,1⟩` is `Basic.unit` (`:237`), `h*h=-1` already at `:240-241`. Command `timeout 870 lake build --wfail GororobaMath.CayleyDickson.DoublingUnit 2>&1 | tail -40` -> `Build completed successfully (9048 jobs).`

3. **Claim 2 survives.** `doublingUnit_mul_mul_add_mul_doublingUnit_mul` (`:52-56`) states exactly the docstring's anticommutation for doubly pure `x=(a,b)`. Hand expansion gives `h*(x*z)=( -(star a*star d + c*star b), star c*star a - star b*d )`, `x*(h*z)=( -a*star d - c*b, star c*a - b*d )`; the sum is `(-(star a+a)*star d - c*(star b+b), star c*(star a+a) - (star b+b)*d)`, matching docstring `:16-17` term for term and vanishing iff `ha`, `hb`. The build above compiles this theorem too; only `simp`/`abel` appear, so no new axiom.

4. **Generality is natural; the suggested weakening fails.** Put `z=h`: `x*h=(-b,a)`, `h*(x*h)=(-star a,-star b)`, `x*(h*h)=-x`, so the sum is `(-(star a+a), -(star b+b))`. Both hypotheses are necessary. A lone central `star a + a = 0` does not suffice: over `ℂ` with conjugation, `a=1,b=0,z=h` gives `(-2,0) ≠ 0`. The theorem therefore sits at the generality its proof has (`AGENTS.md:356-358`).

5. **Docstring attribution accurate, with one optional sharpening.** `pdftotext -layout math_0511691.pdf SCRATCH/bdi.txt`: line 354 Prop 5.3 (left multiplication gives the `C_n`-vector space), 390 Lemma 5.7 `(yx)α=(yα*)x` and `α(xy)=x(α*y)`, 432-434 Lemma 6.4 (conjugate-linearity of `L_x`, proved from Lemma 5.7), 721 Lemma 9.6, 747 Lemma 9.9, 771 Prop 9.10. Prop 5.3 + Lemma 6.4 is a fair citation for `:23-28`; Lemma 5.7 (`α=i_n`, `α*=-i_n`) is the direct source of the identity and could be named. Row A5-671 exists at `gororoba-quantum/docs/evidence/a5-exceptional-fibers/ledger.tsv:649` and says the square and anticommutation are integer matrix identities, bilinear hence basis-wide.

6. **Maintenance overlap, low consequence.** `ScaledPairAnnihilator.lean:186-195` already proves `Tower.mk_mul_iota_mul` (the fixed-level anticommutation over a field, labeled BDI Lemma 6.4) and `:201-214` `mul_cs_mul_eq_zero` (kernel invariance, Lemma 9.6). The new module generalizes both to any `CayleyDickson A` over `NonAssocRing`+`StarRing` but never cites them. Add a docstring cross-reference; do not edit either file.

7. **Registry/ledger, low consequence.** `DoublingUnit` is absent from `ci/headline-results.tsv` (111 rows) and `ci/claims/ledger.tsv`; `ci/check.sh` steps 8/9 validate existing rows and do not require a new one. If the PR presents this as a headline result, `AGENTS.md:303-325` requires a row with a Rocq partner, otherwise leave as is. Minor naming inconsistency: `:46-56` uses `⟨0,1⟩` where `Basic.unit` (`:237`) exists.

## What should follow: parity step

The cheap Lean route is a determinant argument, already compiled on `the compute workstation` at `SCRATCH/parity.lean` (`lake env lean` -> no errors, one linter warning about a `simpa` that `simp [d]` closes):

```
lemma even_finrank_of_sq_eq_neg_one {K V} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
    [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    (J : V →ₗ[K] V) (hJ : J * J = -1) : Even (finrank K V) := by
  classical; let d := LinearMap.det J
  have hd1 : LinearMap.det (-1 : V →ₗ[K] V) = (-1 : K) ^ finrank K V := by
    rw [← LinearMap.det_toMatrix (Module.finBasis K V)]
    rw [map_neg, LinearMap.toMatrix_one, Matrix.det_neg]; simp
  have hd : d * d = (-1 : K) ^ finrank K V := by
    calc d * d = LinearMap.det (J * J) := by simp [d]
      _ = LinearMap.det (-1 : V →ₗ[K] V) := by rw [hJ]
      _ = (-1 : K) ^ finrank K V := hd1
  by_contra hne; rw [Nat.not_even_iff_odd] at hne
  have hp : (-1 : K) ^ finrank K V = -1 := hne.neg_one_pow
  rw [hp] at hd; have hnn : (0 : K) ≤ d * d := mul_self_nonneg d
  rw [hd] at hnn; linarith
```

Key API: `LinearMap.det` is a monoid hom; `Matrix.det_neg`, `LinearMap.toMatrix_one`, `Odd.neg_one_pow`, `Nat.not_even_iff_odd`. No Mathlib complex-structure helper exists (grep of `.lake/packages/mathlib/Mathlib` for `ComplexStructure` / `sq = -1` returned nothing). Precedents: `MorenoKernel.lean:63` (`even_finrank_ker_add_card_of_transpose_eq_neg`) and its `four_dvd_finrank_ker_mulLeft`; `CzComplexKernel.lean:287` (`doublyPure_of_mk_mul_eq_zero`); `TowerModule.lean:119` (`mulLeft`).

Route: take doubly pure factors `p,q` (BDI Lemma 9.5 / `doublyPure_of_mk_mul_eq_zero`), let `S = ker L_p ∩ ker L_q`; `mul_doublingUnit_mul_eq_zero` (`:60-64`) makes each kernel `L_h`-invariant, hence `S`; `J = L_h` restricted to `S` satisfies `J*J=-1` by claim 1; apply the lemma over `ℝ` to get `Even (finrank ℝ S)` (level 5: 0, 2, or 4 with the existing rank bound). This cannot be stated over arbitrary `NonAssocRing`+`StarRing`: the determinant step needs an ordered field, since `-1` is a square over `ℂ` (`i·Id` in odd dimension).
