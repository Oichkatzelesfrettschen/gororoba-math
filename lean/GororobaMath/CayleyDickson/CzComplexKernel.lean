/- SPDX-License-Identifier: Apache-2.0 -/
module

public import GororobaMath.CayleyDickson.MorenoKernel
public import GororobaMath.CayleyDickson.BorderedLeftMul
public import GororobaMath.CayleyDickson.AnnihilatorBound
public import GororobaMath.CayleyDickson.ScaledPairAnnihilator

/-!
# The complex form of the nullity of a doubly pure element: `nullity = 2^(k+1) - 4 - 2 rank_C C_z`

Convention: `Tower ℝ k` is the Cayley-Dickson tower of `GororobaMath.CayleyDickson.Tower` over the
reals with the product `(p, q) (c, d) = (p c - star d q, d p + q star c)`, `Tower.basis ℝ k` is
its basis indexed by `BitVec k` (index `p.toNat` of `cd_core.cd_sign`), and `Tower.czMatrix` is
the real matrix `C_y` of `GororobaMath.CayleyDickson.CzMatrix`. An element `y = mk p q` of level
`k + 1` is doubly pure when `p` and `q` both have coordinate `0` at index `0` (`y_0 = y_(2^k) =
0`; `Tower.DoublyPure`, `Tower.doublyPure_mk_iff`, with index `2 ^ k` of `mk p q` read through
`Tower.repr_mk_inr` and `Tower.toNat_cons_true_zero`). The complex coordinate vector of `y` is
`z_c = p_c - i q_c` for the nonzero indices `c` of level `k` (`Tower.czVec`), the complex matrix
`C_z = C_p - i C_q` has the entries `sign (r ^^^ c) c * z_(r ^^^ c)` (`Tower.czComplex`), and the
border vector is `conj z`. The ledger row A5-356 of gororoba-quantum writes `z = p + i q` and
`C_z = C_p + i C_q` (`Tower.czComplexPlus`); that matrix is the entrywise conjugate of
`Tower.czComplex` and has the same rank (`Tower.rank_czComplexPlus`).
The inner product `conj z ⬝ᵥ z` is the sum of `p_c^2 + q_c^2` over the nonzero indices.

The kernel matrix `A + i B` of `Tower.kerMatrix` (`A` the matrix of `L_p`, `B` that of `R_q`) has
real kernel dimension equal to the real nullity of `(p, q)` (`Tower.finrank_ker_mulLeft_mk_eq`).
In the border basis it is the bordered matrix `[[0, -conj z^T], [conj z, C_z]]`, because for `c ≠
0` and `r ≠ 0` the coordinate of `e_c q` at `r` is minus that of `q e_c` (polarization of pure
elements), and `C_z` is skew with `C_z z = 0`; the bordered-kernel splitting then removes one
complex dimension.

## Main results

* `Tower.kerMatrix_submatrix_border`: `kerMatrix p q` reindexed by `borderEquiv` is
  `bordered (czComplex p q) (conj z)`.
* `Tower.czComplex_transpose`, `Tower.czComplex_mulVec`: `C_z` is skew and `C_z z = 0`.
* `Tower.nullity_mk_add_two_rank_add_four`: for doubly pure nonzero `y = mk p q`,
  `nullity y + 2 rank_C C_z + 4 = 2^(k+1)`.
* `Tower.nullity_mk_level_five`: at level `5`, `nullity y + 2 rank_C C_z = 28`.
* `Tower.rank_czMatrix_mk_eq`: `rank_R C_y = 2 rank_C C_z + 2`.
* `Tower.rank_czComplexPlus`: `rank_C (C_p + i C_q) = rank_C (C_p - i C_q)`.
* `Tower.doublyPure_of_mk_mul_eq_zero`: both factors of a vanishing product of nonzero elements
  are doubly pure, at every level (the halves of each factor are imaginary,
  `Tower.re_halves_eq_zero_of_mk_mul_eq_zero`).
* `Tower.zeroDivisor_doublyPure_nullity_level_five`: at level `5` every zero divisor is doubly
  pure and the nullity of a nonzero doubly pure `y` is `28 - 2 rank_C C_z` with `z = p + i q`.
-/

@[expose] public section

open Module Matrix

namespace CayleyDickson

namespace Tower

variable {k : ℕ}

/-- The coordinate at index `0` is the real part. -/
theorem repr_zero_eq_re (x : Tower ℝ k) : (basis ℝ k).repr x 0#k = re k x := by
  rw [← dot_e_right, e_zero, dot_one_right]

/-- A pair `mk p q` has coordinate `0` at index `0` exactly when `p` does. -/
theorem repr_zero_mk (p q : Tower ℝ k) :
    (basis ℝ (k + 1)).repr (mk p q) 0#(k + 1) = (basis ℝ k).repr p 0#k := by
  rw [repr_zero_eq_re, repr_zero_eq_re, re_mk]

/-- The coordinate of `mk p q` at the index with top bit set over `i` (index `2 ^ k + i`) is
the coordinate of `q` at `i`: the basis of level `k + 1` is the product basis of the two halves
reindexed by the top bit. -/
theorem repr_mk_inr (p q : Tower ℝ k) (i : BitVec k) :
    (basis ℝ (k + 1)).repr (mk p q) (BitVec.cons true i) = (basis ℝ k).repr q i := by
  change (((((basis ℝ k).prod (basis ℝ k)).map (linearEquivProd (Tower ℝ k) ℝ).symm).reindex
    (sumEquiv k)).repr (CayleyDickson.mk p q)) (sumEquiv k (Sum.inr i)) = _
  rw [Basis.repr_reindex_apply, Equiv.symm_apply_apply, Basis.map_repr, LinearEquiv.trans_apply,
    Basis.prod_repr_inr]
  rfl

/-- The index `BitVec.cons true 0#k` is `2 ^ k`. -/
theorem toNat_cons_true_zero (k : ℕ) : (BitVec.cons true (0#k)).toNat = 2 ^ k := by
  simp only [BitVec.true_cons_zero, BitVec.toNat_twoPow]
  exact Nat.mod_eq_of_lt (Nat.pow_lt_pow_right (by norm_num) (Nat.lt_succ_self k))

/-- An element `y` of level `k + 1` is doubly pure when its coordinates at index `0` and at index
`2 ^ k` vanish (`y_0 = y_(2^k) = 0`). -/
def DoublyPure (y : Tower ℝ (k + 1)) : Prop :=
  (basis ℝ (k + 1)).repr y 0#(k + 1) = 0 ∧ (basis ℝ (k + 1)).repr y (BitVec.cons true 0#k) = 0

/-- `mk p q` is doubly pure exactly when `p` and `q` both have coordinate `0` at index `0`. -/
theorem doublyPure_mk_iff (p q : Tower ℝ k) :
    DoublyPure (mk p q) ↔ (basis ℝ k).repr p 0#k = 0 ∧ (basis ℝ k).repr q 0#k = 0 := by
  rw [DoublyPure, repr_zero_mk, repr_mk_inr]

theorem toMatrix_mulRight_apply (q : Tower ℝ k) (i j : BitVec k) :
    LinearMap.toMatrix (basis ℝ k) (basis ℝ k) (mulRight ℝ k q) i j =
      (basis ℝ k).repr (e ℝ k j * q) i := by
  simp [LinearMap.toMatrix_apply, basis_apply]

theorem kerMatrix_apply (p q : Tower ℝ k) (i j : BitVec k) :
    kerMatrix p q i j = ⟨(basis ℝ k).repr (p * e ℝ k j) i, (basis ℝ k).repr (e ℝ k j * q) i⟩ := by
  rw [kerMatrix, Matrix.of_apply, toMatrix_mulLeft_apply, toMatrix_mulRight_apply]

/-- For `c ≠ 0`, the coordinate of `e_c q` at `0` is `-q_c`. -/
theorem repr_e_mul_zero {q : Tower ℝ k} {c : BitVec k} (hc : c ≠ 0#k) :
    (basis ℝ k).repr (e ℝ k c * q) 0#k = -(basis ℝ k).repr q c := by
  rw [repr_e_mul, BitVec.xor_zero, negSign_self k c hc]
  simp

/-- For pure `q`, `c ≠ 0` and `r ≠ 0`, the coordinate of `e_c q` at `r` is minus that of `q e_c`:
`e_c q + q e_c` is a multiple of `1`. -/
theorem repr_e_mul_pure {q : Tower ℝ k} (hq : star q = -q) {c r : BitVec k} (hc : c ≠ 0#k)
    (hr : r ≠ 0#k) :
    (basis ℝ k).repr (e ℝ k c * q) r = -(basis ℝ k).repr (q * e ℝ k c) r := by
  have hu : star (e ℝ k c) = -e ℝ k c := by simp [star_e, hc]
  have h := mul_add_mul_of_star_eq_neg hu hq
  have h1 : (basis ℝ k).repr (1 : Tower ℝ k) r = 0 := by
    have := repr_e (R := ℝ) (0#k) r
    rw [e_zero] at this
    rw [this]
    simp [Ne.symm hr]
  have h2 := congrArg (fun x => (basis ℝ k).repr x r) h
  simp only [map_add, Finsupp.add_apply, map_smul, Finsupp.smul_apply, smul_eq_mul, h1,
    mul_zero] at h2
  linarith

/-- The complex coordinate vector `z = p - i q` on the nonzero indices. -/
noncomputable def czVec (p q : Tower ℝ k) : NonzeroIndex k → ℂ :=
  fun c => ⟨(basis ℝ k).repr p c.1, -(basis ℝ k).repr q c.1⟩

/-- The border vector `conj z = p + i q`. -/
noncomputable def czBorder (p q : Tower ℝ k) : NonzeroIndex k → ℂ :=
  fun c => ⟨(basis ℝ k).repr p c.1, (basis ℝ k).repr q c.1⟩

/-- The complex matrix `C_z = C_p - i C_q`. -/
noncomputable def czComplex (p q : Tower ℝ k) : Matrix (NonzeroIndex k) (NonzeroIndex k) ℂ :=
  Matrix.of fun r c => ⟨czMatrix p r c, -czMatrix q r c⟩

/-- In the border basis `A + i B` is `[[0, -conj z^T], [conj z, C_z]]`. -/
theorem kerMatrix_submatrix_border {p q : Tower ℝ k} (hp0 : (basis ℝ k).repr p 0#k = 0)
    (hq0 : (basis ℝ k).repr q 0#k = 0) :
    (kerMatrix p q).submatrix (borderEquiv k) (borderEquiv k) =
      Matrix.bordered (czComplex p q) (czBorder p q) := by
  have hq : star q = -q := star_eq_neg_of_re_eq_zero (by rw [← repr_zero_eq_re]; exact hq0)
  ext (⟨⟩ | r) (⟨⟩ | c)
  · rw [submatrix_apply, borderEquiv_inl, kerMatrix_apply, e_zero, mul_one,
      one_mul, hp0, hq0]
    apply Complex.ext <;> simp [bordered]
  · rw [submatrix_apply, borderEquiv_inl, borderEquiv_inr, kerMatrix_apply, repr_mul_e,
      BitVec.zero_xor, sign_self_of_ne c.2, repr_e_mul_zero c.2]
    apply Complex.ext <;> simp [bordered, czBorder]
  · rw [submatrix_apply, borderEquiv_inr, borderEquiv_inl, kerMatrix_apply, e_zero, mul_one,
      one_mul]
    apply Complex.ext <;> simp [bordered, czBorder]
  · rw [submatrix_apply, borderEquiv_inr, borderEquiv_inr, kerMatrix_apply,
      repr_e_mul_pure hq c.2 r.2]
    apply Complex.ext <;> simp [bordered, czComplex, czMatrix]

/-- The complex matrix `C_(p + i q) = C_p + i C_q` of the convention `z = p + i q`. -/
noncomputable def czComplexPlus (p q : Tower ℝ k) : Matrix (NonzeroIndex k) (NonzeroIndex k) ℂ :=
  Matrix.of fun r c => ⟨czMatrix p r c, czMatrix q r c⟩

open scoped ComplexOrder in
/-- `C_p + i C_q` is the entrywise conjugate of `C_p - i C_q`, a conjugate transpose of a
transpose, so the two have the same complex rank. -/
theorem rank_czComplexPlus (p q : Tower ℝ k) :
    (czComplexPlus p q).rank = (czComplex p q).rank := by
  have h : czComplexPlus p q = (czComplex p q)ᴴᵀ := by
    ext r c
    apply Complex.ext <;> simp [czComplexPlus, czComplex, Matrix.conjTranspose_apply]
  rw [h, Matrix.rank_transpose, Matrix.rank_conjTranspose]

theorem czMatrix_add (p q : Tower ℝ k) : czMatrix (p + q) = czMatrix p + czMatrix q := by
  ext r c
  simp [czMatrix, add_mul]

/-- `C_z` is skew. -/
theorem czComplex_transpose {p q : Tower ℝ k} (hp0 : (basis ℝ k).repr p 0#k = 0)
    (hq0 : (basis ℝ k).repr q 0#k = 0) : (czComplex p q)ᵀ = -czComplex p q := by
  ext r c
  have h1 := congrFun (congrFun (czMatrix_transpose hp0) r) c
  have h2 := congrFun (congrFun (czMatrix_transpose hq0) r) c
  simp only [Matrix.transpose_apply, Matrix.neg_apply] at h1 h2
  apply Complex.ext
  · simp [czComplex, h1]
  · simp [czComplex, h2]

/-- `C_z z = 0`: `C_p p = 0`, `C_q q = 0` and `C_p q + C_q p = 0` (the polarization of
`C_(p+q) (p+q) = 0`). -/
theorem czComplex_mulVec {p q : Tower ℝ k} (hp0 : (basis ℝ k).repr p 0#k = 0)
    (hq0 : (basis ℝ k).repr q 0#k = 0) : czComplex p q *ᵥ czVec p q = 0 := by
  funext r
  have hAp := congrFun (czMatrix_mulVec_repr hp0) r
  have hBq := congrFun (czMatrix_mulVec_repr hq0) r
  have hs : (basis ℝ k).repr (p + q) 0#k = 0 := by
    simp [hp0, hq0]
  have hm := congrFun (czMatrix_mulVec_repr hs) r
  simp only [Matrix.mulVec, dotProduct, Pi.zero_apply, czMatrix_add, Matrix.add_apply, map_add,
    Finsupp.add_apply, add_mul, mul_add, Finset.sum_add_distrib] at hAp hBq hm
  apply Complex.ext
  · simp only [Matrix.mulVec, dotProduct, czComplex, czVec, Matrix.of_apply, Complex.re_sum,
      Complex.mul_re, Finset.sum_sub_distrib, Pi.zero_apply, Complex.zero_re]
    simp only [mul_neg, neg_mul, neg_neg]
    linarith
  · simp only [Matrix.mulVec, dotProduct, czComplex, czVec, Matrix.of_apply, Complex.im_sum,
      Complex.mul_im, Pi.zero_apply, Complex.zero_im]
    simp only [mul_neg, neg_mul, Finset.sum_add_distrib, Finset.sum_neg_distrib]
    linarith

/-- The inner product `conj z ⬝ᵥ z` is nonzero for a nonzero doubly pure `mk p q`. -/
theorem czBorder_dotProduct_ne {p q : Tower ℝ k} (hp0 : (basis ℝ k).repr p 0#k = 0)
    (hq0 : (basis ℝ k).repr q 0#k = 0) (hy : mk p q ≠ 0) :
    czBorder p q ⬝ᵥ czVec p q ≠ 0 := by
  intro h
  have hre := congrArg Complex.re h
  have hsum : ∑ c : NonzeroIndex k,
      ((basis ℝ k).repr p c.1 * (basis ℝ k).repr p c.1 +
        (basis ℝ k).repr q c.1 * (basis ℝ k).repr q c.1) = 0 := by
    simpa [dotProduct, czBorder, czVec, Complex.re_sum] using hre
  have hz := (Finset.sum_eq_zero_iff_of_nonneg
    (fun c _ => add_nonneg (mul_self_nonneg _) (mul_self_nonneg _))).1 hsum
  apply hy
  have hall : ∀ i : BitVec k, (basis ℝ k).repr p i = 0 ∧ (basis ℝ k).repr q i = 0 := by
    intro i
    by_cases hi : i = 0#k
    · rw [hi]; exact ⟨hp0, hq0⟩
    · have := hz ⟨i, hi⟩ (Finset.mem_univ _)
      constructor <;> nlinarith [mul_self_nonneg ((basis ℝ k).repr p i),
        mul_self_nonneg ((basis ℝ k).repr q i)]
  have hp : p = 0 := (basis ℝ k).ext_elem fun i => by simpa using (hall i).1
  have hq : q = 0 := (basis ℝ k).ext_elem fun i => by simpa using (hall i).2
  rw [hp, hq, zero_eq_mk]

/-- For a nonzero doubly pure `y = mk p q`, the real nullity of `L_y`, twice the complex rank of
`C_z` and `4` add to `2^(k+1)`. -/
theorem nullity_mk_add_two_rank_add_four {p q : Tower ℝ k}
    (hp0 : (basis ℝ k).repr p 0#k = 0) (hq0 : (basis ℝ k).repr q 0#k = 0) (hy : mk p q ≠ 0) :
    nullity ℝ (k + 1) (mk p q) + 2 * (czComplex p q).rank + 4 = 2 ^ (k + 1) := by
  have hp : star p = -p := star_eq_neg_of_re_eq_zero (by rw [← repr_zero_eq_re]; exact hp0)
  have hq : star q = -q := star_eq_neg_of_re_eq_zero (by rw [← repr_zero_eq_re]; exact hq0)
  have h1 : nullity ℝ (k + 1) (mk p q) =
      2 * finrank ℂ (LinearMap.ker (kerMatrix p q).mulVecLin) := finrank_ker_mulLeft_mk_eq hp hq
  have hB := kerMatrix_submatrix_border hp0 hq0
  have hcard : Fintype.card (NonzeroIndex k) + 1 = 2 ^ k := by
    have h := Fintype.card_congr (borderEquiv k)
    rw [Fintype.card_sum, Fintype.card_unit] at h
    have h2 : Fintype.card (BitVec k) = 2 ^ k := by
      rw [Fintype.card_congr BitVec.equivFin.toEquiv, Fintype.card_fin]
    omega
  have r1 := Matrix.rank_add_finrank_ker_toLin' (kerMatrix p q)
  rw [Matrix.toLin'_apply'] at r1
  have h2 : Fintype.card (BitVec k) = 2 ^ k := by
    rw [Fintype.card_congr BitVec.equivFin.toEquiv, Fintype.card_fin]
  have hrk : ((kerMatrix p q).submatrix (borderEquiv k) (borderEquiv k)).rank =
      (kerMatrix p q).rank := Matrix.rank_submatrix _ _ _
  rw [hB] at hrk
  have r2 := Matrix.rank_add_finrank_ker_toLin' (Matrix.bordered (czComplex p q) (czBorder p q))
  have h4 := Matrix.finrank_ker_bordered_add_one (czComplex p q) (czBorder p q) (czVec p q)
    (czComplex_transpose hp0 hq0)
    (czComplex_mulVec hp0 hq0) (czBorder_dotProduct_ne hp0 hq0 hy)
  have r3 := Matrix.rank_add_finrank_ker_toLin' (czComplex p q)
  have h6 : Fintype.card (Unit ⊕ NonzeroIndex k) = Fintype.card (NonzeroIndex k) + 1 := by
    simp [Fintype.card_sum, add_comm]
  have hp2 : 2 ^ (k + 1) = 2 * 2 ^ k := by ring
  omega

/-- At level `5` the nullity of a nonzero doubly pure `y` is `28 - 2 rank_C C_z`. -/
theorem nullity_mk_level_five {p q : Tower ℝ 4} (hp0 : (basis ℝ 4).repr p 0#4 = 0)
    (hq0 : (basis ℝ 4).repr q 0#4 = 0) (hy : mk p q ≠ 0) :
    nullity ℝ 5 (mk p q) + 2 * (czComplex p q).rank = 28 := by
  have h : nullity ℝ (4 + 1) (mk p q) + 2 * (czComplex p q).rank + 4 = 2 ^ (4 + 1) :=
    nullity_mk_add_two_rank_add_four hp0 hq0 hy
  have h32 : (2 : ℕ) ^ (4 + 1) = 32 := by norm_num
  change nullity ℝ 5 (mk p q) + 2 * (czComplex p q).rank + 4 = 2 ^ 5 at h
  omega

/-- The real matrix `C_y` of a nonzero doubly pure `y` has rank `2 rank_C C_z + 2`. -/
theorem rank_czMatrix_mk_eq {p q : Tower ℝ k} (hp0 : (basis ℝ k).repr p 0#k = 0)
    (hq0 : (basis ℝ k).repr q 0#k = 0) (hy : mk p q ≠ 0) :
    (czMatrix (mk p q)).rank = 2 * (czComplex p q).rank + 2 := by
  have h := nullity_add_rank_add_two_of_ne_zero (y := mk p q) (by rw [repr_zero_mk]; exact hp0) hy
  have := nullity_mk_add_two_rank_add_four hp0 hq0 hy
  omega

/-- When a product of two nonzero elements vanishes, in either order, both factors are doubly pure:
each half of each factor is imaginary. -/
theorem doublyPure_of_mk_mul_eq_zero {a b c d : Tower ℝ k}
    (h : mk a b * mk c d = 0 ∨ mk c d * mk a b = 0) (hu : mk a b ≠ 0) (hw : mk c d ≠ 0) :
    DoublyPure (mk a b) ∧ DoublyPure (mk c d) := by
  have key : mk a b * mk c d = 0 → re k a = 0 ∧ re k b = 0 ∧ re k c = 0 ∧ re k d = 0 :=
    fun h' => re_halves_eq_zero_of_mk_mul_eq_zero (fun x : ℝ => mul_self_nonneg x) h' hu hw
  have key' : mk c d * mk a b = 0 → re k a = 0 ∧ re k b = 0 ∧ re k c = 0 ∧ re k d = 0 := by
    intro h'
    obtain ⟨h3, h4, h1, h2⟩ :=
      re_halves_eq_zero_of_mk_mul_eq_zero (fun x : ℝ => mul_self_nonneg x) h' hw hu
    exact ⟨h1, h2, h3, h4⟩
  obtain ⟨h1, h2, h3, h4⟩ := h.elim key key'
  rw [doublyPure_mk_iff, doublyPure_mk_iff, repr_zero_eq_re, repr_zero_eq_re, repr_zero_eq_re,
    repr_zero_eq_re]
  exact ⟨⟨h1, h2⟩, h3, h4⟩

/-- At level `5`, every zero divisor is doubly pure (`y_0 = y_16 = 0`) and the nullity of a nonzero
doubly pure `y = mk p q` is `28 - 2 rank_C C_z` for the `15 x 15` matrix `C_z = C_p + i C_q`. -/
theorem zeroDivisor_doublyPure_nullity_level_five :
    (∀ a b c d : Tower ℝ 4,
      (mk a b * mk c d = 0 ∨ mk c d * mk a b = 0) → mk a b ≠ 0 → mk c d ≠ 0 →
        DoublyPure (mk a b) ∧ DoublyPure (mk c d)) ∧
    ∀ p q : Tower ℝ 4, DoublyPure (mk p q) → mk p q ≠ 0 →
      nullity ℝ 5 (mk p q) + 2 * (czComplexPlus p q).rank = 28 := by
  refine ⟨fun a b c d h hu hw => doublyPure_of_mk_mul_eq_zero h hu hw, ?_⟩
  intro p q hd hy
  rw [doublyPure_mk_iff] at hd
  rw [rank_czComplexPlus]
  exact nullity_mk_level_five hd.1 hd.2 hy

end Tower

end CayleyDickson
