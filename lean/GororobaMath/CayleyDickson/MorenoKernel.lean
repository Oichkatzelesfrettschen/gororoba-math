/- SPDX-License-Identifier: Apache-2.0 -/
module

public import GororobaMath.CayleyDickson.HalfFold
public import GororobaMath.CayleyDickson.LeftMulMatrix
public import GororobaMath.CayleyDickson.AssociatorSpace
public import Mathlib.LinearAlgebra.Complex.FiniteDimensional
public import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv

/-!
# The kernel of left multiplication by a doubly pure element has dimension divisible by four

Convention: `Tower ℝ k` is the tower of `GororobaMath.CayleyDickson.Tower` over the reals with the
product `(p, q) (c, d) = (p c - star d q, d p + q star c)`, `Tower.mk` builds a pair, and
`Tower.basis ℝ k` is its basis indexed by `BitVec k`. An element is pure when `star x = -x`,
equivalently `re x = 0` (`Tower.star_eq_neg_of_re_eq_zero`); an element `a = (p, q)` of level
`k + 1` is doubly pure when `dot a 1 = 0` and `dot a (mk 0 1) = 0`, that is, when `p` and `q`
are both pure. The matrix of a linear map has entry `(i, j)` equal to the coordinate at `i` of its
value at the basis vector `j`.

Write `y = (c, d)`, `u = c` and `w = star d`. For pure `p` and `q` the equation
`(p, q) y = 0` reads `p u - w q = 0` and `p w + u q = 0`: the second component of the product
is `d p + q star c`, and its star is `-(p w + u q)`. With `A` the matrix of left multiplication by
`p` and `B` the matrix of right multiplication by `q`, both skew (`A = -Aᵀ`, `B = -Bᵀ`) because
the trace form makes multiplication by a pure element skew, the pair `(u, w)` solves the system
exactly when the complex vector `u + i w` lies in the kernel of the complex matrix `A + i B`.
That matrix is skew-symmetric, and the nullity of a skew-symmetric matrix of even size is even,
since the alternating form it defines is nondegenerate on a complement of its kernel and a
nondegenerate alternating form has even rank (its Gram matrix has determinant `(-1)^n` times
itself). The real kernel has twice the complex dimension, so its dimension is divisible by four.
The proof needs no associativity, no norm condition and no order on the tower.

## Main results

* `Tower.even_finrank_ker_add_card_of_transpose_eq_neg`: over a field of characteristic zero, the
  nullity of a skew-symmetric matrix has the parity of its size.
* `Tower.finrank_ker_mulLeft_mk_eq`: for pure `p` and `q`, the real nullity of `(p, q)` is twice
  the complex nullity of `A + i B`.
* `Tower.four_dvd_finrank_ker_mulLeft_mk`: for pure `p` and `q` at `k ≥ 1`, the real nullity of
  `(p, q)` is divisible by four.
* `Tower.four_dvd_finrank_ker_mulLeft`: Moreno 1997, Corollary 1.17 (i), at every level, for the
  actual kernels. It is a concrete strengthening of `cor_1_17_mod4` of
  `rocq/open/theories/C1543_MorMod4Bound.v`, not its restatement: the Rocq declaration proves
  divisibility by four for every dimension that satisfies the abstract hypothesis `is_h_module_dim`
  (the reading of `Module.four_dvd_finrank_of_quaternion`, plan rows 69 and 70), while this theorem
  proves it for the kernel of left multiplication itself, with no module hypothesis.
-/

@[expose] public section

open Module Matrix

namespace CayleyDickson

namespace Tower

/-- Over a field of characteristic zero, the nullity of a skew-symmetric matrix has the parity of
its size. The matrix defines an alternating form; on a complement of its kernel the form is
nondegenerate, so its Gram matrix `G` satisfies `det G = (-1)^n det G` and `det G ≠ 0`, which
forces the complement to have even dimension `n`. -/
theorem even_finrank_ker_add_card_of_transpose_eq_neg {K ι : Type*} [Field K] [CharZero K]
    [Fintype ι] (Y : Matrix ι ι K) (hY : Yᵀ = -Y) :
    Even (finrank K (LinearMap.ker Y.mulVecLin) + Fintype.card ι) := by
  classical
  set R := LinearMap.ker Y.mulVecLin with hR
  -- the form
  let b : (ι → K) → (ι → K) → K := fun x y => x ⬝ᵥ Y.mulVec y
  have hb : ∀ x y, b y x = -b x y := by
    intro x y
    have h1 : y ⬝ᵥ Y.mulVec x = x ⬝ᵥ (Yᵀ.mulVec y) := by
      rw [Matrix.mulVec_transpose, Matrix.dotProduct_mulVec, dotProduct_comm]
    change y ⬝ᵥ Y.mulVec x = -(x ⬝ᵥ Y.mulVec y)
    rw [h1, hY, Matrix.neg_mulVec, dotProduct_neg]
  have hbR : ∀ w, ∀ r ∈ R, b w r = 0 := by
    intro w r hr
    have : Y.mulVec r = 0 := hr
    simp [b, this]
  obtain ⟨W, hW⟩ := Submodule.exists_isCompl R
  have hrad : ∀ w ∈ W, (∀ w' ∈ W, b w w' = 0) → w = 0 := by
    intro w hw h
    have hall : ∀ v, b w v = 0 := by
      intro v
      obtain ⟨r, hr, w', hw', rfl⟩ :=
        Submodule.mem_sup.1 (by rw [hW.sup_eq_top]; trivial : v ∈ R ⊔ W)
      have e1 := hbR w r hr
      have e2 := h w' hw'
      simp only [b] at e1 e2 ⊢
      rw [Matrix.mulVec_add, dotProduct_add, e1, e2, add_zero]
    have h0 : w ᵥ* Y = 0 := by
      ext j
      have := hall (Pi.single j 1)
      simpa [b, Matrix.dotProduct_mulVec] using this
    have h1 : Y.mulVec w = 0 := by
      have : Yᵀ.mulVec w = 0 := by rw [Matrix.mulVec_transpose]; exact h0
      rw [hY, Matrix.neg_mulVec, neg_eq_zero] at this
      exact this
    have : w ∈ R := h1
    exact (Submodule.disjoint_def.1 hW.disjoint) w this hw
  -- Gram matrix on W
  set n := finrank K W with hn
  let B := Module.finBasis K W
  let G : Matrix (Fin n) (Fin n) K := fun i j => b (B i : ι → K) (B j : ι → K)
  have hGt : Gᵀ = -G := by
    ext i j; exact hb (B i : ι → K) (B j : ι → K)
  have hdet : G.det ≠ 0 := by
    intro hd
    obtain ⟨v, hv, hGv⟩ := Matrix.exists_mulVec_eq_zero_iff.2 hd
    apply hv
    let w : W := ∑ j, v j • B j
    have hBw : ∀ i, b (B i : ι → K) (w : ι → K) = 0 := by
      intro i
      have h := congrFun hGv i
      have e : b (B i : ι → K) (w : ι → K) = ∑ j, G i j * v j := by
        simp only [b, w, G, Submodule.coe_sum, Submodule.coe_smul, Matrix.mulVec_sum,
          Matrix.mulVec_smul, dotProduct_sum, dotProduct_smul, smul_eq_mul]
        exact Finset.sum_congr rfl (fun j _ => mul_comm _ _)
      rw [e]; simpa [Matrix.mulVec, dotProduct] using h
    have hw1 : ∀ w' ∈ W, b w' (w : ι → K) = 0 := by
      intro w' hw'
      obtain ⟨x, rfl⟩ : ∃ x : W, (x : ι → K) = w' := ⟨⟨w', hw'⟩, rfl⟩
      have h2 : (x : ι → K) = ∑ i, B.repr x i • (B i : ι → K) := by
        have h3 := congrArg Subtype.val (B.sum_repr x)
        rw [Submodule.coe_sum] at h3
        simpa using h3.symm
      rw [h2]
      simp only [b]
      simp only [sum_dotProduct, smul_dotProduct, smul_eq_mul]
      exact Finset.sum_eq_zero (fun i _ => by
        have := hBw i; simp only [b] at this; rw [this, mul_zero])
    have hw0 : ∀ w' ∈ W, b (w : ι → K) w' = 0 := by
      intro w' hw'; rw [hb, hw1 w' hw', neg_zero]
    have hz : (w : ι → K) = 0 := hrad w w.2 hw0
    have hz' : w = 0 := Subtype.ext hz
    exact funext (Fintype.linearIndependent_iff.1 B.linearIndependent v hz')
  have hdet2 : G.det = (-1) ^ n * G.det := by
    have := congrArg Matrix.det hGt
    rw [Matrix.det_transpose, Matrix.det_neg, Fintype.card_fin] at this
    exact this
  have heven : Even n := by
    by_contra hodd
    rw [Nat.not_even_iff_odd] at hodd
    rw [hodd.neg_one_pow] at hdet2
    have : (2 : K) * G.det = 0 := by linear_combination hdet2
    rcases mul_eq_zero.1 this with h | h
    · exact two_ne_zero h
    · exact hdet h
  have hsum : finrank K R + n = Fintype.card ι := by
    rw [hn, Submodule.finrank_add_eq_of_isCompl hW, Module.finrank_fintype_fun_eq_card]
  obtain ⟨m, hm⟩ := heven
  exact ⟨finrank K R + m, by omega⟩
/-- The real and imaginary parts of a complex coordinate vector as a pair of real ones. -/
def pairEquiv (ι : Type*) : ((ι → ℝ) × (ι → ℝ)) ≃ₗ[ℝ] (ι → ℂ) where
  toFun p i := ⟨p.1 i, p.2 i⟩
  invFun z := (fun i => (z i).re, fun i => (z i).im)
  map_add' p q := by funext i; apply Complex.ext <;> simp
  map_smul' r p := by funext i; apply Complex.ext <;> simp
  left_inv p := by simp
  right_inv z := by funext i; apply Complex.ext <;> simp

variable {k : ℕ}

/-- The matrix of left multiplication by a pure element is skew in the basis. -/
theorem toMatrix_mulLeft_neg {p : Tower ℝ k} (hp : star p = -p) :
    (LinearMap.toMatrix (basis ℝ k) (basis ℝ k) (mulLeft ℝ k p))ᵀ =
      -LinearMap.toMatrix (basis ℝ k) (basis ℝ k) (mulLeft ℝ k p) := by
  rw [← toMatrix_mulLeft_star, hp]
  have : mulLeft ℝ k (-p) = -mulLeft ℝ k p := LinearMap.ext fun y => by simp [neg_mul]
  rw [this, map_neg]

/-- The matrix of right multiplication by a pure element is skew in the basis. -/
theorem toMatrix_mulRight_neg {q : Tower ℝ k} (hq : star q = -q) :
    (LinearMap.toMatrix (basis ℝ k) (basis ℝ k) (mulRight ℝ k q))ᵀ =
      -LinearMap.toMatrix (basis ℝ k) (basis ℝ k) (mulRight ℝ k q) := by
  ext i j
  simp only [Matrix.transpose_apply, Matrix.neg_apply, LinearMap.toMatrix_apply, mulRight_apply,
    basis_apply]
  rw [← dot_e_right, ← dot_e_right, dot_mul_right_of_star_eq_neg hq, dot_comm]

/-- The product of the complex matrix `A + i B` with `u + i w` has real part `A u - B w` and
imaginary part `A w + B u`. -/
theorem mulVec_pairEquiv {ι : Type*} [Fintype ι] (A Bm : Matrix ι ι ℝ) (u w : ι → ℝ) :
    (Matrix.of fun i j => (⟨A i j, Bm i j⟩ : ℂ)).mulVec (pairEquiv ι (u, w)) =
      pairEquiv ι (A.mulVec u - Bm.mulVec w, A.mulVec w + Bm.mulVec u) := by
  funext i
  apply Complex.ext
  · simp [Matrix.mulVec, dotProduct, pairEquiv, Complex.re_sum, Finset.sum_sub_distrib]
  · simp [Matrix.mulVec, dotProduct, pairEquiv, Complex.im_sum, Finset.sum_add_distrib]

section Kernel

/-- The coordinates of `(c, d)` as the complex vector with real part the coordinates of `c` and
imaginary part the coordinates of `star d`. -/
noncomputable def kerCoord (k : ℕ) : Tower ℝ (k + 1) ≃ₗ[ℝ] (BitVec k → ℂ) :=
  ((CayleyDickson.linearEquivProd (Tower ℝ k) ℝ).trans
    (LinearEquiv.prodCongr (basis ℝ k).equivFun
      ((starEquiv k).trans (basis ℝ k).equivFun))).trans (pairEquiv (BitVec k))

theorem kerCoord_mk (c d : Tower ℝ k) :
    kerCoord k (mk c d) = pairEquiv (BitVec k)
      ((basis ℝ k).equivFun c, (basis ℝ k).equivFun (star d)) := rfl

theorem mulVec_equivFun (x : Tower ℝ k) (f : Tower ℝ k →ₗ[ℝ] Tower ℝ k) :
    (LinearMap.toMatrix (basis ℝ k) (basis ℝ k) f).mulVec ((basis ℝ k).equivFun x) =
      (basis ℝ k).equivFun (f x) := by
  ext i
  have := congrFun (LinearMap.toMatrix_mulVec_repr (basis ℝ k) (basis ℝ k) f x) i
  simpa [Basis.equivFun_apply] using this

/-- The complex matrix `A + i B` of the kernel system, with `A` the matrix of `L_p` and `B` the
matrix of `R_q` in the basis. -/
noncomputable def kerMatrix (p q : Tower ℝ k) : Matrix (BitVec k) (BitVec k) ℂ :=
  Matrix.of fun i j => (⟨LinearMap.toMatrix (basis ℝ k) (basis ℝ k) (mulLeft ℝ k p) i j,
    LinearMap.toMatrix (basis ℝ k) (basis ℝ k) (mulRight ℝ k q) i j⟩ : ℂ)

/-- The matrix `A + i B` is skew-symmetric when `p` and `q` are pure. -/
theorem kerMatrix_transpose {p q : Tower ℝ k} (hp : star p = -p) (hq : star q = -q) :
    (kerMatrix p q)ᵀ = -kerMatrix p q := by
  ext i j
  apply Complex.ext
  · have := congrFun (congrFun (toMatrix_mulLeft_neg hp) i) j
    simpa [kerMatrix] using this
  · have := congrFun (congrFun (toMatrix_mulRight_neg hq) i) j
    simpa [kerMatrix] using this

/-- For pure `p` and `q`, `(p, q) y = 0` exactly when the complex coordinate vector of `y` lies in
the kernel of `A + i B`. -/
theorem mk_mul_eq_zero_iff_kerMatrix {p q : Tower ℝ k} (hp : star p = -p) (hq : star q = -q)
    (y : Tower ℝ (k + 1)) :
    mk p q * y = 0 ↔ (kerMatrix p q).mulVec (kerCoord k y) = 0 := by
  obtain ⟨c, d, rfl⟩ : ∃ c d, y = mk c d := ⟨CayleyDickson.re (A := Tower ℝ k) y,
    CayleyDickson.im (A := Tower ℝ k) y, rfl⟩
  rw [kerCoord_mk, kerMatrix, mulVec_pairEquiv, mulVec_equivFun, mulVec_equivFun,
    mulVec_equivFun, mulVec_equivFun, mk_mul_mk]
  rw [← map_sub, ← map_add, LinearEquiv.map_eq_zero_iff, Prod.mk_eq_zero,
    LinearEquiv.map_eq_zero_iff, LinearEquiv.map_eq_zero_iff, zero_eq_mk, mk_inj,
    mulLeft_apply, mulLeft_apply, mulRight_apply, mulRight_apply]
  refine and_congr Iff.rfl ?_
  have hY : star (d * p + q * star c) = -(p * star d + c * q) := by
    simp only [star_add, star_mul, star_star, hp, hq, neg_mul, mul_neg, neg_add_rev]
    exact add_comm _ _
  exact star_eq_zero.symm.trans (by rw [hY, neg_eq_zero])

/-- For pure `p` and `q`, the real nullity of `(p, q)` is twice the complex nullity of `A + i B`. -/
theorem finrank_ker_mulLeft_mk_eq {p q : Tower ℝ k} (hp : star p = -p) (hq : star q = -q) :
    finrank ℝ (LinearMap.ker (mulLeft ℝ (k + 1) (mk p q))) =
      2 * finrank ℂ (LinearMap.ker (kerMatrix p q).mulVecLin) := by
  have hmap : (LinearMap.ker (mulLeft ℝ (k + 1) (mk p q))).map (kerCoord k).toLinearMap =
      (LinearMap.ker (kerMatrix p q).mulVecLin).restrictScalars ℝ := by
    ext z
    simp only [Submodule.mem_map, LinearMap.mem_ker, mulLeft_apply, Submodule.restrictScalars_mem,
      Matrix.mulVecLin_apply]
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact (mk_mul_eq_zero_iff_kerMatrix hp hq y).1 hy
    · intro hz
      refine ⟨(kerCoord k).symm z, (mk_mul_eq_zero_iff_kerMatrix hp hq _).2 ?_, by simp⟩
      simpa using hz
  let e := LinearEquiv.ofSubmodules (kerCoord k) (LinearMap.ker (mulLeft ℝ (k + 1) (mk p q)))
    ((LinearMap.ker (kerMatrix p q).mulVecLin).restrictScalars ℝ) hmap
  rw [e.finrank_eq]
  exact finrank_real_of_complex (LinearMap.ker (kerMatrix p q).mulVecLin)

/-- For pure `p` and `q` at level `k ≥ 1`, the kernel of left multiplication by `(p, q)` has real
dimension divisible by four. -/
theorem four_dvd_finrank_ker_mulLeft_mk {p q : Tower ℝ k} (hk : 1 ≤ k) (hp : star p = -p)
    (hq : star q = -q) :
    4 ∣ finrank ℝ (LinearMap.ker (mulLeft ℝ (k + 1) (mk p q))) := by
  rw [finrank_ker_mulLeft_mk_eq hp hq]
  have h := even_finrank_ker_add_card_of_transpose_eq_neg (kerMatrix p q)
    (kerMatrix_transpose hp hq)
  have hc : Even (Fintype.card (BitVec k)) := by
    rw [Fintype.card_congr BitVec.equivFin.toEquiv, Fintype.card_fin]
    exact (Nat.even_pow.2 ⟨even_two, by omega⟩)
  obtain ⟨m, hm⟩ := (Nat.even_add.1 h).2 hc
  omega

/-- Moreno 1997, Corollary 1.17 (i), at every level: for a unit `a` orthogonal to `1` and to the
adjoined unit, the kernel of left multiplication by `a` has real dimension divisible by four. The
Rocq original is `cor_1_17_mod4` of `rocq/open/theories/C1543_MorMod4Bound.v`, which assumes that
the kernel dimension is an `is_h_module_dim` value. -/
theorem four_dvd_finrank_ker_mulLeft {a : Tower ℝ (k + 1)} (h1 : dot (k + 1) a 1 = 0)
    (hi : dot (k + 1) a (mk 0 1) = 0) (hn : dot (k + 1) a a = 1) :
    4 ∣ finrank ℝ (LinearMap.ker (mulLeft ℝ (k + 1) a)) := by
  obtain ⟨p, q⟩ := a
  change dot (k + 1) (mk p q) 1 = 0 at h1
  change dot (k + 1) (mk p q) (mk 0 1) = 0 at hi
  change dot (k + 1) (mk p q) (mk p q) = 1 at hn
  rw [dot_one_right, re_mk] at h1
  rw [dot_mk, dot_zero_right, zero_add, dot_one_right] at hi
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · exfalso
    have hp0 : (show ℝ from p) = 0 := h1
    have hq0 : (show ℝ from q) = 0 := hi
    rw [dot_mk] at hn
    change (show ℝ from p) * (show ℝ from p) + (show ℝ from q) * (show ℝ from q) = 1 at hn
    rw [hp0, hq0] at hn
    norm_num at hn
  · exact four_dvd_finrank_ker_mulLeft_mk hk (star_eq_neg_of_re_eq_zero h1)
      (star_eq_neg_of_re_eq_zero hi)

end Kernel

end Tower

end CayleyDickson
