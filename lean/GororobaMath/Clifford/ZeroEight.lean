/- SPDX-License-Identifier: Apache-2.0 -/
module

public import GororobaMath.CayleyDickson.Tower

/-!
# The Clifford algebra of signature (0, 8) is the algebra of 16 x 16 real matrices

Convention. The quadratic form is `quadForm x = -(x 0 ^ 2 + ... + x 7 ^ 2)` on `Fin 8 → ℝ`
(`QuadraticMap.weightedSumSquares` with the weight `-1`), so every generator of
`CliffordAlgebra quadForm` squares to `-1`. The generator `i : Fin 8` is sent to the
matrix of left multiplication by the sedenion unit `e_(i + 1)` of `Tower ℝ 4`
(`gen i = BitVec.ofNat 4 (i + 1)`), so the units `e_1 .. e_8` are used; the basis
index `p : BitVec 4` of `Tower.e` is read as the row and column number
`p.toNat : Fin 16`. The matrix of left multiplication by `e_a` has row index equal to
the output coordinate: its entry at row `j` and column `l` is the coefficient of
`e_j` in `e_a * e_l`, namely `Tower.sign 4 a l` when `j = a ^^^ l` and `0`
otherwise (`leftMulZ`). A matrix of the library is the function of its row and
column; `Matrix (Fin 16) (Fin 16) ℝ` carries the usual product.

The sedenions are not alternative, and left multiplication by `e_a` squares to
`-1` (`Tower.negSign_xor_right`) while two such operators anticommute only for
indices of the octonion block and the doubling unit; the relations are checked for
`e_1 .. e_8` by evaluation (`genMat_sq`, `genMat_anti`).

## Main results

* `Clifford.ZeroEight.e_mul_e_eq_sum`: the product of two basis units of the
  tower is the column of `leftMulZ`, so the matrices are the left multiplications
  of the tower product.
* `Clifford.ZeroEight.genMat_sq`, `Clifford.ZeroEight.genMat_anti`: the relations of
  Cl(0, 8) over `ℤ`.
* `Clifford.ZeroEight.mono_linearIndependent`: the 256 ordered monomials of the
  generator matrices are linearly independent (by the characters that conjugation by
  a generator defines on them, and the trace).
* `Clifford.ZeroEight.cliffordEquivMatrix`: `CliffordAlgebra quadForm ≃ₐ[ℝ] Matrix (Fin 16) (Fin 16) ℝ`,
  the algebra map of `CliffordAlgebra.lift` at `v ↦ ∑ i, v i • G i`. Its Rocq partner
  for the matrix half is `rocq/open/verified/C1463_CliffordMatrixBasis.v:C1463_clifford_matrix_basis`.
-/

@[expose] public section

namespace Clifford.ZeroEight

open CayleyDickson

/-- The basis index of the sedenion unit that generator `i` is sent to: `e_(i + 1)`. -/
def gen (i : Fin 8) : BitVec 4 := BitVec.ofNat 4 (i.val + 1)

/-- The matrix of left multiplication by `e_a` on the coordinates of the sedenions:
entry `(j, l)` is the coefficient of `e_j` in `e_a * e_l`. -/
def leftMulZ (a : BitVec 4) : Matrix (Fin 16) (Fin 16) ℤ := fun j l =>
  if (a ^^^ BitVec.ofNat 4 l.val).toNat = j.val then
    Tower.sign 4 a (BitVec.ofNat 4 l.val) else 0

/-- The column `l` of `leftMulZ a` holds the coordinates of `e_a * e_l` in the tower. -/
theorem e_mul_e_eq_sum {R : Type*} [NonAssocRing R] [StarRing R] (a : BitVec 4) (l : Fin 16) :
    Tower.e R 4 a * Tower.e R 4 (BitVec.ofNat 4 l.val) =
      ∑ j : Fin 16, leftMulZ a j l • Tower.e R 4 (BitVec.ofNat 4 j.val) := by
  have hq : BitVec.ofNat 4 (a ^^^ BitVec.ofNat 4 l.val).toNat = a ^^^ BitVec.ofNat 4 l.val := by
    simp
  rw [Tower.e_mul_e_sign, Finset.sum_eq_single
    ⟨(a ^^^ BitVec.ofNat 4 l.val).toNat, (a ^^^ BitVec.ofNat 4 l.val).isLt⟩]
  · simp only [leftMulZ, hq, ↓reduceIte]
  · intro j _ hj
    have h : ¬ (a ^^^ BitVec.ofNat 4 l.val).toNat = j.val := fun h => hj (Fin.ext h.symm)
    simp only [leftMulZ, h, ↓reduceIte, zero_smul]
  · intro h
    exact absurd (Finset.mem_univ _) h

/-- The integer matrix of generator `i`. -/
def genMat (i : Fin 8) : Matrix (Fin 16) (Fin 16) ℤ := leftMulZ (gen i)

theorem genMat_sq : ∀ i : Fin 8, genMat i * genMat i = -1 := by decide +kernel

theorem genMat_anti :
    ∀ i j : Fin 8, i ≠ j → genMat i * genMat j + genMat j * genMat i = 0 := by decide +kernel

/-- The real `16 × 16` matrices. -/
abbrev Mat16 : Type := Matrix (Fin 16) (Fin 16) ℝ

/-- The real matrix of generator `i`. -/
def G (i : Fin 8) : Mat16 := (Int.castRingHom ℝ).mapMatrix (genMat i)

theorem G_sq (i : Fin 8) : G i * G i = -1 := by
  rw [G, ← map_mul, genMat_sq, map_neg, map_one]

theorem G_anti {i j : Fin 8} (h : i ≠ j) : G i * G j + G j * G i = 0 := by
  rw [G, G, ← map_mul, ← map_mul, ← map_add, genMat_anti i j h, map_zero]

theorem G_anti' {i j : Fin 8} (h : i ≠ j) : G i * G j = -(G j * G i) :=
  eq_neg_of_add_eq_zero_left (G_anti h)

/-- The quadratic form of signature `(0, 8)`. -/
noncomputable def quadForm : QuadraticForm ℝ (Fin 8 → ℝ) :=
  QuadraticMap.weightedSumSquares ℝ fun _ => (-1 : ℝ)

/-- The linear map `v ↦ ∑ i, v i • G i`. -/
def genLin : (Fin 8 → ℝ) →ₗ[ℝ] Mat16 where
  toFun v := ∑ i, v i • G i
  map_add' v w := by simp [add_smul, Finset.sum_add_distrib]
  map_smul' c v := by simp [Finset.smul_sum, smul_smul]

theorem genLin_sq (v : Fin 8 → ℝ) : genLin v * genLin v = algebraMap ℝ Mat16 (quadForm v) := by
  have hS : genLin v * genLin v = ∑ i, ∑ j, (v i * v j) • (G i * G j) := by
    simp only [genLin, LinearMap.coe_mk, AddHom.coe_mk]
    rw [Finset.sum_mul_sum]
    simp only [smul_mul_smul_comm]
  have hT : ∑ i, ∑ j, (v i * v j) • (G i * G j) = ∑ i, ∑ j, (v i * v j) • (G j * G i) := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    rw [mul_comm (v j) (v i)]
  have hsum : (∑ i, ∑ j, (v i * v j) • (G i * G j)) + ∑ i, ∑ j, (v i * v j) • (G j * G i) =
      ∑ i, ∑ j, (v i * v j) • (if i = j then ((-2 : ℝ) • (1 : Mat16)) else 0) := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [← smul_add]
    by_cases h : i = j
    · subst h
      simp only [↓reduceIte]
      rw [G_sq]
      module
    · simp only [h, ↓reduceIte]
      rw [G_anti h]
  have hdiag : ∑ i, ∑ j, (v i * v j) • (if i = j then ((-2 : ℝ) • (1 : Mat16)) else 0) =
      (∑ i, (v i * v i) * (-2 : ℝ)) • (1 : Mat16) := by
    rw [Finset.sum_smul]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp [smul_ite, smul_smul, Finset.sum_ite_eq]
  have hQ : algebraMap ℝ Mat16 (quadForm v) = (∑ i, (-1 : ℝ) * (v i * v i)) • (1 : Mat16) := by
    rw [Algebra.algebraMap_eq_smul_one]
    simp [quadForm]
  have hc : ∑ i, (v i * v i) * (-2 : ℝ) = 2 * ∑ i, (-1 : ℝ) * (v i * v i) := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => by ring
  have hS' : genLin v * genLin v = ∑ i, ∑ j, (v i * v j) • (G j * G i) := hS.trans hT
  have h3 : genLin v * genLin v + genLin v * genLin v = (∑ i, (v i * v i) * (-2 : ℝ)) • (1 : Mat16) := by
    calc genLin v * genLin v + genLin v * genLin v
        = (∑ i, ∑ j, (v i * v j) • (G i * G j)) + ∑ i, ∑ j, (v i * v j) • (G j * G i) := by
          rw [← hS, ← hS']
      _ = _ := hsum
      _ = _ := hdiag
  have h2 : (2 : ℝ) • (genLin v * genLin v) = (2 : ℝ) • algebraMap ℝ Mat16 (quadForm v) := by
    rw [two_smul, h3, hQ, smul_smul, hc]
  exact smul_right_injective Mat16 (two_ne_zero : (2 : ℝ) ≠ 0) h2

theorem genLin_gen (i : Fin 8) : genLin (Pi.single i 1) = G i := by
  simp [genLin, Pi.single_apply]

/-- The algebra map that sends the generator `i` to `G i`. -/
noncomputable def liftMat : CliffordAlgebra quadForm →ₐ[ℝ] Mat16 :=
  CliffordAlgebra.lift quadForm ⟨genLin, genLin_sq⟩

theorem liftMat_ι (i : Fin 8) :
    liftMat (CliffordAlgebra.ι quadForm (Pi.single i 1)) = G i := by
  rw [liftMat, CliffordAlgebra.lift_ι_apply]
  exact genLin_gen i

/-- The factor of the monomial `n` at position `j`: `G j` when bit `j` of `n` is set. -/
def factor (n : ℕ) (j : Fin 8) : Mat16 := if n.testBit j.val then G j else 1

/-- The ordered monomial of the bit set `n`: the product of the `G j` with bit `j`
set, in increasing order of `j`. -/
def mono (n : Fin 256) : Mat16 := ((List.finRange 8).map (factor n.val)).prod

/-- The sign with which `G i` commutes past the monomial `n`: `-1` per generator of
`n` other than `G i`. -/
def chi (i : Fin 8) (n : ℕ) : ℤ :=
  ((List.finRange 8).map fun j => if j ≠ i ∧ n.testBit j.val then (-1 : ℤ) else 1).prod

theorem chi_sq : ∀ (i : Fin 8) (n : Fin 256), chi i n.val * chi i n.val = 1 := by decide +kernel

/-- The commutation signs separate the 256 monomials. -/
theorem chi_sep :
    ∀ n m : Fin 256, n ≠ m → ∃ i : Fin 8, chi i n.val * chi i m.val = -1 := by decide +kernel

theorem list_comm {A ι : Type*} [Ring A] (x : A) (y : ι → A) (c : ι → ℤ) (L : List ι)
    (h : ∀ j ∈ L, x * y j = c j • (y j * x)) :
    x * (L.map y).prod = (L.map c).prod • ((L.map y).prod * x) := by
  induction L with
  | nil => simp
  | cons a L ih =>
    have h1 := h a (by simp)
    have ih' := ih (fun j hj => h j (by simp [hj]))
    simp only [List.map_cons, List.prod_cons]
    rw [← mul_assoc, h1, smul_mul_assoc, mul_assoc, ih', mul_smul_comm, smul_smul, mul_assoc]

theorem G_mono_comm (i : Fin 8) (n : Fin 256) : G i * mono n = chi i n.val • (mono n * G i) := by
  unfold mono chi
  apply list_comm (G i) (factor n.val)
  intro j _
  unfold factor
  by_cases hb : n.val.testBit j.val = true
  · by_cases hj : j = i
    · subst hj
      simp [hb]
    · simp only [hb, ↓reduceIte]
      simp only [ne_eq, hj, not_false_eq_true, and_self, ↓reduceIte, G_anti' (Ne.symm hj)]
      simp
  · simp only [Bool.not_eq_true] at hb
    simp [hb]

theorem isUnit_G (i : Fin 8) : IsUnit (G i) :=
  ⟨⟨G i, -G i, by rw [mul_neg, G_sq, neg_neg], by rw [neg_mul, G_sq, neg_neg]⟩, rfl⟩

theorem isUnit_list_prod {A : Type*} [Monoid A] (L : List A) (h : ∀ x ∈ L, IsUnit x) :
    IsUnit L.prod := by
  induction L with
  | nil => simp
  | cons a L ih =>
    rw [List.prod_cons]
    exact (h a (by simp)).mul (ih fun x hx => h x (by simp [hx]))

theorem isUnit_mono (n : Fin 256) : IsUnit (mono n) := by
  apply isUnit_list_prod
  intro x hx
  obtain ⟨j, _, rfl⟩ := List.mem_map.1 hx
  unfold factor
  split_ifs
  · exact isUnit_G j
  · exact isUnit_one

theorem trace_mono_mul_inv (n T : Fin 256) (u : Mat16) (hT : mono T * u = 1) (hT' : u * mono T = 1)
    (hne : n ≠ T) : Matrix.trace (mono n * u) = 0 := by
  obtain ⟨i, hi⟩ := chi_sep n T hne
  have hn := G_mono_comm i n
  have hT2 := G_mono_comm i T
  have hsq := chi_sq i T
  have hcomm : mono T * G i = chi i T.val • (G i * mono T) := by
    rw [hT2, smul_smul, hsq, one_smul]
  have hGu : G i * u = chi i T.val • (u * G i) := by
    calc G i * u = (u * mono T) * G i * u := by rw [hT', one_mul]
      _ = u * (mono T * G i) * u := by rw [mul_assoc u]
      _ = chi i T.val • (u * (G i * mono T) * u) := by
          rw [hcomm, mul_smul_comm, smul_mul_assoc]
      _ = chi i T.val • (u * G i * (mono T * u)) := by rw [mul_assoc u, mul_assoc, mul_assoc]
      _ = chi i T.val • (u * G i) := by rw [hT, mul_one]
  have hP : G i * (mono n * u) = -((mono n * u) * G i) := by
    calc G i * (mono n * u) = (G i * mono n) * u := by rw [mul_assoc]
      _ = chi i n.val • (mono n * (G i * u)) := by rw [hn, smul_mul_assoc, mul_assoc]
      _ = chi i n.val • (mono n * (chi i T.val • (u * G i))) := by rw [hGu]
      _ = (chi i n.val * chi i T.val) • (mono n * u * G i) := by
          rw [mul_smul_comm, smul_smul, mul_assoc]
      _ = -((mono n * u) * G i) := by rw [hi, neg_smul, one_smul]
  have e1 : G i * ((mono n * u) * G i) = mono n * u := by
    rw [← mul_assoc, hP, neg_mul, mul_assoc, G_sq]
    simp
  have e2 : Matrix.trace (G i * ((mono n * u) * G i)) = - Matrix.trace (mono n * u) := by
    rw [Matrix.trace_mul_comm, mul_assoc, G_sq]
    simp
  rw [e1] at e2
  linarith

/-- The 256 ordered monomials of the generator matrices are linearly independent. -/
theorem mono_linearIndependent : LinearIndependent ℝ mono := by
  rw [Fintype.linearIndependent_iff]
  intro c hc T
  obtain ⟨U, hU⟩ := isUnit_mono T
  have hT : mono T * ((U⁻¹ : Mat16ˣ) : Mat16) = 1 := by rw [← hU]; exact U.mul_inv
  have hT' : ((U⁻¹ : Mat16ˣ) : Mat16) * mono T = 1 := by rw [← hU]; exact U.inv_mul
  have h1 := congrArg (fun M : Mat16 => Matrix.trace (M * ((U⁻¹ : Mat16ˣ) : Mat16))) hc
  simp only [Finset.sum_mul, smul_mul_assoc, zero_mul, Matrix.trace_zero] at h1
  rw [Matrix.trace_sum] at h1
  simp only [Matrix.trace_smul] at h1
  rw [Finset.sum_eq_single T] at h1
  · rw [hT] at h1
    simp at h1
    exact h1
  · intro n _ hn
    rw [trace_mono_mul_inv n T _ hT hT' hn, smul_zero]
  · intro h
    exact absurd (Finset.mem_univ _) h

theorem finrank_clifford : Module.finrank ℝ (CliffordAlgebra quadForm) = 256 := by
  have : Invertible (2 : ℝ) := invertibleOfNonzero two_ne_zero
  rw [(CliffordAlgebra.equivExterior quadForm).finrank_eq,
    Module.finrank_eq_card_basis (Module.Basis.ExteriorAlgebra (Pi.basisFun ℝ (Fin 8)))]
  simp

theorem finrank_mat16 : Module.finrank ℝ Mat16 = 256 := by
  simp [Module.finrank_matrix]

theorem liftMat_surjective : Function.Surjective liftMat := by
  have hspan : Submodule.span ℝ (Set.range mono) = ⊤ :=
    mono_linearIndependent.span_eq_top_of_card_eq_finrank' (by simp [finrank_mat16])
  have hmem : ∀ n, mono n ∈ liftMat.range := by
    intro n
    apply Subalgebra.list_prod_mem
    intro x hx
    obtain ⟨j, _, rfl⟩ := List.mem_map.1 hx
    unfold factor
    split_ifs
    · exact ⟨CliffordAlgebra.ι quadForm (Pi.single j 1), liftMat_ι j⟩
    · exact Subalgebra.one_mem _
  have hle : (⊤ : Submodule ℝ Mat16) ≤ Subalgebra.toSubmodule liftMat.range := by
    rw [← hspan, Submodule.span_le]
    rintro _ ⟨n, rfl⟩
    exact hmem n
  intro M
  exact hle (Submodule.mem_top (x := M))

/-- The Clifford algebra of `quadForm` is the algebra of `16 × 16` real matrices, by the
algebra map that sends generator `i` to the matrix of left multiplication by the sedenion
unit `e_(i + 1)` (`leftMulZ`, tied to the tower product by
`e_mul_e_eq_sum`). The Rocq partner of the matrix half is
`rocq/open/verified/C1463_CliffordMatrixBasis.v:C1463_clifford_matrix_basis`. -/
noncomputable def cliffordEquivMatrix : CliffordAlgebra quadForm ≃ₐ[ℝ] Mat16 := by
  haveI : FiniteDimensional ℝ (CliffordAlgebra quadForm) :=
    Module.finite_of_finrank_pos (by rw [finrank_clifford]; norm_num)
  haveI : FiniteDimensional ℝ Mat16 := inferInstance
  exact AlgEquiv.ofBijective liftMat
    ⟨(LinearMap.injective_iff_surjective_of_finrank_eq_finrank
      (f := liftMat.toLinearMap) (by rw [finrank_clifford, finrank_mat16])).2
        liftMat_surjective, liftMat_surjective⟩

/-- The algebra of the quadratic form `quadForm` (generators squaring to `-1`) is isomorphic to
the algebra of `16 × 16` real matrices. -/
theorem cliffordAlgebra_equiv_matrix :
    Nonempty (CliffordAlgebra quadForm ≃ₐ[ℝ] Matrix (Fin 16) (Fin 16) ℝ) :=
  ⟨cliffordEquivMatrix⟩

theorem cliffordEquivMatrix_ι (i : Fin 8) :
    cliffordEquivMatrix (CliffordAlgebra.ι quadForm (Pi.single i 1)) = G i :=
  liftMat_ι i

end Clifford.ZeroEight
