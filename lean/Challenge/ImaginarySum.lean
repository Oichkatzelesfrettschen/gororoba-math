/- SPDX-License-Identifier: Apache-2.0 -/
module

public import GororobaMath.CayleyDickson.TraceForm

/-!
# Challenge: the sum of the imaginary basis elements

This file restates, with `sorry` as each proof, the headline theorems that the solution
module proves and that the "Lean library" table of `README.md` names, with the
definitions those statements use. It imports the library modules that the solution
module imports. `lake comparator --config` with the JSON file beside this one checks
that each named theorem of the solution module has the statement written here and
depends only on `propext`, `Classical.choice` and `Quot.sound`. No library module
imports this file, and the admission gate does not build it.
-/

@[expose] public section

namespace CayleyDickson

namespace Tower

universe u

variable {R : Type u} [CommRing R] [StarRing R]

variable (R) in
/-- The imaginary sum, the sum of the basis units other than `1`. -/
def isum (k : ℕ) : Tower R k := ∑ p ∈ Finset.univ.erase (0#k), e R k p

variable (R) in
theorem sum_e_succ (k : ℕ) :
    ∑ p : BitVec (k + 1), e R (k + 1) p =
      mk (∑ p : BitVec k, e R k p) (∑ p : BitVec k, e R k p) := by
  rw [← (sumEquiv k).sum_comp, Fintype.sum_sum_type]
  have h0 : ∀ p : BitVec k, e R (k + 1) (sumEquiv k (Sum.inl p)) = mk (e R k p) 0 := by
    intro p
    have hm : (BitVec.cons false p).msb = false := by simp
    change e R (k + 1) (BitVec.cons false p) = _
    rw [e_succ_of_not_msb hm]
    simp
  have h1 : ∀ p : BitVec k, e R (k + 1) (sumEquiv k (Sum.inr p)) = mk 0 (e R k p) := by
    intro p
    have hm : (BitVec.cons true p).msb = true := by simp
    change e R (k + 1) (BitVec.cons true p) = _
    rw [e_succ_of_msb hm]
    simp
  simp only [h0, h1, sum_mk, Finset.sum_const_zero]
  rw [add_mk, add_zero, zero_add]

variable (R) in
theorem isum_eq_sub (k : ℕ) : isum R k = ∑ p : BitVec k, e R k p - 1 := by
  rw [isum, Finset.sum_erase_eq_sub (Finset.mem_univ _), e_zero]

variable (R) in
theorem isum_zero : isum R 0 = 0 :=
  Finset.sum_eq_zero fun _ hp => absurd BitVec.of_length_zero (Finset.ne_of_mem_erase hp)

variable (R) in
/-- The imaginary sum doubles as `(s, 1 + s)`. -/
theorem isum_succ (k : ℕ) : isum R (k + 1) = mk (isum R k) (1 + isum R k) := by
  rw [isum_eq_sub, sum_e_succ, isum_eq_sub, one_eq_mk, sub_eq_add_neg, neg_mk, add_mk]
  exact mk_inj.2 ⟨by abel, by abel⟩

section Trivial

variable [TrivialStar R]

variable (R) in
omit [TrivialStar R] in
/-- The imaginary sum is pure. -/
theorem star_isum : ∀ k : ℕ, star (isum R k) = -isum R k
  | 0 => by rw [isum_zero, star_zero, neg_zero]
  | k + 1 => by rw [isum_succ, star_mk, neg_mk, star_isum k]

variable (R) in
theorem isum_laws_aux1 (k : ℕ)
    (L2 : ∀ x : Tower R k, isum R k * (isum R k * x) = (-(2 ^ k - 1 : R)) • x)
    (R2 : ∀ x : Tower R k, x * isum R k * isum R k = (-(2 ^ k - 1 : R)) • x)
    (F : ∀ x : Tower R k, isum R k * (x * isum R k) = isum R k * x * isum R k)
    (a b : Tower R k) :
    mk (isum R k) (1 + isum R k) * (mk (isum R k) (1 + isum R k) * mk a b) =
      (-(2 ^ (k + 1) - 1 : R)) • mk a b := by
  have hs := star_isum R k
  have Sq : isum R k * isum R k = (-(2 ^ k - 1 : R)) • (1 : Tower R k) := by
    have := L2 1
    rwa [mul_one] at this
  have ha := star_eq_smul_one_sub a
  have hb := star_eq_smul_one_sub b
  generalize isum R k = s at *
  simp only [mk_mul_mk, smul_mk, mk_inj]
  simp only [star_add, star_sub, star_mul, star_one, hs, star_smul', ha, hb,
    mul_add, add_mul, mul_sub, sub_mul, smul_mul_assoc', mul_smul_comm', mul_one, one_mul, mul_neg,
    neg_mul, Sq, L2, R2, F]
  constructor <;> module

variable (R) in
theorem isum_laws_aux2 (k : ℕ)
    (L2 : ∀ x : Tower R k, isum R k * (isum R k * x) = (-(2 ^ k - 1 : R)) • x)
    (R2 : ∀ x : Tower R k, x * isum R k * isum R k = (-(2 ^ k - 1 : R)) • x)
    (F : ∀ x : Tower R k, isum R k * (x * isum R k) = isum R k * x * isum R k)
    (a b : Tower R k) :
    mk a b * mk (isum R k) (1 + isum R k) * mk (isum R k) (1 + isum R k) =
      (-(2 ^ (k + 1) - 1 : R)) • mk a b := by
  have hs := star_isum R k
  have Sq : isum R k * isum R k = (-(2 ^ k - 1 : R)) • (1 : Tower R k) := by
    have := L2 1
    rwa [mul_one] at this
  have ha := star_eq_smul_one_sub a
  have hb := star_eq_smul_one_sub b
  generalize isum R k = s at *
  simp only [mk_mul_mk, smul_mk, mk_inj]
  simp only [star_add, star_one, hs,
    mul_add, add_mul, mul_sub, sub_mul, one_mul, mul_neg,
    neg_mul, L2, R2, F]
  constructor <;> module

variable (R) in
theorem isum_laws_aux3 (k : ℕ)
    (L2 : ∀ x : Tower R k, isum R k * (isum R k * x) = (-(2 ^ k - 1 : R)) • x)
    (R2 : ∀ x : Tower R k, x * isum R k * isum R k = (-(2 ^ k - 1 : R)) • x)
    (F : ∀ x : Tower R k, isum R k * (x * isum R k) = isum R k * x * isum R k)
    (a b : Tower R k) :
    mk (isum R k) (1 + isum R k) * (mk a b * mk (isum R k) (1 + isum R k)) =
      mk (isum R k) (1 + isum R k) * mk a b * mk (isum R k) (1 + isum R k) := by
  have hs := star_isum R k
  have Sq : isum R k * isum R k = (-(2 ^ k - 1 : R)) • (1 : Tower R k) := by
    have := L2 1
    rwa [mul_one] at this
  have ha := star_eq_smul_one_sub a
  have hb := star_eq_smul_one_sub b
  generalize isum R k = s at *
  simp only [mk_mul_mk, mk_inj]
  simp only [star_add, star_sub, star_neg, star_mul, star_one, hs, ha, hb,
    mul_add, add_mul, mul_sub, sub_mul, smul_mul_assoc', mul_smul_comm', mul_one, one_mul, mul_neg,
    neg_mul, Sq, L2, R2, F]
  constructor <;> module

variable (R) in
theorem isum_laws_all (k : ℕ) :
    (∀ x : Tower R k, isum R k * (isum R k * x) = (-(2 ^ k - 1 : R)) • x) ∧
    (∀ x : Tower R k, x * isum R k * isum R k = (-(2 ^ k - 1 : R)) • x) ∧
    (∀ x : Tower R k, isum R k * (x * isum R k) = isum R k * x * isum R k) := by
  induction k with
  | zero =>
    rw [isum_zero]
    refine ⟨fun x => ?_, fun x => ?_, fun x => ?_⟩ <;> simp
  | succ k ih =>
    obtain ⟨L2, R2, F⟩ := ih
    refine ⟨fun ⟨a, b⟩ => ?_, fun ⟨a, b⟩ => ?_, fun ⟨a, b⟩ => ?_⟩ <;> rw [isum_succ]
    · exact isum_laws_aux1 R k L2 R2 F a b
    · exact isum_laws_aux2 R k L2 R2 F a b
    · exact isum_laws_aux3 R k L2 R2 F a b

/-- For the imaginary sum `s`, `s (s x) = (x s) s = -(2 ^ k - 1) x` and `s (x s) = (s x) s` at
every level. The Rocq original is `isum_laws` of `rocq/quantum/CdImaginarySumConference.v`. -/
theorem isum_laws (k : ℕ) (x : Tower R k) :
    isum R k * (isum R k * x) = (-(2 ^ k - 1 : R)) • x ∧
      x * isum R k * isum R k = (-(2 ^ k - 1 : R)) • x ∧
      isum R k * (x * isum R k) = isum R k * x * isum R k := by
  sorry

/-- Left and right multiplication by the imaginary sum are skew for the trace form at every
level. The Rocq original is `isum_skew` of `rocq/quantum/CdImaginarySumConference.v`. -/
theorem dot_isum_mul (k : ℕ) (x y : Tower R k) :
    dot k (isum R k * x) y = -dot k x (isum R k * y) ∧
      dot k (x * isum R k) y = -dot k x (y * isum R k) := by
  sorry

/-- Right multiplication by the imaginary sum scales the trace form by `2 ^ k - 1`, a skew
conference matrix. The Rocq original is `isum_conference` of
`rocq/quantum/CdImaginarySumConference.v`. -/
theorem dot_mul_isum_mul_isum (k : ℕ) (x y : Tower R k) :
    dot k (x * isum R k) (y * isum R k) = (2 ^ k - 1 : R) * dot k x y := by
  sorry

/-- `I + R_s` is a skew Hadamard matrix at every level. The Rocq original is
`isum_skew_hadamard` of `rocq/quantum/CdImaginarySumConference.v`. -/
theorem dot_add_mul_isum (k : ℕ) (x y : Tower R k) :
    dot k (x + x * isum R k) (y + y * isum R k) = (2 ^ k : R) * dot k x y := by
  sorry

/-- The map `α I + β R_s` scales the trace form by `α ^ 2 + (2 ^ k - 1) β ^ 2`. The Rocq original
is `isum_scaled_isometry` of `rocq/quantum/CdTowerBasisSign.v`. -/
theorem dot_smul_add_smul_mul_isum (k : ℕ) (α β : R) (x y : Tower R k) :
    dot k (α • x + β • (x * isum R k)) (α • y + β • (y * isum R k)) =
      (α * α + (2 ^ k - 1) * (β * β)) * dot k x y := by
  sorry

omit [TrivialStar R] in
/-- The arc matrix of right multiplication by the imaginary sum: the coordinate of `e a * s` at
index `a ^^^ b` is `sign k a b` for `b ≠ 0`. The Rocq original is `arc_entry` of
`rocq/quantum/CdTowerBasisSign.v`, whose index `a < 2 ^ k` is `a.toNat` here. -/
theorem repr_e_mul_isum {k : ℕ} (a b : BitVec k) (hb : b ≠ 0#k) :
    (basis R k).repr (e R k a * isum R k) (a ^^^ b) = (Tower.sign k a b : R) := by
  sorry

end Trivial

end Tower

end CayleyDickson
