/- SPDX-License-Identifier: Apache-2.0 -/
module

public import GororobaMath.CayleyDickson.AlternativeIdentities
public import GororobaMath.CayleyDickson.ZeroDivisors
public import GororobaMath.CayleyDickson.Kaplansky

/-!
# Reversal of the inverse of a product: levels up to 3, and its failure from level 4

Convention: the product of `Tower K k` is the Cayley-Dickson product
`(a, b) (c, d) = (a c - star d b, d a + b star c)` of `GororobaMath.CayleyDickson.Basic` over a
field `K` with the identity as star, and `Tower.normInv x = (dot x x)⁻¹ • star x` is the inverse
by the trace norm, a two-sided inverse of `x` whenever `dot x x ≠ 0`.

## Main results

* `Tower.normInv_mul_iff`: over an ordered field `(a b)⁻¹ = b⁻¹ a⁻¹` holds for every `a` and `b`
  exactly at the levels `k ≤ 3`.
* `Tower.exists_normInv_mul_mul_ne`: the left inverse property `x⁻¹ (x y) = y` fails from level 4
  for an element with nonzero norm.
* `Tower.exists_normInv_mul_ne`: from level 4 on, a pair of elements with nonzero norms violates
  the reversal. The pair is built from a zero-divisor pair `x * y = 0`: `(x + s) y = s y`, and the
  reversal at `a = x + s`, `b = y` for `s = 1` and `s = -1` would force `dot x x = 0`.
-/

@[expose] public section

namespace CayleyDickson

namespace Tower

universe u

section Field

variable {K : Type u} [Field K] [LinearOrder K] [IsStrictOrderedRing K] [StarRing K]
  [TrivialStar K] {k : ℕ}

/-- From level 4 on, over an ordered field, the inverse of a product is not always the product of
the inverses in reverse order. -/
theorem exists_normInv_mul_ne (hk : 4 ≤ k) :
    ∃ a b : Tower K k, dot k a a ≠ 0 ∧ dot k b b ≠ 0 ∧
      normInv (a * b) ≠ normInv b * normInv a := by
  have hsq : ∀ z : K, 0 ≤ z * z := fun z => mul_self_nonneg z
  obtain ⟨x, y, hx, hy, hxy⟩ := exists_zero_divisor (R := K) hk
  have hd : dot k y y ≠ 0 := dot_self_ne_zero hsq hy
  have hmul : ∀ s : K, (x + s • (1 : Tower K k)) * y = s • y := fun s => by
    rw [add_mul, hxy, zero_add, smul_mul_assoc', one_mul]
  have hne : ∀ s : K, s ≠ 0 → dot k (x + s • (1 : Tower K k)) (x + s • 1) ≠ 0 := by
    intro s hs
    apply dot_self_ne_zero hsq
    intro ha
    have h := hmul s
    rw [ha, zero_mul] at h
    exact hy (eq_zero_of_smul_eq_zero hs h.symm)
  have key : ∀ s : K, s ≠ 0 →
      normInv ((x + s • (1 : Tower K k)) * y) = normInv y * normInv (x + s • 1) →
        dot k x x + 2 * s * re k x = 0 := by
    intro s hs heq
    have hna := hne s hs
    have hn : dot k (x + s • (1 : Tower K k)) (x + s • 1) = dot k x x + 2 * s * re k x + s * s := by
      simp only [dot_add_left, dot_add_right, dot_smul_left, dot_smul_right, dot_one_right,
        dot_one_left, re_add, re_smul, re_one]
      ring
    have e1 : star y * star (x + s • (1 : Tower K k)) = s • star y := by
      rw [← star_mul, hmul, star_smul']
    rw [hmul] at heq
    unfold normInv at heq
    rw [smul_mul_assoc', mul_smul_comm', e1, smul_smul, star_smul', smul_smul, dot_smul_left,
      dot_smul_right, smul_smul] at heq
    have hne' : star y ≠ 0 := fun h => hy (star_eq_zero.1 h)
    have h2 := sub_eq_zero.2 heq
    rw [← sub_smul] at h2
    have hc : (s * (s * dot k y y))⁻¹ * s - (dot k y y)⁻¹ * (dot k (x + s • (1 : Tower K k))
        (x + s • 1))⁻¹ * s = 0 := by
      by_contra hc
      exact hc ((smul_eq_zero.1 h2).resolve_right hne')
    rw [hn] at hna hc
    generalize hN : dot k x x + 2 * s * re k x + s * s = N at hna hc
    have hNs : N = s * s := by
      field_simp at hc
      linear_combination hc
    linear_combination hN + hNs
  by_contra H
  push Not at H
  have h1 := key 1 one_ne_zero (H _ y (hne 1 one_ne_zero) hd)
  have h2 := key (-1) (neg_ne_zero.2 one_ne_zero) (H _ y (hne (-1) (neg_ne_zero.2 one_ne_zero)) hd)
  have h3 : dot k x x = 0 := by
    have : (2 : K) * dot k x x = 0 := by linear_combination h1 + h2
    exact (mul_eq_zero.1 this).resolve_left two_ne_zero
  exact hx (eq_zero_of_dot_self_eq_zero hsq h3)

/-- From level 4 on, over an ordered field, the left inverse property `x⁻¹ (x y) = y` fails for
an element with nonzero norm. -/
theorem exists_normInv_mul_mul_ne (hk : 4 ≤ k) :
    ∃ x y : Tower K k, dot k x x ≠ 0 ∧ normInv x * (x * y) ≠ y := by
  have hsq : ∀ z : K, 0 ≤ z * z := fun z => mul_self_nonneg z
  obtain ⟨x, y, h⟩ := exists_left_alternative_ne (R := K) two_ne_zero k hk
  have hx : x ≠ 0 := by
    rintro rfl
    apply h
    simp
  refine ⟨x, y, dot_self_ne_zero hsq hx, fun h' => h ?_⟩
  have h5 := star_mul_mul_sub_eq x y
  have h6 : star x * (x * y) = dot k x x • y := by
    unfold normInv at h'
    rw [smul_mul_assoc'] at h'
    calc star x * (x * y) = dot k x x • ((dot k x x)⁻¹ • (star x * (x * y))) := by
          rw [smul_smul, mul_inv_cancel₀ (dot_self_ne_zero hsq hx), one_smul]
      _ = dot k x x • y := by rw [h']
  rw [h6, sub_self] at h5
  exact sub_eq_zero.1 h5.symm

/-- Over an ordered field, `(a b)⁻¹ = b⁻¹ a⁻¹` for every `a` and `b` exactly at the levels up
to 3. -/
theorem normInv_mul_iff :
    (∀ a b : Tower K k, normInv (a * b) = normInv b * normInv a) ↔ k ≤ 3 := by
  refine ⟨fun h => ?_, fun hk a b => normInv_mul_of_le_three hk a b⟩
  by_contra hk
  obtain ⟨a, b, -, -, hne⟩ := exists_normInv_mul_ne (K := K) (k := k) (by omega)
  exact hne (h a b)

end Field

end Tower

end CayleyDickson
