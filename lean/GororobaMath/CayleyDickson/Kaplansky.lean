/- SPDX-License-Identifier: Apache-2.0 -/
module

public import GororobaMath.CayleyDickson.TraceForm
public import GororobaMath.CayleyDickson.Associator

/-!
# No idempotents but `0` and `1`, and no nonzero nilpotents, at every level

Convention: the product of `Tower R k` is the Cayley-Dickson product
`(a, b) (c, d) = (a c - star d b, d a + b star c)` of `GororobaMath.CayleyDickson.Basic`, over a
commutative ring `R` with the identity as star; `Tower.dot k x y` is the trace form and
`Tower.re k x` the coordinate of `1` (`GororobaMath.CayleyDickson.AnnihilatorSymmetry`). The
order hypotheses are those of that module: `hsq` for the squares, `IsOrderedAddMonoid` over a
partial order for the sums, and `NoZeroDivisors`.

The quadratic law `x * x = (2 * re x) • x - dot x x • 1` (`Tower.mul_self_eq_smul_sub`) is the only
algebraic input: no step uses alternativity, so the results hold in the sedenions and above,
where the product has zero divisors. `Tower.leftPow x n` is the left-nested power
`x * (x * (... * x))`; its coordinates lie in `R 1 + R x` (power-associativity,
`Tower.associator_span_one_self`).

## Main results

* `Tower.eq_zero_or_eq_one_of_mul_self_eq`: `x * x = x` forces `x = 0` or `x = 1`.
* `Tower.eq_zero_of_leftPow_eq_zero`: a nonzero `x` has no vanishing power, `x ^ n = 0` with
  `n ≠ 0` forces `x = 0`.
-/

@[expose] public section

namespace CayleyDickson

namespace Tower

universe u

section Scalars

variable {R : Type u} [CommRing R] [StarRing R] {k : ℕ}

theorem re_smul (r : R) (x : Tower R k) : re k (r • x) = r * re k x := by
  rw [← dot_one_right, ← dot_one_right, dot_smul_left]

theorem re_one : ∀ k : ℕ, re k (1 : Tower R k) = 1
  | 0 => rfl
  | k + 1 => by rw [one_eq_mk, re_mk, re_one k]

theorem re_zero (k : ℕ) : re k (0 : Tower R k) = 0 := by
  rw [← dot_one_right, dot_zero_left]

theorem dot_one_left (y : Tower R k) : dot k 1 y = re k y := by
  rw [dot_comm, dot_one_right]

end Scalars

section Ordered

variable {R : Type u} [CommRing R] [StarRing R] [TrivialStar R] [PartialOrder R]
  [IsOrderedAddMonoid R] [NoZeroDivisors R] {k : ℕ}

/-- The only idempotents of the tower over an ordered domain are `0` and `1`, at every level. -/
theorem eq_zero_or_eq_one_of_mul_self_eq (hsq : ∀ x : R, 0 ≤ x * x) {x : Tower R k}
    (h : x * x = x) : x = 0 ∨ x = 1 := by
  rw [mul_self_eq_smul_sub, sub_eq_iff_eq_add] at h
  have h1 : (2 * re k x - 1) • x = dot k x x • (1 : Tower R k) := by
    rw [sub_smul, one_smul, h]
    abel
  have hre : (2 * re k x - 1) * re k x = dot k x x := by
    have := congrArg (re k) h1
    rwa [re_smul, re_smul, re_one, mul_one] at this
  have hd : (2 * re k x - 1) * dot k x x = dot k x x * re k x := by
    have := congrArg (fun z => dot k z x) h1
    simpa only [dot_smul_left, dot_one_left] using this
  have h3 : dot k x x * (re k x - 1) = 0 := by linear_combination hd
  rcases mul_eq_zero.1 h3 with hn | ha
  · exact Or.inl (eq_zero_of_dot_self_eq_zero hsq hn)
  · right
    have ha' : re k x = 1 := sub_eq_zero.1 ha
    have hn : dot k x x = 1 := by rw [← hre, ha']; ring
    have h0 : dot k (x - 1) (x - 1) = 0 := by
      simp only [dot_sub_left, dot_sub_right, dot_one_right, dot_one_left, re_sub,
        re_one, ha', hn]
      ring
    exact sub_eq_zero.1 (eq_zero_of_dot_self_eq_zero hsq h0)

/-- The left-nested power `x * (x * (... * x))`. -/
def leftPow (x : Tower R k) : ℕ → Tower R k
  | 0 => 1
  | n + 1 => x * leftPow x n

omit [PartialOrder R] [IsOrderedAddMonoid R] [NoZeroDivisors R] in
/-- Multiplication in `R 1 + R v` for a pure part `v` with `v * v = -(m • 1)`. -/
theorem mul_one_add_smul (r α β m : R) (v : Tower R k) (hvv : v * v = -(m • (1 : Tower R k))) :
    ((r • (1 : Tower R k) + v) * (α • (1 : Tower R k) + β • v)) =
      (r * α - m * β) • (1 : Tower R k) + (r * β + α) • v := by
  simp only [add_mul, mul_add, smul_mul_assoc', mul_smul_comm', one_mul, mul_one, hvv, smul_neg,
    smul_smul]
  module

omit [PartialOrder R] [IsOrderedAddMonoid R] [NoZeroDivisors R] in
/-- A power of `x = r 1 + v` is `α 1 + β v` with `α² + m β² = (r² + m)^n`, where `m = dot v v`. -/
theorem exists_leftPow_eq (r : R) (v : Tower R k) (m : R) (hvv : v * v = -(m • (1 : Tower R k)))
    (n : ℕ) : ∃ α β : R, leftPow (r • (1 : Tower R k) + v) n = α • (1 : Tower R k) + β • v ∧
      α * α + m * (β * β) = (r * r + m) ^ n := by
  induction n with
  | zero => exact ⟨1, 0, by simp [leftPow], by simp⟩
  | succ n ih =>
    obtain ⟨α, β, hp, hn⟩ := ih
    refine ⟨r * α - m * β, r * β + α, ?_, ?_⟩
    · change (r • (1 : Tower R k) + v) * leftPow (r • (1 : Tower R k) + v) n = _
      rw [hp, mul_one_add_smul r α β m v hvv]
    · calc (r * α - m * β) * (r * α - m * β) + m * ((r * β + α) * (r * β + α))
          = (r * r + m) * (α * α + m * (β * β)) := by ring
        _ = (r * r + m) ^ (n + 1) := by rw [hn, pow_succ']

/-- A nonzero element of the tower over an ordered domain has no vanishing power: at every level
`x ^ n = 0` with `n ≠ 0` forces `x = 0`. -/
theorem eq_zero_of_leftPow_eq_zero (hsq : ∀ x : R, 0 ≤ x * x) {x : Tower R k} {n : ℕ} (hn : n ≠ 0)
    (h : leftPow x n = 0) : x = 0 := by
  set r : R := re k x with hr
  set v : Tower R k := x - r • (1 : Tower R k) with hv
  have hx : x = r • (1 : Tower R k) + v := by rw [hv]; abel
  have hvre : re k v = 0 := by rw [hv, re_sub, re_smul, re_one, hr]; ring
  have hvv : v * v = -(dot k v v • (1 : Tower R k)) := by
    rw [mul_self_eq_smul_sub v, hvre, mul_zero, zero_smul, zero_sub]
  obtain ⟨α, β, hp, hpn⟩ := exists_leftPow_eq r v (dot k v v) hvv n
  rw [← hx, h] at hp
  have hα : α = 0 := by
    have := congrArg (re k) hp
    rw [re_zero, re_add, re_smul, re_smul, re_one, hvre] at this
    linear_combination -this
  rw [hα, zero_smul, zero_add] at hp
  have hβ : dot k v v * (β * β) = 0 := by
    have := congrArg (fun z => dot k z z) hp
    simp only [dot_zero_left, dot_smul_left, dot_smul_right] at this
    linear_combination -this
  rw [hα, hβ, mul_zero, zero_add] at hpn
  have hrm : r * r + dot k v v = 0 := pow_eq_zero_iff hn |>.1 hpn.symm
  obtain ⟨hr0, hm0⟩ := (add_eq_zero_iff_of_nonneg (hsq r) (dot_self_nonneg hsq k v)).1 hrm
  have hv0 : v = 0 := eq_zero_of_dot_self_eq_zero hsq hm0
  rw [hx, hv0, mul_self_eq_zero.1 hr0, zero_smul, add_zero]

end Ordered

end Tower

end CayleyDickson
