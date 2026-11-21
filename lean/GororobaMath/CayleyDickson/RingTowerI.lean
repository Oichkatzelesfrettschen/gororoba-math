/- SPDX-License-Identifier: Apache-2.0 -/
module

public import GororobaMath.CayleyDickson.TraceForm
public import GororobaMath.CayleyDickson.NonAssociative

/-!
# The kernel swap and a square root of minus one

Convention: `Tower R k` is the tower of `GororobaMath.CayleyDickson.Tower` over a commutative
ring `R` whose star is the identity, with the product
`(a, b) (c, d) = (a c - star d b, d a + b star c)`. `Tower.ofPair a b` is the level-1 element
`(a, b)` with coordinates in `R`, and `i : R` satisfies `i * i = -1`. The kernel swap at level
`k` is `a * z = 0 → z * a = 0` for all `a z`.

At level 2 the pure element `N = (e₁ + i e₂)` and `W = -1 - i e₃` satisfy `N * W = 0` and
`W * N = -2 N`. The embedding `x ↦ (x, 0)` carries them to level `k + 2` (`Tower.liftTwo`, an
induction on `k`, since `k + 2` unfolds to `(k + 1) + 1` by `rfl` while `Tower.lift 2 k` lands in
`Tower R (2 + k)`). The swap then forces `-2 = 0`.

## Main results

* `Tower.pure_kernel_swap_two_eq_zero`: the Rocq original is `pure_kernel_swap_two_zero` of the
  functor `RingTowerI` in `rocq/quantum/CdTowerRing.v`.
* `Tower.kernel_swap_iff_two_eq_zero`: the Rocq `kernel_swap_iff_two_zero` of the same functor.
* `Tower.zmod5_not_pure_kernel_swap`: the Rocq `mod5_kernel_swap_fails` of
  `rocq/quantum/CdTowerRing.v`, over `ZMod 5` with the identity as star and `i = 2`; the star
  instances are arguments of the theorem.
-/

@[expose] public section

namespace CayleyDickson

namespace Tower

universe u

variable {R : Type u} [CommRing R] [StarRing R]

/-- The level-1 element `(a, b)` with coordinates `a b : R`. -/
def ofPair (a b : R) : Tower R 1 := mk (show Tower R 0 from a) (show Tower R 0 from b)

theorem ofPair_add (a b c d : R) : ofPair a b + ofPair c d = ofPair (a + c) (b + d) := rfl

theorem ofPair_sub (a b c d : R) : ofPair a b - ofPair c d = ofPair (a - c) (b - d) := rfl

theorem ofPair_neg (a b : R) : -ofPair a b = ofPair (-a) (-b) := rfl

theorem ofPair_zero : ofPair (0 : R) 0 = 0 := rfl

omit [CommRing R] [StarRing R] in
theorem ofPair_inj {a b c d : R} : ofPair a b = ofPair c d ↔ a = c ∧ b = d := mk_inj

/-- The embedding `x ↦ (x, 0)` of level `2` into level `k + 2`. -/
def liftTwo : (k : ℕ) → Tower R 2 → Tower R (k + 2)
  | 0, x => x
  | k + 1, x => mk (liftTwo k x) 0

theorem liftTwo_mul : ∀ (k : ℕ) (x y : Tower R 2), liftTwo k (x * y) = liftTwo k x * liftTwo k y
  | 0, _, _ => rfl
  | k + 1, x, y => by
    change mk (liftTwo k (x * y)) 0 = mk (liftTwo k x) 0 * mk (liftTwo k y) 0
    rw [mk_zero_mul_mk_zero, liftTwo_mul k]

theorem liftTwo_star : ∀ (k : ℕ) (x : Tower R 2), liftTwo k (star x) = star (liftTwo k x)
  | 0, _ => rfl
  | k + 1, x => by
    change mk (liftTwo k (star x)) 0 = star (mk (liftTwo k x) 0)
    rw [star_mk, liftTwo_star k, neg_zero]

theorem liftTwo_neg : ∀ (k : ℕ) (x : Tower R 2), liftTwo k (-x) = -liftTwo k x
  | 0, _ => rfl
  | k + 1, x => by
    change mk (liftTwo k (-x)) 0 = -mk (liftTwo k x) 0
    rw [neg_mk, liftTwo_neg k, neg_zero]

theorem liftTwo_eq_zero_iff : ∀ (k : ℕ) (x : Tower R 2), liftTwo k x = 0 ↔ x = 0
  | 0, _ => Iff.rfl
  | k + 1, x => by
    change mk (liftTwo k x) 0 = 0 ↔ x = 0
    rw [zero_eq_mk (k + 2), mk_inj, liftTwo_eq_zero_iff k]
    simp

section Trivial

variable [TrivialStar R]

omit [TrivialStar R] in
theorem ofPair_smul (r a b : R) : r • ofPair a b = ofPair (r * a) (r * b) := rfl

theorem ofPair_star (a b : R) : star (ofPair a b) = ofPair a (-b) := by
  change mk (star (show Tower R 0 from a)) (-(show Tower R 0 from b)) = _
  rw [show star (show Tower R 0 from a) = show Tower R 0 from a from star_trivial a]
  rfl

theorem ofPair_mul (a b c d : R) :
    ofPair a b * ofPair c d = ofPair (a * c - d * b) (d * a + b * c) := by
  change mk (show Tower R 0 from a) (show Tower R 0 from b) *
    mk (show Tower R 0 from c) (show Tower R 0 from d) = _
  rw [mk_mul_mk, show star (show Tower R 0 from d) = show Tower R 0 from d from star_trivial d,
    show star (show Tower R 0 from c) = show Tower R 0 from c from star_trivial c]
  rfl

omit [TrivialStar R] in
theorem liftTwo_smul : ∀ (k : ℕ) (r : R) (x : Tower R 2), liftTwo k (r • x) = r • liftTwo k x
  | 0, _, _ => rfl
  | k + 1, r, x => by
    change mk (liftTwo k (r • x)) 0 = r • mk (liftTwo k x) 0
    rw [smul_mk, liftTwo_smul k, smul_zero]

variable (i : R)

/-- The pure nilpotent `e₁ + i e₂` of level 2. -/
def nilpotent2 : Tower R 2 := mk (ofPair 0 1) (ofPair i 0)

/-- The witness `-1 - i e₃` of level 2. -/
def witness2 : Tower R 2 := mk (ofPair (-1) 0) (ofPair 0 (-i))

variable {i}

theorem star_nilpotent2 : star (nilpotent2 i) = -nilpotent2 i := by
  simp only [nilpotent2, star_mk, neg_mk, ofPair_star, ofPair_neg, neg_zero]

theorem nilpotent2_mul_witness2 (hi : i * i = -1) : nilpotent2 i * witness2 i = 0 := by
  simp only [nilpotent2, witness2, mk_mul_mk, ofPair_star, ofPair_mul, ofPair_sub, ofPair_add]
  rw [zero_eq_mk, ← ofPair_zero, mk_inj, ofPair_inj, ofPair_inj]
  exact ⟨⟨by ring, by linear_combination (-1 : R) * hi⟩, by ring, by ring⟩

theorem witness2_mul_nilpotent2 (hi : i * i = -1) :
    witness2 i * nilpotent2 i = (-2 : R) • nilpotent2 i := by
  simp only [nilpotent2, witness2, mk_mul_mk, ofPair_star, ofPair_mul, ofPair_sub, ofPair_add,
    smul_mk, ofPair_smul, mk_inj, ofPair_inj]
  exact ⟨⟨by ring, by linear_combination hi⟩, by ring, by ring⟩

/-- Over a commutative ring with `i * i = -1`, if the kernel swap holds for every pure element at
level `k + 2`, then `2 = 0`. The Rocq original is `pure_kernel_swap_two_zero` of the functor
`RingTowerI` in `rocq/quantum/CdTowerRing.v`. -/
theorem pure_kernel_swap_two_eq_zero (hi : i * i = -1) (k : ℕ)
    (h : ∀ a z : Tower R (k + 2), star a = -a → a * z = 0 → z * a = 0) : (2 : R) = 0 := by
  have hpure : star (liftTwo k (nilpotent2 i)) = -liftTwo k (nilpotent2 i) := by
    rw [← liftTwo_star, star_nilpotent2, liftTwo_neg]
  have h0 := h _ _ hpure (by
    rw [← liftTwo_mul, nilpotent2_mul_witness2 hi]
    exact (liftTwo_eq_zero_iff k 0).2 rfl)
  rw [← liftTwo_mul, witness2_mul_nilpotent2 hi] at h0
  have h1 := (liftTwo_eq_zero_iff k _).1 h0
  simp only [nilpotent2, smul_mk, ofPair_smul, zero_eq_mk, mk_inj] at h1
  have h3 : ofPair (-2 * 0) (-2 * 1) = ofPair (0 : R) 0 := h1.1
  linear_combination -(ofPair_inj.1 h3).2

/-- Over a commutative ring with `i * i = -1`, the kernel swap holds at level `k + 2` exactly when
`2 = 0`. The Rocq original is `kernel_swap_iff_two_zero` of the functor `RingTowerI` in
`rocq/quantum/CdTowerRing.v`. -/
theorem kernel_swap_iff_two_eq_zero (hi : i * i = -1) (k : ℕ) :
    (∀ a z : Tower R (k + 2), a * z = 0 → z * a = 0) ↔ (2 : R) = 0 :=
  ⟨fun h => pure_kernel_swap_two_eq_zero hi k fun a z _ => h a z, fun h2 a z hz => by
    rw [mul_comm_of_two_eq_zero h2]
    exact hz⟩

end Trivial

section ZMod5

/-- Over `ZMod 5` with the identity as star and `i = 2`, the kernel swap fails for pure elements
at every level `k + 2`. The Rocq original is `mod5_kernel_swap_fails` of
`rocq/quantum/CdTowerRing.v`. The star of `ZMod 5` enters as instance arguments, and
`TrivialStar` makes it the identity, so the tower is that of the Rocq functor and not of a
Gaussian conjugation; `starRingOfComm` with `⟨fun _ => rfl⟩` supplies both at a call site. -/
theorem zmod5_not_pure_kernel_swap [StarRing (ZMod 5)] [TrivialStar (ZMod 5)] (k : ℕ) :
    ¬ ∀ a z : Tower (ZMod 5) (k + 2), star a = -a → a * z = 0 → z * a = 0 := fun h =>
  absurd (pure_kernel_swap_two_eq_zero (i := (2 : ZMod 5)) (by decide) k h) (by decide)

end ZMod5

end Tower

end CayleyDickson
