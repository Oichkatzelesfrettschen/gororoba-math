/- SPDX-License-Identifier: Apache-2.0 -/
module

public import GororobaMath.CayleyDickson.Associator

/-!
# Alternativity and the Moufang identities at levels up to 3, and their failure from level 4

Convention: the product of `Tower R k` is the Cayley-Dickson product
`(a, b) (c, d) = (a c - star d b, d a + b star c)` of `GororobaMath.CayleyDickson.Basic`, the
associator is `associator a b c = (a * b) * c - a * (b * c)` (`Associator.lean`), and `e R k p` is
the basis element of index `p : BitVec k`. The level-3 results read over a commutative ring `R`
with the identity as star, and `Tower R 3` is the octonion algebra with coefficients in `R`; the
levels `0` to `2` follow through the embedding `Tower.lift`. The failure results read over a ring
with a star in which `2 ≠ 0`.

## Main results

* `Tower.left_alternative_three`, `Tower.right_alternative_three`: `x (x y) = (x x) y` and
  `(y x) x = y (x x)` at level 3, by the coordinates of the three-fold double, with no division
  by `2`. `Tower.left_alternative_of_le_three`, `Tower.right_alternative_of_le_three`: the same
  at every level `k ≤ 3`.
* `Tower.moufang_left_three`, `Tower.moufang_middle_three`, `Tower.moufang_right_three`,
  `Tower.flexible_three` and their versions at every level `k ≤ 3`
  (`Tower.moufang_left_of_le_three`, `Tower.bol_left_of_le_three`, ...).
* `Tower.associator_add_swap_left_of_le_three`, `Tower.associator_add_swap_right_of_le_three`,
  `Tower.associator_cyclic_of_le_three`: the associator is alternating at levels up to 3.
* `Tower.exists_left_alternative_ne`, `Tower.exists_right_alternative_ne`,
  `Tower.exists_moufang_left_ne`, `Tower.exists_moufang_middle_ne`,
  `Tower.exists_moufang_right_ne`, `Tower.exists_bol_left_ne`,
  `Tower.exists_associator_swap_left_ne`, `Tower.exists_associator_swap_right_ne`,
  `Tower.exists_associator_cyclic_ne`: at every level `k ≥ 4`, over a ring with a star in which
  `2 ≠ 0`, each law fails. The sedenion witnesses are `associator x x y = 2 e 15` for
  `x = e 1 + e 10`, `y = e 4`, `associator y x x = -2 e 15`, and the basis triple
  `e 1, e 2, e 12` for the middle Moufang identity; `Tower.lift` carries them to every higher
  level.
-/

@[expose] public section

namespace CayleyDickson

namespace Tower

universe u

section Lift

variable {R : Type u} [NonAssocRing R] [StarRing R]

theorem lift_zero (j m : ℕ) : lift (R := R) j m 0 = 0 := by
  induction m with
  | zero => rfl
  | succ m ih =>
    change mk (lift (R := R) j m 0) 0 = 0
    rw [ih]; rfl

theorem lift_sub (j m : ℕ) (x y : Tower R j) :
    lift j m (x - y) = lift j m x - lift j m y := by
  induction m with
  | zero => rfl
  | succ m ih =>
    change mk (lift j m (x - y)) 0 = mk (lift j m x) 0 - mk (lift j m y) 0
    rw [ih]
    exact mk_inj.2 ⟨rfl, (sub_self _).symm⟩

/-- The embedding `lift` carries the associator to the associator. -/
theorem lift_associator (j m : ℕ) (a b c : Tower R j) :
    lift j m (associator a b c) = associator (lift j m a) (lift j m b) (lift j m c) := by
  simp only [associator, lift_sub, lift_mul]

/-- A level embeds into a higher one without changing whether an associator vanishes. -/
theorem associator_lift_eq_zero_iff (j m : ℕ) (a b c : Tower R j) :
    associator (lift j m a) (lift j m b) (lift j m c) = 0 ↔ associator a b c = 0 := by
  rw [← lift_associator, ← lift_zero j m]
  exact (lift_injective j m).eq_iff

theorem mk_add_mk {k : ℕ} (a b c d : Tower R k) : mk a b + mk c d = mk (a + c) (b + d) := rfl

theorem mk_sub_mk {k : ℕ} (a b c d : Tower R k) : mk a b - mk c d = mk (a - c) (b - d) := rfl

end Lift

section Coordinates

variable {R : Type u} [CommRing R] [StarRing R]

omit [CommRing R] [StarRing R] in
/-- A level-3 element has eight coordinates in `R`. -/
theorem exists_coordinates_three (x : Tower R 3) :
    ∃ a0 a1 a2 a3 a4 a5 a6 a7 : R,
      x = mk (mk (ofPair a0 a1) (ofPair a2 a3)) (mk (ofPair a4 a5) (ofPair a6 a7)) := by
  obtain ⟨p, q⟩ := x
  obtain ⟨p0, p1⟩ := p
  obtain ⟨q0, q1⟩ := q
  obtain ⟨a0, a1, rfl⟩ := exists_ofPair p0
  obtain ⟨a2, a3, rfl⟩ := exists_ofPair p1
  obtain ⟨a4, a5, rfl⟩ := exists_ofPair q0
  obtain ⟨a6, a7, rfl⟩ := exists_ofPair q1
  exact ⟨a0, a1, a2, a3, a4, a5, a6, a7, rfl⟩

end Coordinates

section LevelThree

variable {R : Type u} [CommRing R] [StarRing R] [TrivialStar R]

/-- Flexible law at level 3. -/
theorem flexible_three (x y : Tower R 3) : x * y * x = x * (y * x) := by
  obtain ⟨a0, a1, a2, a3, a4, a5, a6, a7, rfl⟩ := exists_coordinates_three x
  obtain ⟨b0, b1, b2, b3, b4, b5, b6, b7, rfl⟩ := exists_coordinates_three y
  simp only [mk_mul_mk, star_mk, ofPair_star, ofPair_mul, mk_sub_mk, mk_add_mk, ofPair_sub,
    ofPair_add, ofPair_neg, mk_inj, ofPair_inj]
  refine ⟨⟨⟨?_, ?_⟩, ?_, ?_⟩, ⟨?_, ?_⟩, ?_, ?_⟩ <;> ring

/-- Left alternative law at level 3. -/
theorem left_alternative_three (x y : Tower R 3) : x * (x * y) = x * x * y := by
  obtain ⟨a0, a1, a2, a3, a4, a5, a6, a7, rfl⟩ := exists_coordinates_three x
  obtain ⟨b0, b1, b2, b3, b4, b5, b6, b7, rfl⟩ := exists_coordinates_three y
  simp only [mk_mul_mk, star_mk, ofPair_star, ofPair_mul, mk_sub_mk, mk_add_mk, ofPair_sub,
    ofPair_add, ofPair_neg, mk_inj, ofPair_inj]
  refine ⟨⟨⟨?_, ?_⟩, ?_, ?_⟩, ⟨?_, ?_⟩, ?_, ?_⟩ <;> ring

/-- Right alternative law at level 3. -/
theorem right_alternative_three (x y : Tower R 3) : y * x * x = y * (x * x) := by
  obtain ⟨a0, a1, a2, a3, a4, a5, a6, a7, rfl⟩ := exists_coordinates_three x
  obtain ⟨b0, b1, b2, b3, b4, b5, b6, b7, rfl⟩ := exists_coordinates_three y
  simp only [mk_mul_mk, star_mk, ofPair_star, ofPair_mul, mk_sub_mk, mk_add_mk, ofPair_sub,
    ofPair_add, ofPair_neg, mk_inj, ofPair_inj]
  refine ⟨⟨⟨?_, ?_⟩, ?_, ?_⟩, ⟨?_, ?_⟩, ?_, ?_⟩ <;> ring

/-- Left Moufang identity at level 3. -/
theorem moufang_left_three (x y z : Tower R 3) : x * (y * (x * z)) = x * y * x * z := by
  obtain ⟨a0, a1, a2, a3, a4, a5, a6, a7, rfl⟩ := exists_coordinates_three x
  obtain ⟨b0, b1, b2, b3, b4, b5, b6, b7, rfl⟩ := exists_coordinates_three y
  obtain ⟨c0, c1, c2, c3, c4, c5, c6, c7, rfl⟩ := exists_coordinates_three z
  simp only [mk_mul_mk, star_mk, ofPair_star, ofPair_mul, mk_sub_mk, mk_add_mk, ofPair_sub,
    ofPair_add, ofPair_neg, mk_inj, ofPair_inj]
  refine ⟨⟨⟨?_, ?_⟩, ?_, ?_⟩, ⟨?_, ?_⟩, ?_, ?_⟩ <;> ring

/-- Middle Moufang identity at level 3. -/
theorem moufang_middle_three (x y z : Tower R 3) : x * y * (z * x) = x * (y * z * x) := by
  obtain ⟨a0, a1, a2, a3, a4, a5, a6, a7, rfl⟩ := exists_coordinates_three x
  obtain ⟨b0, b1, b2, b3, b4, b5, b6, b7, rfl⟩ := exists_coordinates_three y
  obtain ⟨c0, c1, c2, c3, c4, c5, c6, c7, rfl⟩ := exists_coordinates_three z
  simp only [mk_mul_mk, star_mk, ofPair_star, ofPair_mul, mk_sub_mk, mk_add_mk, ofPair_sub,
    ofPair_add, ofPair_neg, mk_inj, ofPair_inj]
  refine ⟨⟨⟨?_, ?_⟩, ?_, ?_⟩, ⟨?_, ?_⟩, ?_, ?_⟩ <;> ring

/-- Right Moufang identity at level 3. -/
theorem moufang_right_three (x y z : Tower R 3) : x * y * z * y = x * (y * (z * y)) := by
  obtain ⟨a0, a1, a2, a3, a4, a5, a6, a7, rfl⟩ := exists_coordinates_three x
  obtain ⟨b0, b1, b2, b3, b4, b5, b6, b7, rfl⟩ := exists_coordinates_three y
  obtain ⟨c0, c1, c2, c3, c4, c5, c6, c7, rfl⟩ := exists_coordinates_three z
  simp only [mk_mul_mk, star_mk, ofPair_star, ofPair_mul, mk_sub_mk, mk_add_mk, ofPair_sub,
    ofPair_add, ofPair_neg, mk_inj, ofPair_inj]
  refine ⟨⟨⟨?_, ?_⟩, ?_, ?_⟩, ⟨?_, ?_⟩, ?_, ?_⟩ <;> ring

/-- Left alternative law at every level `k ≤ 3`. -/
theorem left_alternative_of_le_three {k : ℕ} (hk : k ≤ 3) (x y : Tower R k) :
    x * (x * y) = x * x * y := by
  interval_cases k
  · apply lift_injective 0 3
    simp only [lift_mul]
    exact left_alternative_three _ _
  · apply lift_injective 1 2
    simp only [lift_mul]
    exact left_alternative_three _ _
  · apply lift_injective 2 1
    simp only [lift_mul]
    exact left_alternative_three _ _
  · exact left_alternative_three x y

/-- Right alternative law at every level `k ≤ 3`. -/
theorem right_alternative_of_le_three {k : ℕ} (hk : k ≤ 3) (x y : Tower R k) :
    y * x * x = y * (x * x) := by
  interval_cases k
  · apply lift_injective 0 3
    simp only [lift_mul]
    exact right_alternative_three _ _
  · apply lift_injective 1 2
    simp only [lift_mul]
    exact right_alternative_three _ _
  · apply lift_injective 2 1
    simp only [lift_mul]
    exact right_alternative_three _ _
  · exact right_alternative_three x y

/-- Flexible law at every level `k ≤ 3`. -/
theorem flexible_of_le_three {k : ℕ} (hk : k ≤ 3) (x y : Tower R k) :
    x * y * x = x * (y * x) := by
  interval_cases k
  · apply lift_injective 0 3
    simp only [lift_mul]
    exact flexible_three _ _
  · apply lift_injective 1 2
    simp only [lift_mul]
    exact flexible_three _ _
  · apply lift_injective 2 1
    simp only [lift_mul]
    exact flexible_three _ _
  · exact flexible_three x y

/-- Left Moufang identity at every level `k ≤ 3`. -/
theorem moufang_left_of_le_three {k : ℕ} (hk : k ≤ 3) (x y z : Tower R k) :
    x * (y * (x * z)) = x * y * x * z := by
  interval_cases k
  · apply lift_injective 0 3
    simp only [lift_mul]
    exact moufang_left_three _ _ _
  · apply lift_injective 1 2
    simp only [lift_mul]
    exact moufang_left_three _ _ _
  · apply lift_injective 2 1
    simp only [lift_mul]
    exact moufang_left_three _ _ _
  · exact moufang_left_three x y z

/-- Middle Moufang identity at every level `k ≤ 3`. -/
theorem moufang_middle_of_le_three {k : ℕ} (hk : k ≤ 3) (x y z : Tower R k) :
    x * y * (z * x) = x * (y * z * x) := by
  interval_cases k
  · apply lift_injective 0 3
    simp only [lift_mul]
    exact moufang_middle_three _ _ _
  · apply lift_injective 1 2
    simp only [lift_mul]
    exact moufang_middle_three _ _ _
  · apply lift_injective 2 1
    simp only [lift_mul]
    exact moufang_middle_three _ _ _
  · exact moufang_middle_three x y z

/-- Right Moufang identity at every level `k ≤ 3`. -/
theorem moufang_right_of_le_three {k : ℕ} (hk : k ≤ 3) (x y z : Tower R k) :
    x * y * z * y = x * (y * (z * y)) := by
  interval_cases k
  · apply lift_injective 0 3
    simp only [lift_mul]
    exact moufang_right_three _ _ _
  · apply lift_injective 1 2
    simp only [lift_mul]
    exact moufang_right_three _ _ _
  · apply lift_injective 2 1
    simp only [lift_mul]
    exact moufang_right_three _ _ _
  · exact moufang_right_three x y z

end LevelThree

section Basis

variable {R : Type u} [NonAssocRing R] [StarRing R]

/-- The integer coefficient of the associator of three basis elements, in the signs of
`Tower.sign`. -/
def assocCoeff (k : ℕ) (p q r : BitVec k) : ℤ :=
  sign k p q * sign k (p ^^^ q) r - sign k q r * sign k p (q ^^^ r)

/-- The associator of three basis elements is an integer multiple of a basis element. -/
theorem associator_e_e_e (k : ℕ) (p q r : BitVec k) :
    associator (e R k p) (e R k q) (e R k r) = assocCoeff k p q r • e R k (p ^^^ q ^^^ r) := by
  unfold associator assocCoeff
  simp only [e_mul_e_sign, smul_mul_assoc, mul_smul_comm, smul_smul, BitVec.xor_assoc, sub_smul]

end Basis

section Failure

variable {R : Type u} [NonAssocRing R] [StarRing R]

/-- Over a ring with `2 ≠ 0`, twice a basis element is not zero. -/
theorem two_zsmul_e_ne_zero (h2 : (2 : R) ≠ 0) (k : ℕ) (p : BitVec k) :
    (2 : ℤ) • e R k p ≠ 0 := by
  intro h
  rw [two_zsmul] at h
  exact e_ne_neg_e h2 k p (eq_neg_of_add_eq_zero_left h)

/-- The associator `x x y` of the sedenions, for `x = e 1 + e 10` and `y = e 4`, is
`2 e 15`. -/
theorem associator_witness_left :
    associator (e R 4 1#4 + e R 4 10#4) (e R 4 1#4 + e R 4 10#4) (e R 4 4#4) =
      (2 : ℤ) • e R 4 15#4 := by
  simp only [associator_add_left, associator_add_mid, associator_e_e_e]
  have h1 : assocCoeff 4 1#4 1#4 4#4 = 0 := by decide
  have h2 : assocCoeff 4 1#4 10#4 4#4 = 2 := by decide
  have h3 : assocCoeff 4 10#4 1#4 4#4 = 0 := by decide
  have h4 : assocCoeff 4 10#4 10#4 4#4 = 0 := by decide
  have hx : (1#4 ^^^ 10#4 ^^^ 4#4) = 15#4 := by decide
  have hx2 : (10#4 ^^^ 1#4 ^^^ 4#4) = 15#4 := by decide
  have hx3 : (1#4 ^^^ 1#4 ^^^ 4#4) = 4#4 := by decide
  have hx4 : (10#4 ^^^ 10#4 ^^^ 4#4) = 4#4 := by decide
  rw [h1, h2, h3, h4, hx, hx2, hx3, hx4]
  simp only [zero_smul, zero_add, add_zero]

/-- The associator `y x x` of the sedenions, for `x = e 1 + e 10` and `y = e 4`, is
`-2 e 15`. -/
theorem associator_witness_right :
    associator (e R 4 4#4) (e R 4 1#4 + e R 4 10#4) (e R 4 1#4 + e R 4 10#4) =
      (-2 : ℤ) • e R 4 15#4 := by
  simp only [associator_add_right, associator_add_mid, associator_e_e_e]
  have h1 : assocCoeff 4 4#4 1#4 1#4 = 0 := by decide
  have h2 : assocCoeff 4 4#4 1#4 10#4 = 0 := by decide
  have h3 : assocCoeff 4 4#4 10#4 1#4 = -2 := by decide
  have h4 : assocCoeff 4 4#4 10#4 10#4 = 0 := by decide
  have hx : (4#4 ^^^ 1#4 ^^^ 1#4) = 4#4 := by decide
  have hx2 : (4#4 ^^^ 1#4 ^^^ 10#4) = 15#4 := by decide
  have hx3 : (4#4 ^^^ 10#4 ^^^ 1#4) = 15#4 := by decide
  have hx4 : (4#4 ^^^ 10#4 ^^^ 10#4) = 4#4 := by decide
  rw [h1, h2, h3, h4, hx, hx2, hx3, hx4]
  simp only [zero_smul, zero_add, add_zero]

end Failure

section Middle

variable {R : Type u} [NonAssocRing R] [StarRing R]

/-- A basis triple of the sedenions that violates the middle Moufang identity:
`(e 1 * e 2) * (e 12 * e 1) = e 14` while `e 1 * ((e 2 * e 12) * e 1) = -e 14`. -/
theorem moufang_middle_witness (h2 : (2 : R) ≠ 0) :
    e R 4 1#4 * e R 4 2#4 * (e R 4 12#4 * e R 4 1#4) ≠
      e R 4 1#4 * (e R 4 2#4 * e R 4 12#4 * e R 4 1#4) := by
  simp only [e_mul_e_sign, smul_mul_assoc, mul_smul_comm, smul_smul]
  have hA : (1#4 ^^^ 2#4 ^^^ (12#4 ^^^ 1#4)) = 14#4 := by decide
  have hB : (1#4 ^^^ (2#4 ^^^ 12#4 ^^^ 1#4)) = 14#4 := by decide
  have h1 : sign 4 12#4 1#4 * (sign 4 1#4 2#4 * sign 4 (1#4 ^^^ 2#4) (12#4 ^^^ 1#4)) = 1 := by
    decide
  have h2' : sign 4 2#4 12#4 * sign 4 (2#4 ^^^ 12#4) 1#4 * sign 4 (1#4) (2#4 ^^^ 12#4 ^^^ 1#4)
      = -1 := by decide
  rw [hA, hB, h1, h2', one_smul, neg_one_zsmul]
  exact e_ne_neg_e h2 4 14#4

end Middle

section Polarization

variable {A : Type*} [NonAssocRing A]

/-- If `x x y` always vanishes, the associator is skew in its first two slots. -/
theorem associator_add_swap_left_of_self (h : ∀ x y : A, associator x x y = 0) (x y z : A) :
    associator x y z + associator y x z = 0 := by
  have := h (x + y) z
  rw [associator_add_left, associator_add_mid, associator_add_mid, h, h] at this
  simpa only [zero_add, add_zero] using this

/-- If `x y y` always vanishes, the associator is skew in its last two slots. -/
theorem associator_add_swap_right_of_self (h : ∀ x y : A, associator x y y = 0) (x y z : A) :
    associator x y z + associator x z y = 0 := by
  have := h x (y + z)
  rw [associator_add_mid, associator_add_right, associator_add_right, h, h] at this
  simpa only [zero_add, add_zero] using this

end Polarization

section LevelThreeAssociator

variable {R : Type u} [CommRing R] [StarRing R] [TrivialStar R] {k : ℕ}

theorem associator_self_left_of_le_three (hk : k ≤ 3) (x y : Tower R k) :
    associator x x y = 0 :=
  sub_eq_zero.2 (left_alternative_of_le_three hk x y).symm

theorem associator_self_right_of_le_three (hk : k ≤ 3) (x y : Tower R k) :
    associator x y y = 0 :=
  sub_eq_zero.2 (right_alternative_of_le_three hk y x)

/-- The associator of levels up to 3 is skew in its first two slots. -/
theorem associator_add_swap_left_of_le_three (hk : k ≤ 3) (x y z : Tower R k) :
    associator x y z + associator y x z = 0 :=
  associator_add_swap_left_of_self (associator_self_left_of_le_three hk) x y z

/-- The associator of levels up to 3 is skew in its last two slots. -/
theorem associator_add_swap_right_of_le_three (hk : k ≤ 3) (x y z : Tower R k) :
    associator x y z + associator x z y = 0 :=
  associator_add_swap_right_of_self (associator_self_right_of_le_three hk) x y z

/-- The associator of levels up to 3 is invariant under a cyclic permutation. -/
theorem associator_cyclic_of_le_three (hk : k ≤ 3) (x y z : Tower R k) :
    associator x y z = associator y z x :=
  (eq_neg_of_add_eq_zero_left (associator_add_swap_left_of_le_three hk x y z)).trans
    (neg_eq_of_add_eq_zero_right (associator_add_swap_right_of_le_three hk y x z))

/-- The Bol form of the left Moufang identity at every level `k ≤ 3`. -/
theorem bol_left_of_le_three (hk : k ≤ 3) (x y z : Tower R k) :
    x * (y * (x * z)) = x * (y * x) * z := by
  rw [← flexible_of_le_three hk]
  exact moufang_left_of_le_three hk x y z

end LevelThreeAssociator

section LiftFailure

variable {R : Type u} [NonAssocRing R] [StarRing R]

theorem lift_add (j m : ℕ) (x y : Tower R j) : lift j m (x + y) = lift j m x + lift j m y := by
  induction m with
  | zero => rfl
  | succ m ih =>
    change mk (lift j m (x + y)) 0 = mk (lift j m x) 0 + mk (lift j m y) 0
    rw [ih]
    exact mk_inj.2 ⟨rfl, (add_zero _).symm⟩

/-- At every level `k ≥ 4`, over a ring with `2 ≠ 0`, the left alternative law fails. -/
theorem exists_left_alternative_ne (h2 : (2 : R) ≠ 0) (k : ℕ) (hk : 4 ≤ k) :
    ∃ x y : Tower R k, x * x * y ≠ x * (x * y) := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le hk
  refine ⟨lift 4 m (e R 4 1#4 + e R 4 10#4), lift 4 m (e R 4 4#4), ?_⟩
  simp only [← lift_mul]
  intro h
  have h4 := lift_injective 4 m h
  have h5 := associator_witness_left (R := R)
  unfold associator at h5
  rw [h4, sub_self] at h5
  exact two_zsmul_e_ne_zero h2 4 15#4 h5.symm

/-- At every level `k ≥ 4`, over a ring with `2 ≠ 0`, the right alternative law fails. -/
theorem exists_right_alternative_ne (h2 : (2 : R) ≠ 0) (k : ℕ) (hk : 4 ≤ k) :
    ∃ x y : Tower R k, x * y * y ≠ x * (y * y) := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le hk
  refine ⟨lift 4 m (e R 4 4#4), lift 4 m (e R 4 1#4 + e R 4 10#4), ?_⟩
  simp only [← lift_mul]
  intro h
  have h4 := lift_injective 4 m h
  have h5 := associator_witness_right (R := R)
  unfold associator at h5
  rw [h4, sub_self] at h5
  have := two_zsmul_e_ne_zero h2 4 15#4
  apply this
  rw [neg_smul] at h5
  simpa using h5.symm

/-- At every level `k ≥ 4`, over a ring with `2 ≠ 0`, the middle Moufang identity fails. -/
theorem exists_moufang_middle_ne (h2 : (2 : R) ≠ 0) (k : ℕ) (hk : 4 ≤ k) :
    ∃ x y z : Tower R k, x * y * (z * x) ≠ x * (y * z * x) := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le hk
  refine ⟨lift 4 m (e R 4 1#4), lift 4 m (e R 4 2#4), lift 4 m (e R 4 12#4), ?_⟩
  simp only [← lift_mul]
  intro h
  exact moufang_middle_witness h2 (lift_injective 4 m h)

/-- At every level `k ≥ 4`, over a ring with `2 ≠ 0`, the left Moufang identity fails. -/
theorem exists_moufang_left_ne (h2 : (2 : R) ≠ 0) (k : ℕ) (hk : 4 ≤ k) :
    ∃ x y z : Tower R k, x * (y * (x * z)) ≠ x * y * x * z := by
  obtain ⟨x, z, h⟩ := exists_left_alternative_ne h2 k hk
  refine ⟨x, 1, z, ?_⟩
  intro hm
  simp only [one_mul, mul_one] at hm
  exact h hm.symm

/-- At every level `k ≥ 4`, over a ring with `2 ≠ 0`, the right Moufang identity fails. -/
theorem exists_moufang_right_ne (h2 : (2 : R) ≠ 0) (k : ℕ) (hk : 4 ≤ k) :
    ∃ x y z : Tower R k, x * y * z * y ≠ x * (y * (z * y)) := by
  obtain ⟨x, y, h⟩ := exists_right_alternative_ne h2 k hk
  refine ⟨x, y, 1, ?_⟩
  intro hm
  simp only [one_mul, mul_one] at hm
  exact h hm

/-- At every level `k ≥ 4`, over a ring with `2 ≠ 0`, the associator is not skew in its first
two slots: `A(e 1, e 10, e 4) + A(e 10, e 1, e 4) = 2 e 15`. -/
theorem exists_associator_swap_left_ne (h2 : (2 : R) ≠ 0) (k : ℕ) (hk : 4 ≤ k) :
    ∃ x y z : Tower R k, associator x y z + associator y x z ≠ 0 := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le hk
  refine ⟨lift 4 m (e R 4 1#4), lift 4 m (e R 4 10#4), lift 4 m (e R 4 4#4), ?_⟩
  rw [← lift_associator, ← lift_associator, ← lift_add]
  intro h
  have h4 := lift_injective 4 m (h.trans (lift_zero 4 m).symm)
  rw [associator_e_e_e, associator_e_e_e] at h4
  have h5 : assocCoeff 4 1#4 10#4 4#4 = 2 := by decide
  have h6 : assocCoeff 4 10#4 1#4 4#4 = 0 := by decide
  have hx : (1#4 ^^^ 10#4 ^^^ 4#4) = 15#4 := by decide
  have hx2 : (10#4 ^^^ 1#4 ^^^ 4#4) = 15#4 := by decide
  rw [h5, h6, hx, hx2, zero_smul, add_zero] at h4
  exact two_zsmul_e_ne_zero h2 4 15#4 h4

/-- At every level `k ≥ 4`, over a ring with `2 ≠ 0`, the associator is not skew in its last
two slots. -/
theorem exists_associator_swap_right_ne (h2 : (2 : R) ≠ 0) (k : ℕ) (hk : 4 ≤ k) :
    ∃ x y z : Tower R k, associator x y z + associator x z y ≠ 0 := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le hk
  refine ⟨lift 4 m (e R 4 4#4), lift 4 m (e R 4 1#4), lift 4 m (e R 4 10#4), ?_⟩
  rw [← lift_associator, ← lift_associator, ← lift_add]
  intro h
  have h4 := lift_injective 4 m (h.trans (lift_zero 4 m).symm)
  rw [associator_e_e_e, associator_e_e_e] at h4
  have h5 : assocCoeff 4 4#4 1#4 10#4 = 0 := by decide
  have h6 : assocCoeff 4 4#4 10#4 1#4 = -2 := by decide
  have hx : (4#4 ^^^ 1#4 ^^^ 10#4) = 15#4 := by decide
  have hx2 : (4#4 ^^^ 10#4 ^^^ 1#4) = 15#4 := by decide
  rw [h5, h6, hx, hx2, zero_smul, zero_add, neg_smul] at h4
  exact two_zsmul_e_ne_zero h2 4 15#4 (neg_eq_zero.1 h4)

/-- At every level `k ≥ 4`, over a ring with `2 ≠ 0`, the Bol form of the left Moufang
identity fails. -/
theorem exists_bol_left_ne (h2 : (2 : R) ≠ 0) (k : ℕ) (hk : 4 ≤ k) :
    ∃ x y z : Tower R k, x * (y * (x * z)) ≠ x * (y * x) * z := by
  obtain ⟨x, z, h⟩ := exists_left_alternative_ne h2 k hk
  refine ⟨x, 1, z, ?_⟩
  intro hm
  simp only [one_mul] at hm
  exact h hm.symm

/-- At every level `k ≥ 4`, over a ring with `2 ≠ 0`, the associator is not invariant under a
cyclic permutation: `A(e 1, e 10, e 4) = 2 e 15` while `A(e 10, e 4, e 1) = 0`. -/
theorem exists_associator_cyclic_ne (h2 : (2 : R) ≠ 0) (k : ℕ) (hk : 4 ≤ k) :
    ∃ x y z : Tower R k, associator x y z ≠ associator y z x := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le hk
  refine ⟨lift 4 m (e R 4 1#4), lift 4 m (e R 4 10#4), lift 4 m (e R 4 4#4), ?_⟩
  rw [← lift_associator, ← lift_associator]
  intro h
  have h4 := lift_injective 4 m h
  rw [associator_e_e_e, associator_e_e_e] at h4
  have h5 : assocCoeff 4 1#4 10#4 4#4 = 2 := by decide
  have h6 : assocCoeff 4 10#4 4#4 1#4 = 0 := by decide
  have hx : (1#4 ^^^ 10#4 ^^^ 4#4) = 15#4 := by decide
  have hx2 : (10#4 ^^^ 4#4 ^^^ 1#4) = 15#4 := by decide
  rw [h5, h6, hx, hx2, zero_smul] at h4
  exact two_zsmul_e_ne_zero h2 4 15#4 h4

end LiftFailure

end Tower

end CayleyDickson
