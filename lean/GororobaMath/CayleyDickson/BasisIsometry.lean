/- SPDX-License-Identifier: Apache-2.0 -/
module

public import GororobaMath.CayleyDickson.LeftMulMatrix

/-!
# Multiplication by a basis unit preserves the trace form

Convention: the product of `Tower R k` is the Cayley-Dickson product of
`GororobaMath.CayleyDickson.Tower`, `(a, b) (c, d) = (a c - star d b, d a + b star c)`, over a
commutative ring with the identity as star; `Tower.e R k j` is the basis unit of index `j`,
`Tower.dot k` the trace form of `GororobaMath.CayleyDickson.AnnihilatorSymmetry` and
`Tower.basis R k` the basis of `GororobaMath.CayleyDickson.TowerModule`.

The product of two basis units is a signed basis unit whose index is the exclusive or of the two
indices (`Tower.e_mul_e`), so multiplication by `e j` on either side permutes the basis up to
sign and its Gram matrix is the identity. Both sides of each identity are bilinear, so the basis
pairs decide it. No step uses associativity or alternativity: the trace form need not be
multiplicative from level 4 on, and the identities hold there because one factor is a basis unit.

## Main results

* `Tower.dot_mul_e_mul_e`: `dot (x * e j) (y * e j) = dot x y` at every level.
* `Tower.dot_e_mul_e_mul`: `dot (e j * x) (e j * y) = dot x y` at every level.
* `Tower.dot_mul_e_self_eq_sum`: `dot (y * e j) (y * e j)` is the sum of the squares of the
  coordinates of `y`, whatever `j` is. This is the identity `||L_y e_j||^2 = sum_i c_i^2` for
  `y = sum_i c_i e_i` of row A5-371 of the findings ledger of gororoba-quantum
  (`docs/evidence/a5-exceptional-fibers/ledger.tsv`), whose instance is `k = 5`; the success
  probability of the ideal herald that the row reads from it is not restated.
-/

@[expose] public section

namespace CayleyDickson

namespace Tower

universe u

variable {R : Type u} [CommRing R] [StarRing R] [TrivialStar R] {k : ℕ}

omit [TrivialStar R] in
/-- Two linear maps whose values on the basis units have the identity Gram matrix preserve the
trace form. -/
theorem dot_map_map_of_dot_e {f g : Tower R k →ₗ[R] Tower R k}
    (h : ∀ p q : BitVec k, dot k (f (e R k p)) (g (e R k q)) = if p = q then 1 else 0)
    (x y : Tower R k) : dot k (f x) (g y) = dot k x y := by
  let D : Tower R k →ₗ[R] Tower R k →ₗ[R] R :=
    LinearMap.mk₂ R (dot k) (dot_add_left k) (dot_smul_left k) (dot_add_right k)
      (dot_smul_right k)
  have hD : ∀ x y, D x y = dot k x y := fun _ _ => rfl
  have key : D.compl₁₂ f g = D :=
    LinearMap.ext_basis (basis R k) (basis R k) fun p q => by
      simp only [LinearMap.compl₁₂_apply, hD, basis_apply, h, dot_e_e]
  have hxy := LinearMap.congr_fun₂ key x y
  simpa only [LinearMap.compl₁₂_apply, hD] using hxy

omit [CommRing R] [StarRing R] [TrivialStar R] in
theorem xor_left_inj_iff (p q j : BitVec k) : p ^^^ j = q ^^^ j ↔ p = q := by
  constructor
  · intro h
    have h' := congrArg (· ^^^ j) h
    simpa [BitVec.xor_assoc] using h'
  · rintro rfl
    rfl

omit [TrivialStar R] in
/-- The right multiples of the basis units by one basis unit have the identity Gram matrix. -/
theorem dot_e_mul_e_e_mul_e (p q j : BitVec k) :
    dot k (e R k p * e R k j) (e R k q * e R k j) = if p = q then 1 else 0 := by
  rw [e_mul_e, e_mul_e]
  by_cases h : p = q
  · subst h
    cases negSign k p j <;> simp [dot_neg_left, dot_neg_right, dot_e_e]
  · have h' : p ^^^ j ≠ q ^^^ j := fun hh => h ((xor_left_inj_iff p q j).1 hh)
    cases negSign k p j <;> cases negSign k q j <;>
      simp [dot_neg_left, dot_neg_right, dot_e_e, h, h']

omit [TrivialStar R] in
/-- The left multiples of the basis units by one basis unit have the identity Gram matrix. -/
theorem dot_e_mul_e_e_mul_e_left (p q j : BitVec k) :
    dot k (e R k j * e R k p) (e R k j * e R k q) = if p = q then 1 else 0 := by
  rw [e_mul_e, e_mul_e]
  have hx : j ^^^ p = j ^^^ q ↔ p = q := by
    rw [BitVec.xor_comm j p, BitVec.xor_comm j q]
    exact xor_left_inj_iff p q j
  by_cases h : p = q
  · subst h
    cases negSign k j p <;> simp [dot_neg_left, dot_neg_right, dot_e_e]
  · have h' : j ^^^ p ≠ j ^^^ q := fun hh => h (hx.1 hh)
    cases negSign k j p <;> cases negSign k j q <;>
      simp [dot_neg_left, dot_neg_right, dot_e_e, h, h']

/-- Right multiplication by a basis unit preserves the trace form, at every level over every
commutative ring with the identity as star. -/
theorem dot_mul_e_mul_e (j : BitVec k) (x y : Tower R k) :
    dot k (x * e R k j) (y * e R k j) = dot k x y := by
  let f : Tower R k →ₗ[R] Tower R k :=
    { toFun := fun z => z * e R k j
      map_add' := fun a b => add_mul a b _
      map_smul' := fun r a => smul_mul_assoc' r a _ }
  exact dot_map_map_of_dot_e (f := f) (g := f) (fun p q => dot_e_mul_e_e_mul_e p q j) x y

/-- Left multiplication by a basis unit preserves the trace form, at every level over every
commutative ring with the identity as star. -/
theorem dot_e_mul_e_mul (j : BitVec k) (x y : Tower R k) :
    dot k (e R k j * x) (e R k j * y) = dot k x y :=
  dot_map_map_of_dot_e (f := mulLeft R k (e R k j)) (g := mulLeft R k (e R k j))
    (fun p q => dot_e_mul_e_e_mul_e_left p q j) x y

/-- The image of a basis unit under left multiplication by `y` has the squared norm of `y`. -/
theorem dot_mul_e_self (j : BitVec k) (y : Tower R k) :
    dot k (y * e R k j) (y * e R k j) = dot k y y :=
  dot_mul_e_mul_e j y y

/-- The image of `y` under left multiplication by a basis unit has the squared norm of `y`. -/
theorem dot_e_mul_self (j : BitVec k) (y : Tower R k) :
    dot k (e R k j * y) (e R k j * y) = dot k y y :=
  dot_e_mul_e_mul j y y

/-- For `y` with coordinates `c i`, every basis unit `e j` has
`dot (y * e j) (y * e j) = ∑ i, c i * c i`: the squared norm of `L_y (e j)` is the same sum for
every `j`. -/
theorem dot_mul_e_self_eq_sum (j : BitVec k) (y : Tower R k) :
    dot k (y * e R k j) (y * e R k j) = ∑ i, (basis R k).repr y i * (basis R k).repr y i := by
  rw [dot_mul_e_self, dot_eq_sum_repr]

end Tower

end CayleyDickson
