/- SPDX-License-Identifier: Apache-2.0 -/
module

public import GororobaMath.CayleyDickson.Tower

/-!
# The tower as a module with the basis `e`

Over a commutative ring `R`, `Tower R k` is an `R`-module that acts on each
half of every double (`CayleyDickson.instModule`); at level `0` it is the
action of `R` on itself by multiplication. The basis elements `Tower.e R k p`
form a basis indexed by `BitVec k`, with the index convention of
`GororobaMath.CayleyDickson.Tower`: the top bit of `p` selects the half of the
outermost double. The coordinate of `x` at `p` is `(Tower.basis R k).repr x p`.

When the star of `R` is the identity (`TrivialStar R`), scalars commute with
the product on both sides at every level, so left multiplication by `x` is
`R`-linear (`Tower.mulLeft`). In coordinates, left multiplication by `e i`
is a signed permutation: the coordinate of `e i * y` at `w` is the
coordinate of `y` at `i ^^^ w`, negated when `negSign k i (i ^^^ w)` holds.

## Main results

* `Tower.instModule`: the `R`-module structure of every level, with
  `Tower.smul_mk` and `Tower.smul_level_zero` holding by `rfl`.
* `Tower.basis`, `Tower.basis_apply`: a basis indexed by `BitVec k` whose
  vector at `p` is `e R k p`; `Tower.finrank_eq` gives `finrank = 2 ^ k`.
* `Tower.mul_smul_comm'`, `Tower.smul_mul_assoc'`, `Tower.smul_eq_mul`: the
  scalar action commutes with the product, and `r • x = (r • 1) * x`.
* `Tower.mulLeft`: left multiplication as an `R`-linear map.
* `Tower.repr_e_mul`: the coordinates of `e i * y`.
-/

@[expose] public section

namespace CayleyDickson

namespace Tower

universe u

open Module

section Module

variable (R : Type u) [CommRing R] [StarRing R]

/-- The module structure of every level: multiplication at level `0`, the
componentwise action of `CayleyDickson.instModule` above it. -/
@[instance_reducible]
def moduleStructure : (k : ℕ) → Module R (Tower R k)
  | 0 => inferInstanceAs (Module R R)
  | k + 1 =>
    letI := moduleStructure k
    inferInstanceAs (Module R (CayleyDickson (Tower R k)))

instance instModule (k : ℕ) : Module R (Tower R k) := moduleStructure R k

variable {R}

omit [StarRing R] in
/-- At level `0` the action is the product of `R`. -/
theorem smul_level_zero (r x : R) : (r • (x : Tower R 0) : Tower R 0) = r * x := rfl

theorem smul_mk {k : ℕ} (r : R) (a b : Tower R k) : r • mk a b = mk (r • a) (r • b) := rfl

/-- Over a commutative ring whose star is the identity, scalars pass through
the product on both sides and through the star, at every level. The three
statements are proved together because the product of level `k + 1` uses the
star of level `k`. -/
theorem smul_mul_star [TrivialStar R] : ∀ (k : ℕ) (r : R) (x y : Tower R k),
    x * (r • y) = r • (x * y) ∧ (r • x) * y = r • (x * y) ∧ star (r • x) = r • star x
  | 0, r, x, y => by
    have h1 : ∀ a b : R, a * (r * b) = r * (a * b) := fun a b => mul_left_comm a r b
    have h2 : ∀ a b : R, (r * a) * b = r * (a * b) := fun a b => mul_assoc r a b
    have h3 : ∀ a : R, star (r * a) = r * star a := fun a => by rw [star_mul', star_trivial]
    exact ⟨h1 x y, h2 x y, h3 x⟩
  | k + 1, r, ⟨a, b⟩, ⟨c, d⟩ => by
    have hm := smul_mul_star k r
    refine ⟨?_, ?_, ?_⟩
    · show mk a b * mk (r • c) (r • d) = r • (mk a b * mk c d)
      rw [mk_mul_mk, mk_mul_mk, smul_mk, (hm a c).1, (hm d d).2.2, (hm (star d) b).2.1,
        (hm d a).2.1, (hm c c).2.2, (hm b (star c)).1, smul_sub, smul_add]
    · show mk (r • a) (r • b) * mk c d = r • (mk a b * mk c d)
      rw [mk_mul_mk, mk_mul_mk, smul_mk, (hm a c).2.1, (hm (star d) b).1, (hm d a).1,
        (hm b (star c)).2.1, smul_sub, smul_add]
    · show star (mk (r • a) (r • b)) = r • star (mk a b)
      rw [star_mk, star_mk, smul_mk, (hm a a).2.2, smul_neg]

variable [TrivialStar R]

theorem mul_smul_comm' {k : ℕ} (r : R) (x y : Tower R k) : x * (r • y) = r • (x * y) :=
  (smul_mul_star k r x y).1

theorem smul_mul_assoc' {k : ℕ} (r : R) (x y : Tower R k) : (r • x) * y = r • (x * y) :=
  (smul_mul_star k r x y).2.1

theorem star_smul' {k : ℕ} (r : R) (x : Tower R k) : star (r • x) = r • star x :=
  (smul_mul_star k r x x).2.2

/-- The action of a scalar is left multiplication by its image `r • 1` in
the tower. -/
theorem smul_eq_mul {k : ℕ} (r : R) (x : Tower R k) : r • x = (r • 1 : Tower R k) * x := by
  rw [smul_mul_assoc', one_mul]

variable (R) in
/-- Left multiplication by `x` as an `R`-linear map. -/
def mulLeft (k : ℕ) (x : Tower R k) : Tower R k →ₗ[R] Tower R k where
  toFun y := x * y
  map_add' := mul_add x
  map_smul' r y := mul_smul_comm' r x y

@[simp] theorem mulLeft_apply {k : ℕ} (x y : Tower R k) : mulLeft R k x y = x * y := rfl

end Module

section Basis

/-- `BitVec (k + 1)` splits by its top bit into two copies of `BitVec k`:
`Sum.inl q` is `q` with top bit `0`, `Sum.inr q` is `q` with top bit `1`. -/
def sumEquiv (k : ℕ) : BitVec k ⊕ BitVec k ≃ BitVec (k + 1) where
  toFun := Sum.elim (BitVec.cons false) (BitVec.cons true)
  invFun p := if p.msb then Sum.inr (p.setWidth k) else Sum.inl (p.setWidth k)
  left_inv s := by
    cases s <;> simp [BitVec.msb_cons, BitVec.setWidth_cons]
  right_inv p := by
    cases h : p.msb
    · simp only [h, Bool.false_eq_true, ↓reduceIte, Sum.elim_inl]
      rw [← h, BitVec.cons_msb_setWidth]
    · simp only [h, ↓reduceIte, Sum.elim_inr]
      rw [← h, BitVec.cons_msb_setWidth]

theorem sumEquiv_symm_apply {k : ℕ} (p : BitVec (k + 1)) :
    (sumEquiv k).symm p = if p.msb then Sum.inr (p.setWidth k) else Sum.inl (p.setWidth k) :=
  rfl

/-- `BitVec 0` has the one element `0#0`. -/
@[instance_reducible]
def uniqueBitVecZero : Unique (BitVec 0) := ⟨⟨0#0⟩, fun _ => BitVec.of_length_zero⟩

variable (R : Type u) [CommRing R] [StarRing R]

/-- The basis of `Tower R k` indexed by `BitVec k`: the unit at level `0`,
and above it the product basis of the two halves reindexed by the top bit. -/
noncomputable def basis : (k : ℕ) → Basis (BitVec k) R (Tower R k)
  | 0 =>
    @Basis.singleton (BitVec 0) R uniqueBitVecZero _
  | k + 1 =>
    (((basis k).prod (basis k)).map (linearEquivProd (Tower R k) R).symm).reindex (sumEquiv k)

/-- The basis vector at `p` is `e R k p`. -/
theorem basis_apply : ∀ (k : ℕ) (p : BitVec k), basis R k p = e R k p
  | 0, p => by
    unfold basis
    exact @Basis.singleton_apply (BitVec 0) R uniqueBitVecZero _ p
  | k + 1, p => by
    show (((basis R k).prod (basis R k)).map (linearEquivProd (Tower R k) R).symm).reindex
      (sumEquiv k) p = e R (k + 1) p
    rw [Basis.reindex_apply, Basis.map_apply, sumEquiv_symm_apply]
    cases h : p.msb
    · simp only [Bool.false_eq_true, ↓reduceIte, Basis.prod_apply, Sum.elim_inl,
        Function.comp_apply, LinearMap.inl_apply, linearEquivProd_symm_apply]
      rw [e_succ_of_not_msb h, basis_apply k]
      rfl
    · simp only [↓reduceIte, Basis.prod_apply, Sum.elim_inr, Function.comp_apply,
        LinearMap.inr_apply, linearEquivProd_symm_apply]
      rw [e_succ_of_msb h, basis_apply k]
      rfl

theorem coe_basis (k : ℕ) : ⇑(basis R k) = e R k := funext (basis_apply R k)

instance (k : ℕ) : Module.Free R (Tower R k) := Module.Free.of_basis (basis R k)

instance (k : ℕ) : Module.Finite R (Tower R k) := Module.Finite.of_basis (basis R k)

/-- `Tower R k` has dimension `2 ^ k` over a nontrivial commutative ring. -/
theorem finrank_eq [Nontrivial R] (k : ℕ) : finrank R (Tower R k) = 2 ^ k := by
  rw [finrank_eq_card_basis (basis R k), Fintype.card_congr BitVec.equivFin.toEquiv,
    Fintype.card_fin]

variable {R}

/-- The coordinate of a basis element: `1` at its own index, `0` elsewhere. -/
theorem repr_e {k : ℕ} (p q : BitVec k) :
    (basis R k).repr (e R k p) q = if p = q then 1 else 0 := by
  rw [← basis_apply R k p, Basis.repr_self, Finsupp.single_apply]

theorem xor_xor_cancel_left {k : ℕ} (i x : BitVec k) : i ^^^ (i ^^^ x) = x := by
  rw [← BitVec.xor_assoc, BitVec.xor_self, BitVec.zero_xor]

variable [TrivialStar R]

/-- Left multiplication by `e i` is a signed permutation of coordinates: the
coordinate of `e i * y` at `w` is the coordinate of `y` at `i ^^^ w`, with
the sign of `e i * e (i ^^^ w)`. -/
theorem repr_e_mul {k : ℕ} (i w : BitVec k) (y : Tower R k) :
    (basis R k).repr (e R k i * y) w =
      if negSign k i (i ^^^ w) then -(basis R k).repr y (i ^^^ w)
      else (basis R k).repr y (i ^^^ w) := by
  let f : Tower R k →ₗ[R] R := (basis R k).coord w ∘ₗ mulLeft R k (e R k i)
  let g : Tower R k →ₗ[R] R :=
    if negSign k i (i ^^^ w) then -(basis R k).coord (i ^^^ w) else (basis R k).coord (i ^^^ w)
  have hfg : f = g := by
    refine (basis R k).ext fun z => ?_
    simp only [f, g, LinearMap.comp_apply, mulLeft_apply, Basis.coord_apply, basis_apply]
    rw [e_mul_e]
    have hiff : i ^^^ z = w ↔ z = i ^^^ w := by
      constructor
      · rintro rfl
        rw [xor_xor_cancel_left]
      · rintro rfl
        rw [xor_xor_cancel_left]
    by_cases hz : z = i ^^^ w
    · subst hz
      rw [xor_xor_cancel_left]
      split_ifs <;> simp [repr_e]
    · have hw : i ^^^ z ≠ w := fun h => hz (hiff.1 h)
      have hz' : z ≠ i ^^^ w := hz
      split_ifs <;> simp [repr_e, hw, hz']
  have := LinearMap.congr_fun hfg y
  simp only [f, g, LinearMap.comp_apply, mulLeft_apply, Basis.coord_apply] at this
  rw [this]
  split_ifs <;> simp

end Basis

end Tower

end CayleyDickson
