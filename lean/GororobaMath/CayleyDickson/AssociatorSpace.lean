/- SPDX-License-Identifier: Apache-2.0 -/
module

public import GororobaMath.CayleyDickson.TwoTermRecursion

/-!
# The associator space of two basis elements

For `a b : Tower R k` the associator space `Tower.assocSpace R k a b` is
`{x | (a * x) * b = a * (x * b)}`, the kernel of the `R`-linear map
`x ↦ (a * x) * b - a * (x * b)` (`Tower.associatorMap`). The tower,
its basis `e`, the index order (top bit outermost) and the signs
`Tower.negSign` (the convention of `cd_core.cd_sign`) are those of
`GororobaMath.CayleyDickson.Tower`; the scalars form a commutative ring
whose star is the identity, so left and right multiplication are linear.

On the basis, `(e a * e c) * e b` and `e a * (e c * e b)` are both signed
copies of `e (a ^^^ c ^^^ b)`, so the associator map sends `e c` to `0`
when the two signs agree (`Tower.associates a b c`) and to `±2 • e (a ^^^ c ^^^ b)`
otherwise. Since `c ↦ a ^^^ c ^^^ b` is a bijection, the associator space
is the coordinate subspace on the indices where the signs agree, once `2`
is a non-zero-divisor.

The sign identity `Tower.associates_eq` follows from the two sign rules
`Tower.negSign_xor_right` and `Tower.negSign_swap_xor` at every level: for
nonzero distinct `a` and `b`, an index `c` outside `{0, a, b, a ^^^ b}`
associates exactly when its pair under the operand `e a + e b` is aligned
(`Tower.misaligned`), and the four indices `0`, `a`, `b`, `a ^^^ b`
always associate and are never aligned (`Tower.misaligned_special`).

## Main results

* `Tower.associates_eq`: the associativity sign of `(e a, e c, e b)` in
  terms of the alignment sign of `c` under `e a + e b`, at every level.
* `Tower.card_associates`: for nonzero distinct `a` and `b`, the number
  of associating indices is `2 * alignedPairCount k a b + 4`.
* `Tower.assocSpaceEquivFun`, `Tower.free_assocSpace_e`: when `2` is a
  non-zero-divisor, the associator space of `e a` and `e b` is linearly
  equivalent to the functions on the associating indices, hence a free
  module, for all `a` and `b`.
* `Tower.finrank_assocSpace_e`: for nonzero distinct `a` and `b`, its rank
  is `2 * alignedPairCount k a b + 4` over every nontrivial commutative ring
  with the identity as star in which `2` is a non-zero-divisor;
  `Tower.finrank_assocSpace_e_of_charZero` is the statement over a field
  of characteristic zero.

Excluded cases: for `a = b` flexibility makes the space the whole level,
and for `a = 0` or `b = 0` the factor `e 0 = 1` does the same, so the rank
there is `2 ^ k`. With `alignedPairCount k a b = 0` in those cases the
formula gives `4`, which agrees only at `k = 2`.
-/

@[expose] public section

namespace CayleyDickson

open Module

section ZeroOff

variable {R : Type*} [CommRing R] {ι : Type*} (S : ι → Bool)

/-- The functions that vanish at every index where `S` is `false`. -/
def zeroOffSubmodule : Submodule R (ι → R) where
  carrier := {f | ∀ x, S x = false → f x = 0}
  add_mem' := by
    intro f g hf hg x hx
    simp [hf x hx, hg x hx]
  zero_mem' := by
    intro x _
    rfl
  smul_mem' := by
    intro r f hf x hx
    simp [hf x hx]

theorem mem_zeroOffSubmodule {f : ι → R} :
    f ∈ zeroOffSubmodule (R := R) S ↔ ∀ x, S x = false → f x = 0 :=
  Iff.rfl

/-- A function vanishing off `S` is its restriction to `S`. -/
def zeroOffEquiv : zeroOffSubmodule (R := R) S ≃ₗ[R] ({x // S x = true} → R) where
  toFun f t := f.1 t.1
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  invFun g := ⟨fun x => if h : S x = true then g ⟨x, h⟩ else 0, by
    intro x hx
    simp [hx]⟩
  left_inv f := by
    apply Subtype.ext
    funext x
    by_cases h : S x = true
    · simp [h]
    · simp only [h]
      exact (f.2 x (by simpa using h)).symm
  right_inv g := by
    funext t
    simp [t.2]

theorem finrank_zeroOffSubmodule [Fintype ι] [Nontrivial R] :
    finrank R (zeroOffSubmodule (R := R) S) = (Finset.univ.filter fun x => S x = true).card := by
  rw [(zeroOffEquiv S).finrank_eq, Module.finrank_fintype_fun_eq_card, Fintype.card_subtype]

end ZeroOff

namespace Tower

universe u

/-- `true` when `(e a * e c) * e b` and `e a * (e c * e b)` carry the same
sign. -/
def associates {k : ℕ} (a b c : BitVec k) : Bool :=
  (negSign k a c ^^ negSign k (a ^^^ c) b) == (negSign k c b ^^ negSign k a (c ^^^ b))

/-- The associativity sign of `(e a, e c, e b)` is the alignment sign of
`c` under the operand `e a + e b`, corrected by four indicator terms. -/
theorem associates_eq {k : ℕ} (a b c : BitVec k) :
    associates a b c =
      !(misaligned k a b c ^^ decide (a ≠ 0#k) ^^ decide (c ≠ 0#k ∧ b ≠ 0#k ∧ c ≠ b) ^^
        decide (b ≠ 0#k) ^^ decide (a ^^^ c ≠ 0#k ∧ b ≠ 0#k ∧ a ^^^ c ≠ b)) := by
  have h1 : partner a b c = a ^^^ (c ^^^ b) := by
    unfold partner
    rw [BitVec.xor_comm c a, BitVec.xor_assoc]
  have h2 : partner a b c = b ^^^ (a ^^^ c) := by
    unfold partner
    rw [BitVec.xor_comm c a, BitVec.xor_comm (a ^^^ c) b]
  have e1 : negSign k a (partner a b c) = (decide (a ≠ 0#k) ^^ negSign k a (c ^^^ b)) := by
    rw [h1, negSign_xor_right]
  have e2 : negSign k b (partner a b c) = (decide (b ≠ 0#k) ^^ negSign k b (a ^^^ c)) := by
    rw [h2, negSign_xor_right]
  have e3 := negSign_swap_xor k c b
  have e4 := negSign_swap_xor k (a ^^^ c) b
  unfold associates misaligned
  rw [e1, e2, e3, e4]
  generalize negSign k a c = s1
  generalize negSign k (a ^^^ c) b = s2
  generalize negSign k c b = s3
  generalize negSign k a (c ^^^ b) = s4
  generalize decide (a ≠ 0#k) = d1
  generalize decide (c ≠ 0#k ∧ b ≠ 0#k ∧ c ≠ b) = d2
  generalize decide (b ≠ 0#k) = d3
  generalize decide (a ^^^ c ≠ 0#k ∧ b ≠ 0#k ∧ a ^^^ c ≠ b) = d4
  revert s1 s2 s3 s4 d1 d2 d3 d4
  decide

theorem xor_eq_iff_eq_xor {k : ℕ} (a b c : BitVec k) : a ^^^ c = b ↔ c = a ^^^ b :=
  ⟨fun h => by rw [← h, xor_xor_cancel_left], fun h => by rw [h, xor_xor_cancel_left]⟩

/-- For nonzero distinct `a` and `b`, the indices that associate are the
aligned indices of `e a + e b` and the four indices `0`, `a`, `b`,
`a ^^^ b`. -/
theorem card_associates {k : ℕ} {a b : BitVec k} (ha : a ≠ 0#k) (hb : b ≠ 0#k) (hab : a ≠ b) :
    (Finset.univ.filter fun c => associates a b c = true).card =
      2 * alignedPairCount k a b + 4 := by
  have hc0 : (0#k : BitVec k) ≠ a ^^^ b := fun h => hab (BitVec.xor_eq_zero_iff.1 h.symm)
  have hy : ∀ c : BitVec k,
      (if associates a b c = true then 1 else 0) =
        (((((if misaligned k a b c = false then 1 else 0) + if c = 0#k then 1 else 0) +
          if c = a then 1 else 0) + if c = b then 1 else 0) + if c = a ^^^ b then 1 else 0) := by
    intro c
    rw [associates_eq]
    have hac : a ^^^ c = 0#k ↔ c = a := by rw [BitVec.xor_eq_zero_iff, eq_comm]
    have hbc : a ^^^ c = b ↔ c = a ^^^ b := xor_eq_iff_eq_xor a b c
    by_cases hs : c = 0#k ∨ c = a ∨ c = b ∨ c = a ^^^ b
    · have hm := (misaligned_special ha hb hab hs).1
      rw [hm]
      rcases hs with h | h | h | h <;> subst h <;>
        simp [ha, hb, hab, Ne.symm ha, Ne.symm hb, Ne.symm hab, hc0, Ne.symm hc0, hbc,
          self_eq_xor_left_iff, self_eq_xor_right_iff]
    · simp only [not_or] at hs
      obtain ⟨h0, hca, hcb, hcab⟩ := hs
      cases misaligned k a b c <;> simp [ha, hb, h0, hcb, hac, hbc, hca, hcab]
  have hsum := Finset.sum_congr (s₁ := (Finset.univ : Finset (BitVec k))) rfl
    fun c (_ : c ∈ Finset.univ) => hy c
  simp only [Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.mem_univ, ite_true] at hsum
  rw [← Finset.card_filter, ← Finset.card_filter] at hsum
  have h2 := alignedCount_eq_two_mul hab
  unfold alignedCount at h2
  omega

variable {R : Type u} [CommRing R] [StarRing R] [TrivialStar R]

variable (R) in
/-- Right multiplication by `x` as an `R`-linear map. -/
def mulRight (k : ℕ) (x : Tower R k) : Tower R k →ₗ[R] Tower R k where
  toFun y := y * x
  map_add' a b := add_mul a b x
  map_smul' r y := smul_mul_assoc' r y x

@[simp] theorem mulRight_apply {k : ℕ} (x y : Tower R k) : mulRight R k x y = y * x := rfl

variable (R) in
/-- The associator `x ↦ (a * x) * b - a * (x * b)` as an `R`-linear map of
`x`. -/
def associatorMap (k : ℕ) (a b : Tower R k) : Tower R k →ₗ[R] Tower R k :=
  mulRight R k b ∘ₗ mulLeft R k a - mulLeft R k a ∘ₗ mulRight R k b

variable (R) in
/-- The associator space `Ass a b = {x | (a * x) * b = a * (x * b)}`, the
kernel of `associatorMap`. -/
def assocSpace (k : ℕ) (a b : Tower R k) : Submodule R (Tower R k) :=
  LinearMap.ker (associatorMap R k a b)

theorem mem_assocSpace {k : ℕ} {a b x : Tower R k} :
    x ∈ assocSpace R k a b ↔ (a * x) * b = a * (x * b) := by
  simp [assocSpace, associatorMap, sub_eq_zero]

variable (R) in
/-- The coefficient of the associator map at `e c`: `0` when the two signs
agree, `±2` otherwise. -/
def assocCoeff {k : ℕ} (a b c : BitVec k) : R :=
  (if negSign k a c ^^ negSign k (a ^^^ c) b then -1 else 1) -
    (if negSign k c b ^^ negSign k a (c ^^^ b) then -1 else 1)

theorem associatorMap_e {k : ℕ} (a b c : BitVec k) :
    associatorMap R k (e R k a) (e R k b) (e R k c) =
      assocCoeff R a b c • e R k (a ^^^ c ^^^ b) := by
  simp only [associatorMap, LinearMap.sub_apply, LinearMap.comp_apply, mulLeft_apply,
    mulRight_apply, assocCoeff, sub_smul]
  rw [e_mul_e k a c, e_mul_e k c b]
  have hx : a ^^^ (c ^^^ b) = a ^^^ c ^^^ b := (BitVec.xor_assoc a c b).symm
  cases h1 : negSign k a c <;> cases h2 : negSign k (a ^^^ c) b <;>
    cases h3 : negSign k c b <;> cases h4 : negSign k a (c ^^^ b) <;>
    simp [e_mul_e, h2, h4, hx]

theorem repr_associatorMap {k : ℕ} (a b x : BitVec k) (y : Tower R k) :
    (basis R k).repr (associatorMap R k (e R k a) (e R k b) y) (a ^^^ b ^^^ x) =
      assocCoeff R a b x * (basis R k).repr y x := by
  let f : Tower R k →ₗ[R] R :=
    (basis R k).coord (a ^^^ b ^^^ x) ∘ₗ associatorMap R k (e R k a) (e R k b)
  let g : Tower R k →ₗ[R] R := assocCoeff R a b x • (basis R k).coord x
  have hfg : f = g := by
    refine (basis R k).ext fun z => ?_
    simp only [f, g, LinearMap.comp_apply, LinearMap.smul_apply, Basis.coord_apply, basis_apply,
      associatorMap_e, map_smul, repr_e, smul_eq_mul]
    have hz' : a ^^^ z ^^^ b = a ^^^ b ^^^ z := by
      rw [BitVec.xor_assoc, BitVec.xor_comm z b, ← BitVec.xor_assoc]
    have hiff : a ^^^ z ^^^ b = a ^^^ b ^^^ x ↔ z = x := by
      rw [hz']
      constructor
      · intro h
        have := congrArg (fun v => (a ^^^ b) ^^^ v) h
        simpa only [xor_xor_cancel_left] using this
      · rintro rfl
        rfl
    by_cases hz : z = x
    · subst hz
      simp [hiff]
    · simp [hiff, hz]
  have := LinearMap.congr_fun hfg y
  simpa [f, g] using this

omit [StarRing R] [TrivialStar R] in
theorem assocCoeff_mul_eq_zero_iff (h2 : IsLeftRegular (2 : R)) {k : ℕ} (a b x : BitVec k)
    (r : R) : assocCoeff R a b x * r = 0 ↔ associates a b x = true ∨ r = 0 := by
  have hr : 2 * r = 0 ↔ r = 0 :=
    ⟨fun h => h2 (show 2 * r = 2 * 0 by rw [h, mul_zero]), fun h => by rw [h, mul_zero]⟩
  unfold assocCoeff associates
  generalize (negSign k a x ^^ negSign k (a ^^^ x) b) = s
  generalize (negSign k x b ^^ negSign k a (x ^^^ b)) = t
  cases s <;> cases t
  · simp
  · have hc : ((if false = true then -1 else 1) - (if true = true then -1 else 1) : R) * r =
        2 * r := by simp; ring
    rw [hc, hr]
    simp
  · have hc : ((if true = true then -1 else 1) - (if false = true then -1 else 1) : R) * r =
        -(2 * r) := by simp; ring
    rw [hc, neg_eq_zero, hr]
    simp
  · simp

/-- The associator space of `e a` and `e b` in coordinates: the vectors
that vanish at every index where the two signs differ. -/
theorem mem_assocSpace_e_iff (h2 : IsLeftRegular (2 : R)) {k : ℕ} (a b : BitVec k)
    (y : Tower R k) :
    y ∈ assocSpace R k (e R k a) (e R k b) ↔
      (basis R k).equivFun y ∈ zeroOffSubmodule (associates a b) := by
  rw [assocSpace, mem_ker_iff_repr_xor (a ^^^ b), mem_zeroOffSubmodule]
  refine forall_congr' fun x => ?_
  rw [repr_associatorMap, assocCoeff_mul_eq_zero_iff h2, Basis.equivFun_apply]
  cases associates a b x <;> simp

variable (R) in
/-- The associator space of `e a` and `e b` is linearly equivalent to the
functions on the indices that associate, when `2` is a non-zero-divisor. -/
noncomputable def assocSpaceEquivFun (h2 : IsLeftRegular (2 : R)) {k : ℕ} (a b : BitVec k) :
    assocSpace R k (e R k a) (e R k b) ≃ₗ[R] ({x // associates a b x = true} → R) :=
  ((basis R k).equivFun.submoduleMap (assocSpace R k (e R k a) (e R k b))).trans
    ((LinearEquiv.ofEq _ _ (by
      ext z
      rw [Submodule.mem_map_equiv, mem_assocSpace_e_iff h2, LinearEquiv.apply_symm_apply])).trans
      (zeroOffEquiv (associates a b)))

/-- The associator space of `e a` and `e b` is a free module when `2` is a
non-zero-divisor. -/
theorem free_assocSpace_e (h2 : IsLeftRegular (2 : R)) {k : ℕ} (a b : BitVec k) :
    Module.Free R (assocSpace R k (e R k a) (e R k b)) :=
  Module.Free.of_equiv (assocSpaceEquivFun R h2 a b).symm

/-- **Associator dimension.** For nonzero distinct indices `a` and `b`, the
associator space of `e a` and `e b` has rank
`2 * alignedPairCount k a b + 4`, over every nontrivial commutative ring
with the identity as star in which `2` is a non-zero-divisor. -/
theorem finrank_assocSpace_e [Nontrivial R] (h2 : IsLeftRegular (2 : R)) {k : ℕ}
    {a b : BitVec k} (ha : a ≠ 0#k) (hb : b ≠ 0#k) (hab : a ≠ b) :
    finrank R (assocSpace R k (e R k a) (e R k b)) = 2 * alignedPairCount k a b + 4 := by
  rw [← (basis R k).equivFun.finrank_map_eq, ← card_associates ha hb hab,
    ← finrank_zeroOffSubmodule (R := R)]
  congr 2 <;>
  · ext z
    rw [Submodule.mem_map_equiv, mem_assocSpace_e_iff h2, LinearEquiv.apply_symm_apply]

/-- The associator dimension over a field of characteristic zero. -/
theorem finrank_assocSpace_e_of_charZero {K : Type u} [Field K] [CharZero K] [StarRing K]
    [TrivialStar K] {k : ℕ} {a b : BitVec k} (ha : a ≠ 0#k) (hb : b ≠ 0#k) (hab : a ≠ b) :
    finrank K (assocSpace K k (e K k a) (e K k b)) = 2 * alignedPairCount k a b + 4 :=
  finrank_assocSpace_e (fun _ _ h => mul_left_cancel₀ two_ne_zero h) ha hb hab

end Tower

end CayleyDickson
