/- SPDX-License-Identifier: Apache-2.0 -/
module

public import GororobaMath.CayleyDickson.TowerModule
public import GororobaMath.CayleyDickson.TwoTerm

/-!
# The nullity of a two-term operand

Left multiplication by `e i + e j` on `Tower R k` has a kernel that is a free
module of rank `alignedPairCount k i j`, over every nontrivial commutative
ring `R` with the identity as star in which `2` is a non-zero-divisor: the
integers, the rationals, the reals, and every field of characteristic other
than two taken with the identity as its star (the complex numbers with
conjugation as star lie outside the statement). Over a field the rank is the
dimension of the kernel. The
basis is `Tower.basis` (the elements `e p`, indexed by `BitVec k` with the
top bit outermost) and the signs are `Tower.negSign`, the convention of
`gororoba_quantum/cd_core.py` (`cd_sign`).

The coordinate of `(e i + e j) * y` at `i ^^^ x` involves only the
coordinates of `y` at `x` and at its partner `x' = x ^^^ i ^^^ j`
(`Tower.repr_e_mul`), so the kernel is cut out by one relation per index:
`y x = y x'` when the two signs `negSign k i x` and `negSign k j x'` differ,
`y x = -y x'` when they agree. A pair `{x, x'}` whose two relations agree is
an aligned pair and contributes one free coordinate; a pair whose relations
disagree forces `y x = -y x`, hence `y x = 0` when `2` cancels. The same
argument with the second sign negated gives the kernel of `e i - e j`.

## Main results

* `CayleyDickson.finrank_pairedSubmodule`: for an involution `σ` and signs
  `δ`, the vectors with `y x = ± y (σ x)` form a free module whose rank is
  the number of pairs whose two relations agree.
* `Tower.mem_ker_mulLeft_e_add_e`, `Tower.mem_ker_mulLeft_e_sub_e`: the
  kernels in coordinates.
* `Tower.finrank_ker_mulLeft_e_add_e`: the kernel of left multiplication by
  `e i + e j` has rank `alignedPairCount k i j` for all `i` and `j`,
  including `i = j`, where it is `0`.
* `Tower.finrank_ker_mulLeft_e_sub_e`: the same for `e i - e j` with `i ≠ j`.
* `Tower.finrank_ker_pathion_1_18`, `Tower.finrank_ker_pathion_1_18_int`:
  the `A_5` operand `e_1 + e_18` has nullity twelve over `ℚ` and over `ℤ`.
-/

@[expose] public section

namespace CayleyDickson

open Module

section Paired

variable {R : Type*} [CommRing R] {ι : Type*} (σ : ι → ι) (δ : ι → Bool)

/-- The vectors that satisfy, at every index `x`, the relation
`y x = y (σ x)` when `δ x` holds and `y x = -y (σ x)` otherwise. -/
def pairedSubmodule : Submodule R (ι → R) where
  carrier := {y | ∀ x, y x = if δ x then y (σ x) else -y (σ x)}
  add_mem' := by
    intro a b ha hb x
    have h1 := ha x
    have h2 := hb x
    cases hδ : δ x <;> simp only [hδ, Bool.false_eq_true, ↓reduceIte] at h1 h2 ⊢ <;>
      simp only [Pi.add_apply, h1, h2, neg_add]
  zero_mem' := by
    intro x
    simp
  smul_mem' := by
    intro c y hy x
    have h1 := hy x
    cases hδ : δ x <;> simp only [hδ, Bool.false_eq_true, ↓reduceIte] at h1 ⊢ <;>
      simp only [Pi.smul_apply, h1, smul_neg]

theorem mem_pairedSubmodule {y : ι → R} :
    y ∈ pairedSubmodule σ δ ↔ ∀ x, y x = if δ x then y (σ x) else -y (σ x) :=
  Iff.rfl

variable {σ} (key : ι → ℕ)

/-- An index is the chosen representative of a pair whose two relations
agree: its key is below its partner's. -/
def IsPairRep (x : ι) : Prop := key x < key (σ x) ∧ δ x = δ (σ x)

instance : DecidablePred (IsPairRep δ key (σ := σ)) := fun x => by
  unfold IsPairRep
  infer_instance

variable {δ key}

theorem not_isPairRep_of_isPairRep (hσ : ∀ x, σ (σ x) = x) {x : ι}
    (h : IsPairRep δ key (σ := σ) x) : ¬IsPairRep δ key (σ := σ) (σ x) := by
  intro h'
  have h1 := h.1
  have h2 := h'.1
  rw [hσ] at h2
  omega

/-- A vector of the paired submodule vanishes at an index outside every
agreeing pair's representative, when `2` cancels and `key` separates the
two elements of each pair. -/
theorem eq_zero_of_not_isPairRep (hσ : ∀ x, σ (σ x) = x)
    (hfix : ∀ x, σ x = x → δ x = false) (hkey : Function.Injective key)
    (h2 : ∀ a : R, a + a = 0 → a = 0) {y : ι → R} (hy : y ∈ pairedSubmodule σ δ) {x : ι}
    (hx : ¬IsPairRep δ key (σ := σ) x) (hσx : ¬IsPairRep δ key (σ := σ) (σ x)) : y x = 0 := by
  apply h2
  have hyx := hy x
  have hyσ := hy (σ x)
  rw [hσ] at hyσ
  by_cases hd : δ x = δ (σ x)
  · have hk : key x = key (σ x) := by
      unfold IsPairRep at hx hσx
      rw [hσ] at hσx
      have : ¬key x < key (σ x) := fun hlt => hx ⟨hlt, hd⟩
      have : ¬key (σ x) < key x := fun hlt => hσx ⟨hlt, hd.symm⟩
      omega
    have hfx : σ x = x := (hkey hk).symm
    rw [hfx, hfix x hfx] at hyx
    simp only [Bool.false_eq_true, ↓reduceIte] at hyx
    linear_combination hyx
  · cases ha : δ x <;> cases hb : δ (σ x) <;> simp only [ha, hb, not_true_eq_false] at hd <;>
      simp only [ha, hb, Bool.false_eq_true, ↓reduceIte] at hyx hyσ
    · linear_combination hyx - hyσ
    · linear_combination hyx + hyσ

/-- The paired submodule is free on the representatives of the pairs whose
two relations agree. -/
def pairedEquiv (hσ : ∀ x, σ (σ x) = x) (hfix : ∀ x, σ x = x → δ x = false)
    (hkey : Function.Injective key) (h2 : ∀ a : R, a + a = 0 → a = 0) :
    pairedSubmodule (R := R) σ δ ≃ₗ[R] ({x // IsPairRep δ key (σ := σ) x} → R) where
  toFun y t := y.1 t.1
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  invFun c :=
    let c' : ι → R := fun x => if h : IsPairRep δ key (σ := σ) x then c ⟨x, h⟩ else 0
    ⟨fun x => c' x + if δ (σ x) then c' (σ x) else -c' (σ x), by
      intro x
      simp only [hσ]
      by_cases hx : IsPairRep δ key (σ := σ) x
      · have hσx := not_isPairRep_of_isPairRep hσ hx
        simp only [c', hx, hσx, dite_true, dite_false, neg_zero, ite_self, add_zero, zero_add]
        cases δ x <;> simp
      · by_cases hσx : IsPairRep δ key (σ := σ) (σ x)
        · have hd : δ (σ x) = δ x := by
            have := hσx.2
            rwa [hσ] at this
          simp only [c', hx, hσx, dite_true, dite_false, zero_add]
          rw [hd]
          cases δ x <;> simp
        · simp [c', hx, hσx]⟩
  left_inv y := by
    apply Subtype.ext
    funext x
    simp only
    by_cases hx : IsPairRep δ key (σ := σ) x
    · have hσx := not_isPairRep_of_isPairRep hσ hx
      simp [hx, hσx]
    · by_cases hσx : IsPairRep δ key (σ := σ) (σ x)
      · have hd : δ (σ x) = δ x := by
          have := hσx.2
          rwa [hσ] at this
        simp only [hx, hσx, dite_true, dite_false, zero_add]
        rw [hd, y.2 x]
      · simp only [hx, hσx, dite_false, neg_zero, ite_self, add_zero]
        exact (eq_zero_of_not_isPairRep hσ hfix hkey h2 y.2 hx hσx).symm
  right_inv c := by
    funext t
    have hσt := not_isPairRep_of_isPairRep hσ t.2
    simp [t.2, hσt]

/-- The rank of the paired submodule is the number of pairs whose two
relations agree, counted by their representatives. -/
theorem finrank_pairedSubmodule [Fintype ι] [Nontrivial R] (hσ : ∀ x, σ (σ x) = x)
    (hfix : ∀ x, σ x = x → δ x = false) (hkey : Function.Injective key)
    (h2 : ∀ a : R, a + a = 0 → a = 0) :
    finrank R (pairedSubmodule (R := R) σ δ) =
      (Finset.univ.filter (IsPairRep δ key (σ := σ))).card := by
  rw [(pairedEquiv hσ hfix hkey h2).finrank_eq, Module.finrank_fintype_fun_eq_card,
    Fintype.card_subtype]

/-- The agreeing pairs are counted twice by their elements. -/
theorem card_agree_eq_two_mul [Fintype ι] (hσ : ∀ x, σ (σ x) = x) (hfix : ∀ x, σ x ≠ x)
    (hkey : Function.Injective key) :
    (Finset.univ.filter fun x => δ x = δ (σ x)).card =
      2 * (Finset.univ.filter (IsPairRep δ key (σ := σ))).card := by
  rw [← Finset.card_filter_add_card_filter_not (p := fun x => key x < key (σ x)),
    Finset.filter_filter, Finset.filter_filter, two_mul]
  have hrep : (Finset.univ.filter fun x => δ x = δ (σ x) ∧ key x < key (σ x)) =
      Finset.univ.filter (IsPairRep δ key (σ := σ)) := by
    ext x
    simp [IsPairRep, and_comm]
  rw [hrep]
  congr 1
  refine Finset.card_bij' (fun x _ => σ x) (fun x _ => σ x) ?_ ?_ (fun x _ => hσ x)
    (fun x _ => hσ x)
  · intro x hx
    simp only [IsPairRep, Finset.mem_filter, Finset.mem_univ, true_and] at hx ⊢
    have hne : key x ≠ key (σ x) := fun h => hfix x (hkey h).symm
    rw [hσ]
    exact ⟨by omega, hx.1.symm⟩
  · intro x hx
    simp only [IsPairRep, Finset.mem_filter, Finset.mem_univ, true_and] at hx ⊢
    rw [hσ]
    exact ⟨hx.2.symm, by omega⟩

end Paired

namespace Tower

universe u

/-- `true` when the signs of `e i * e x` and `e j * e x'` differ, with
`x' = partner i j x`: the coordinate relation of the kernel of `e i + e j`
at `x` is then `y x = y x'`, and otherwise `y x = -y x'`. -/
def pairSign {k : ℕ} (i j x : BitVec k) : Bool := xor (negSign k i x) (negSign k j (partner i j x))

theorem xor_xor_eq_partner {k : ℕ} (i j x : BitVec k) : j ^^^ (i ^^^ x) = partner i j x := by
  unfold partner
  ext n hn
  simp only [BitVec.getElem_xor]
  cases x[n] <;> cases i[n] <;> cases j[n] <;> rfl

/-- A pair is aligned exactly when its two coordinate relations agree. -/
theorem aligned_iff_pairSign {k : ℕ} (i j x : BitVec k) :
    (alignedAdd k i j x || alignedSub k i j x) = true ↔
      pairSign i j x = pairSign i j (partner i j x) := by
  unfold alignedAdd alignedSub pairSign
  rw [partner_partner]
  cases negSign k i x <;> cases negSign k j (partner i j x) <;> cases negSign k j x <;>
    cases negSign k i (partner i j x) <;> decide

/-- `alignedPairCount` for `i ≠ j` is half the number of indices whose pair
is aligned. -/
theorem alignedPairCount_eq_card {k : ℕ} {i j : BitVec k} (hij : i ≠ j) :
    alignedPairCount k i j =
      (Finset.univ.filter fun x => (alignedAdd k i j x || alignedSub k i j x) = true).card / 2 := by
  simp only [alignedPairCount, hij, ↓reduceIte]
  congr 1
  set p : BitVec k → Bool := fun x => alignedAdd k i j x || alignedSub k i j x
  let l := (List.range (2 ^ k)).map (BitVec.ofNat k)
  have hl : l.Nodup := by
    refine List.Nodup.map_on ?_ List.nodup_range
    intro a ha b hb h
    have := congrArg BitVec.toNat h
    simp only [BitVec.toNat_ofNat] at this
    rw [List.mem_range] at ha hb
    rwa [Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb] at this
  have hfl : l.toFinset = Finset.univ := by
    ext x
    simp only [l, List.mem_toFinset, List.mem_map, List.mem_range, Finset.mem_univ, iff_true]
    exact ⟨x.toNat, x.isLt, by simp⟩
  have hlen : ((List.range (2 ^ k)).filter fun n => p (BitVec.ofNat k n)).length =
      (l.filter p).length := by
    simp only [l, List.filter_map, List.length_map]
    rfl
  rw [hlen, ← List.toFinset_card_of_nodup (hl.filter p), List.toFinset_filter, hfl]

variable {R : Type u} [CommRing R] [StarRing R] [TrivialStar R]

/-- The coordinate of `(e i ± e j) * y` at `i ^^^ x` in terms of the
coordinates of `y` at `x` and at its partner. -/
theorem repr_e_add_e_mul {k : ℕ} (i j x : BitVec k) (y : Tower R k) :
    (basis R k).repr ((e R k i + e R k j) * y) (i ^^^ x) =
      (if negSign k i x then -(basis R k).repr y x else (basis R k).repr y x) +
        (if negSign k j (partner i j x) then -(basis R k).repr y (partner i j x)
          else (basis R k).repr y (partner i j x)) := by
  rw [add_mul, map_add, Finsupp.add_apply, repr_e_mul, repr_e_mul, xor_xor_cancel_left,
    xor_xor_eq_partner]

theorem repr_e_sub_e_mul {k : ℕ} (i j x : BitVec k) (y : Tower R k) :
    (basis R k).repr ((e R k i - e R k j) * y) (i ^^^ x) =
      (if negSign k i x then -(basis R k).repr y x else (basis R k).repr y x) -
        (if negSign k j (partner i j x) then -(basis R k).repr y (partner i j x)
          else (basis R k).repr y (partner i j x)) := by
  rw [sub_mul, map_sub, Finsupp.sub_apply, repr_e_mul, repr_e_mul, xor_xor_cancel_left,
    xor_xor_eq_partner]

omit [TrivialStar R] in
/-- `y` lies in the kernel of `L` exactly when every coordinate of `L y` at
an index `i ^^^ x` vanishes. -/
theorem mem_ker_iff_repr_xor {k : ℕ} (i : BitVec k) (L : Tower R k →ₗ[R] Tower R k)
    (y : Tower R k) :
    y ∈ LinearMap.ker L ↔ ∀ x, (basis R k).repr (L y) (i ^^^ x) = 0 := by
  rw [LinearMap.mem_ker]
  constructor
  · intro h x
    rw [h, map_zero, Finsupp.zero_apply]
  · intro h
    apply (basis R k).repr.injective
    ext w
    have := h (i ^^^ w)
    rw [xor_xor_cancel_left] at this
    rw [this, map_zero, Finsupp.zero_apply]

/-- The kernel of left multiplication by `e i + e j` in coordinates. -/
theorem mem_ker_mulLeft_e_add_e {k : ℕ} (i j : BitVec k) (y : Tower R k) :
    y ∈ LinearMap.ker (mulLeft R k (e R k i + e R k j)) ↔
      (basis R k).equivFun y ∈ pairedSubmodule (partner i j) (pairSign i j) := by
  rw [mem_ker_iff_repr_xor i, mem_pairedSubmodule]
  refine forall_congr' fun x => ?_
  rw [mulLeft_apply, repr_e_add_e_mul, pairSign]
  simp only [Basis.equivFun_apply]
  cases negSign k i x <;> cases negSign k j (partner i j x) <;>
    simp only [Bool.false_eq_true, ↓reduceIte, Bool.xor_false, Bool.xor_true, Bool.not_false,
      Bool.not_true] <;>
    constructor <;> intro h <;> first | linear_combination h | linear_combination -h

/-- The kernel of left multiplication by `e i - e j` in coordinates: the
relation at each index is that of `e i + e j` with the sign reversed. -/
theorem mem_ker_mulLeft_e_sub_e {k : ℕ} (i j : BitVec k) (y : Tower R k) :
    y ∈ LinearMap.ker (mulLeft R k (e R k i - e R k j)) ↔
      (basis R k).equivFun y ∈ pairedSubmodule (partner i j) (fun x => !pairSign i j x) := by
  rw [mem_ker_iff_repr_xor i, mem_pairedSubmodule]
  refine forall_congr' fun x => ?_
  rw [mulLeft_apply, repr_e_sub_e_mul, pairSign]
  simp only [Basis.equivFun_apply]
  cases negSign k i x <;> cases negSign k j (partner i j x) <;>
    simp only [Bool.false_eq_true, ↓reduceIte, Bool.xor_false, Bool.xor_true, Bool.not_false,
      Bool.not_true] <;>
    constructor <;> intro h <;> first | linear_combination h | linear_combination -h

omit [TrivialStar R] in
theorem finrank_ker_eq_paired {k : ℕ} (L : Tower R k →ₗ[R] Tower R k) (δ : BitVec k → Bool)
    (σ : BitVec k → BitVec k)
    (hL : ∀ y, y ∈ LinearMap.ker L ↔ (basis R k).equivFun y ∈ pairedSubmodule σ δ) :
    finrank R (LinearMap.ker L) = finrank R (pairedSubmodule (R := R) σ δ) := by
  rw [← (basis R k).equivFun.finrank_map_eq]
  congr 2 <;>
  · ext z
    rw [Submodule.mem_map_equiv, hL, LinearEquiv.apply_symm_apply]

omit [StarRing R] [TrivialStar R] in
theorem add_self_eq_zero_of_isLeftRegular (h2 : IsLeftRegular (2 : R)) (a : R)
    (h : a + a = 0) : a = 0 :=
  h2 (show 2 * a = 2 * 0 by rw [two_mul, h, mul_zero])

/-- The nullity of left multiplication by `e i + e j` is the number of
aligned pairs, at every level `k` and for all indices `i` and `j`, over
every nontrivial commutative ring with the identity as star in which `2` is
a non-zero-divisor. For `i = j` both sides are `0`. -/
theorem finrank_ker_mulLeft_e_add_e [Nontrivial R] (h2 : IsLeftRegular (2 : R)) (k : ℕ)
    (i j : BitVec k) :
    finrank R (LinearMap.ker (mulLeft R k (e R k i + e R k j))) = alignedPairCount k i j := by
  have hσ : ∀ x, partner i j (partner i j x) = x := partner_partner i j
  have hfix : ∀ x, partner i j x = x → pairSign i j x = false := by
    intro x hx
    unfold pairSign
    rw [(partner_eq_self_iff i j x).1 hx, (partner_eq_self_iff j j x).2 rfl]
    simp
  rw [finrank_ker_eq_paired _ _ _ (mem_ker_mulLeft_e_add_e i j),
    finrank_pairedSubmodule (key := BitVec.toNat) hσ hfix
      (fun _ _ h => BitVec.eq_of_toNat_eq h) (add_self_eq_zero_of_isLeftRegular h2)]
  by_cases hij : i = j
  · subst hij
    rw [alignedPairCount_self, Finset.card_eq_zero, Finset.filter_eq_empty_iff]
    intro x _ hx
    have := hx.1
    rw [(partner_eq_self_iff i i x).2 rfl] at this
    exact lt_irrefl _ this
  · have hne : ∀ x, partner i j x ≠ x := fun x h => hij ((partner_eq_self_iff i j x).1 h)
    rw [alignedPairCount_eq_card hij]
    simp only [aligned_iff_pairSign]
    rw [card_agree_eq_two_mul hσ hne (fun _ _ h => BitVec.eq_of_toNat_eq h),
      Nat.mul_div_cancel_left _ two_pos]

/-- The nullity of left multiplication by `e i - e j` is the number of
aligned pairs, for `i ≠ j`, under the hypotheses of
`finrank_ker_mulLeft_e_add_e`. For `i = j` the operand is `0`. -/
theorem finrank_ker_mulLeft_e_sub_e [Nontrivial R] (h2 : IsLeftRegular (2 : R)) (k : ℕ)
    {i j : BitVec k} (hij : i ≠ j) :
    finrank R (LinearMap.ker (mulLeft R k (e R k i - e R k j))) = alignedPairCount k i j := by
  have hσ : ∀ x, partner i j (partner i j x) = x := partner_partner i j
  have hne : ∀ x, partner i j x ≠ x := fun x h => hij ((partner_eq_self_iff i j x).1 h)
  rw [finrank_ker_eq_paired _ _ _ (mem_ker_mulLeft_e_sub_e i j),
    finrank_pairedSubmodule (key := BitVec.toNat) hσ (fun x hx => absurd hx (hne x))
      (fun _ _ h => BitVec.eq_of_toNat_eq h) (add_self_eq_zero_of_isLeftRegular h2),
    alignedPairCount_eq_card hij]
  simp only [aligned_iff_pairSign]
  rw [card_agree_eq_two_mul hσ hne (fun _ _ h => BitVec.eq_of_toNat_eq h),
    Nat.mul_div_cancel_left _ two_pos]
  congr 1
  ext x
  simp [IsPairRep]

/-- Over a field of characteristic zero the hypothesis on `2` holds. -/
theorem finrank_ker_mulLeft_e_add_e_of_charZero {K : Type u} [Field K] [CharZero K]
    [StarRing K] [TrivialStar K] (k : ℕ) (i j : BitVec k) :
    finrank K (LinearMap.ker (mulLeft K k (e K k i + e K k j))) = alignedPairCount k i j :=
  finrank_ker_mulLeft_e_add_e (fun _ _ h => mul_left_cancel₀ two_ne_zero h) k i j

/-- The `A_5` operand `e_1 + e_18` has a twelve-dimensional kernel over the
rationals. -/
theorem finrank_ker_pathion_1_18 :
    finrank ℚ (LinearMap.ker (mulLeft ℚ 5 (e ℚ 5 1#5 + e ℚ 5 18#5))) = 12 := by
  rw [finrank_ker_mulLeft_e_add_e_of_charZero, alignedPairCount_pathion_1_18]

/-- Over the integers, where `2` is not a unit, the kernel of `e_1 + e_18`
on `A_5` has rank twelve. The statement elaborates `finrank ℤ` with the
`ℤ`-module structure of the additive group, which `Subsingleton` identifies
with the one of `Tower.instModule`. -/
theorem finrank_ker_pathion_1_18_int :
    finrank ℤ (LinearMap.ker (mulLeft ℤ 5 (e ℤ 5 1#5 + e ℤ 5 18#5))) = 12 := by
  have h := finrank_ker_mulLeft_e_add_e (R := ℤ)
    (fun _ _ h => mul_left_cancel₀ two_ne_zero h) 5 1#5 18#5
  rw [alignedPairCount_pathion_1_18] at h
  convert h using 2
  exact Subsingleton.elim _ _

end Tower

end CayleyDickson
