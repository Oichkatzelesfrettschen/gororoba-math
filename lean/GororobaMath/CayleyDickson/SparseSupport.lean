/- SPDX-License-Identifier: Apache-2.0 -/
module

public import GororobaMath.CayleyDickson.TowerModule

/-!
# Products of operands supported on an XOR coset

Convention: the product of `Tower R k` is the Cayley-Dickson product of
`GororobaMath.CayleyDickson.Tower`, over a commutative ring whose star is the identity, and
`(basis R k).repr x p` is the coordinate of `x` on the basis element `e R k p`, `p : BitVec k`
with the most significant bit outermost. A set `G` of indices that contains `0` and is closed
under `^^^` is an XOR subgroup; an element `y` is supported on the coset `s ^^^ G` when its
coordinate at `p` vanishes unless `s ^^^ p ∈ G`. The coordinate of a product is
`repr (y * v) p = ∑ i, repr y i * ± repr v (i ^^^ p)` (`Tower.repr_e_mul`), so a nonzero
coordinate at `p` needs an index `i` in the support of `y` with `i ^^^ p` in the support of `v`
(`Tower.exists_repr_ne_zero_of_mul`).

## Main results

* `Tower.repr_mul_ne_zero_mem`: operands supported on the cosets `s ^^^ G` and `t ^^^ G` have a
  product supported on `s ^^^ t ^^^ G`. The Rocq original is `sparse_support_transport` of
  `rocq/open/theories/CDSparseBlockTransport.v`, whose `sparse_cd_apply` sums
  `operand (output XOR input)` times the sign times `vector input`.
* `Tower.mul_eq_zero_iff_forall_sector`: for an operand supported on one coset, a vector is
  annihilated exactly when each of its sector projections `Tower.sectorProj G c v`, the part of
  `v` supported on the coset `c ^^^ G`, is annihilated. The Rocq originals are
  `sparse_kernel_decomposition` of `rocq/open/theories/CDSparseBlockTransport.v` and the kernel
  form of `sparse_field_rank_decomposition` of
  `rocq/open/theories/CDSparseMatrixTransport.v`.
-/

@[expose] public section

namespace CayleyDickson

namespace Tower

universe u

theorem xor_aux1 {k : ℕ} (a b c d : BitVec k) : a ^^^ b ^^^ (c ^^^ (b ^^^ d)) = a ^^^ c ^^^ d := by
  have h : ∀ a b c d : Bool, (a ^^ b ^^ (c ^^ (b ^^ d))) = (a ^^ c ^^ d) := by decide
  ext j hj
  simp only [BitVec.getElem_xor]
  exact h _ _ _ _

theorem xor_aux2 {k : ℕ} (s c p i : BitVec k) :
    s ^^^ c ^^^ p ^^^ (s ^^^ i) = c ^^^ (i ^^^ p) := by
  have h : ∀ s c p i : Bool, (s ^^ c ^^ p ^^ (s ^^ i)) = (c ^^ (i ^^ p)) := by decide
  ext j hj
  simp only [BitVec.getElem_xor]
  exact h _ _ _ _

theorem xor_aux1' {k : ℕ} (s i c p : BitVec k) : s ^^^ i ^^^ (c ^^^ (i ^^^ p)) = s ^^^ c ^^^ p := xor_aux1 s i c p

theorem xor_aux3 {k : ℕ} (s p : BitVec k) : s ^^^ (s ^^^ p) ^^^ p = 0#k := by
  have h : ∀ s p : Bool, (s ^^ (s ^^ p) ^^ p) = false := by decide
  ext j hj
  simp only [BitVec.getElem_xor, BitVec.getElem_zero]
  exact h _ _

variable {R : Type u} [CommRing R] [StarRing R] [TrivialStar R]

/-- A nonzero coordinate of a product comes from an index of the left support whose XOR with the
output index lies in the right support. -/
theorem exists_repr_ne_zero_of_mul {k : ℕ} (y v : Tower R k) (p : BitVec k)
    (h : (basis R k).repr (y * v) p ≠ 0) :
    ∃ i, (basis R k).repr y i ≠ 0 ∧ (basis R k).repr v (i ^^^ p) ≠ 0 := by
  have hy := (basis R k).sum_repr y
  simp only [coe_basis] at hy
  have key : y * v = ∑ i, (basis R k).repr y i • (e R k i * v) := by
    conv_lhs => rw [← hy]
    rw [Finset.sum_mul]
    simp [smul_mul_assoc']
  rw [key] at h
  simp only [map_sum, map_smul, Finsupp.coe_finsetSum, Finset.sum_apply, Finsupp.smul_apply,
    smul_eq_mul] at h
  obtain ⟨i, _, hi⟩ := Finset.exists_ne_zero_of_sum_ne_zero h
  have h1 := left_ne_zero_of_mul hi
  have h2 := right_ne_zero_of_mul hi
  refine ⟨i, h1, ?_⟩
  rw [repr_e_mul] at h2
  split_ifs at h2 with hs
  · exact neg_ne_zero.1 h2
  · exact h2

/-- Operands supported on XOR cosets `s ^^^ G` and `t ^^^ G` of a subgroup `G` have a product
supported on `s ^^^ t ^^^ G`. The Rocq original is `sparse_support_transport` of
`rocq/open/theories/CDSparseBlockTransport.v`. -/
theorem repr_mul_ne_zero_mem {k : ℕ} {G : Set (BitVec k)} (hG0 : 0#k ∈ G)
    (hG : ∀ a ∈ G, ∀ b ∈ G, a ^^^ b ∈ G) {y v : Tower R k} {s t : BitVec k}
    (hy : ∀ p, (basis R k).repr y p ≠ 0 → s ^^^ p ∈ G)
    (hv : ∀ p, (basis R k).repr v p ≠ 0 → t ^^^ p ∈ G) (p : BitVec k)
    (hp : (basis R k).repr (y * v) p ≠ 0) : s ^^^ t ^^^ p ∈ G := by
  have _ := hG0
  obtain ⟨i, hi1, hi2⟩ := exists_repr_ne_zero_of_mul y v p hp
  have h := hG _ (hy i hi1) _ (hv _ hi2)
  rwa [xor_aux1] at h

open scoped Classical in
/-- The part of `v` supported on the coset `c ^^^ G`. -/
noncomputable def sectorProj {k : ℕ} (G : Set (BitVec k)) (c : BitVec k) (v : Tower R k) :
    Tower R k :=
  ∑ p ∈ Finset.univ.filter fun p => c ^^^ p ∈ G, (basis R k).repr v p • e R k p

omit [TrivialStar R] in
open scoped Classical in
theorem repr_sectorProj {k : ℕ} (G : Set (BitVec k)) (c : BitVec k) (v : Tower R k)
    (q : BitVec k) :
    (basis R k).repr (sectorProj G c v) q = if c ^^^ q ∈ G then (basis R k).repr v q else 0 := by
  unfold sectorProj
  simp only [map_sum, map_smul, Finsupp.coe_finsetSum, Finset.sum_apply, Finsupp.smul_apply,
    smul_eq_mul, repr_e]
  rw [Finset.sum_filter]
  simp only [mul_ite, mul_one, mul_zero]
  rw [Finset.sum_eq_single q]
  · by_cases h : c ^^^ q ∈ G <;> simp [h]
  · intro p _ hp
    simp [hp]
  · simp

/-- For an operand supported on one coset, a vector is annihilated exactly when each of its
sector projections is. The Rocq original is `sparse_kernel_decomposition` of
`rocq/open/theories/CDSparseBlockTransport.v`. -/
theorem mul_eq_zero_iff_forall_sector {k : ℕ} {G : Set (BitVec k)} (hG0 : 0#k ∈ G)
    (hG : ∀ a ∈ G, ∀ b ∈ G, a ^^^ b ∈ G) {y : Tower R k} {s : BitVec k}
    (hy : ∀ p, (basis R k).repr y p ≠ 0 → s ^^^ p ∈ G) (v : Tower R k) :
    y * v = 0 ↔ ∀ c, y * sectorProj G c v = 0 := by
  classical
  have hcoset : ∀ (c p : BitVec k), s ^^^ c ^^^ p ∈ G →
      (basis R k).repr (y * (v - sectorProj G c v)) p = 0 := by
    intro c p hp
    by_contra hne
    obtain ⟨i, hi1, hi2⟩ := exists_repr_ne_zero_of_mul y _ p hne
    rw [map_sub, Finsupp.sub_apply, repr_sectorProj] at hi2
    have hsi := hy i hi1
    have : c ^^^ (i ^^^ p) ∈ G := by
      have := hG _ hp _ hsi
      rwa [xor_aux2] at this
    simp [this] at hi2
  constructor
  · intro h c
    apply (basis R k).repr.injective
    ext p
    rw [map_zero, Finsupp.zero_apply]
    by_cases hp : s ^^^ c ^^^ p ∈ G
    · have h1 := hcoset c p hp
      rw [mul_sub, h, zero_sub, map_neg, Finsupp.neg_apply, neg_eq_zero] at h1
      exact h1
    · by_contra hne
      obtain ⟨i, hi1, hi2⟩ := exists_repr_ne_zero_of_mul y _ p hne
      rw [repr_sectorProj] at hi2
      by_cases hm : c ^^^ (i ^^^ p) ∈ G
      · apply hp
        have := hG _ (hy i hi1) _ hm
        rwa [xor_aux1'] at this
      · simp [hm] at hi2
  · intro h
    apply (basis R k).repr.injective
    ext p
    rw [map_zero, Finsupp.zero_apply]
    have h0 : s ^^^ (s ^^^ p) ^^^ p ∈ G := by rw [xor_aux3]; exact hG0
    have h1 := hcoset (s ^^^ p) p h0
    have h2 := h (s ^^^ p)
    have : y * v = y * sectorProj G (s ^^^ p) v + y * (v - sectorProj G (s ^^^ p) v) := by
      rw [← mul_add]; congr 1; abel
    rw [this, h2, zero_add]
    exact h1
