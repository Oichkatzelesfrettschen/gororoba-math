/- SPDX-License-Identifier: Apache-2.0 -/
module

public import GororobaMath.CayleyDickson.TowerModule
public import Mathlib.LinearAlgebra.Matrix.ToLin

/-!
# The matrix `C_z` of left multiplication by a pure element: entries, skewness, `C_z z = 0`

Convention: the product of `Tower R k` is the Cayley-Dickson product of
`GororobaMath.CayleyDickson.Tower` over a commutative ring `R` whose star is the identity, the
coordinate of `x` at `p` is `(Tower.basis R k).repr x p`, and the basis element at index `p` is
`Tower.e R k p` with the index of `cd_core.cd_sign` (`p.toNat`). A pure element is one whose
coordinate at index `0` vanishes. `Tower.czMatrix z` is the square matrix on the nonzero
indices, the basis `e_1, ..., e_(2^k - 1)`, whose entry at row `r` and column `c` is the
coordinate at `r` of `z * e_c`. It is `_c_matrix` of
`docs/evidence/a5-kernel-attachments/holomorphic_kernel_lemma.py` in gororoba-quantum, whose entry
`(r, c)` is `cd_sign(16, r xor c, c) * z_(r xor c)` at level 4, with `z` the vector of
coordinates of a pure element; `Tower.czMatrix_apply` proves that formula with
`Tower.sign k (r ^^^ c) c` for `cd_sign` at every level and over every commutative ring.

For a pure `z` the full matrix of left multiplication by `z` on all indices is the bordered
skew matrix `[[0, -z^T], [z, C_z]]`, since `z * 1 = z` and the coordinate of `z * e_c` at `0` is
`-z_c`; its kernel is the subject of the bordered-kernel splitting.

## Main results

* `Tower.repr_mul_e`: the coordinate of `z * e_c` at `r` is `sign (r ^^^ c) c * z_(r ^^^ c)`, for
  every `z`.
* `Tower.czMatrix_apply`: the entry formula of `czMatrix`.
* `Tower.czMatrix_transpose`: `(C_z)^T = -C_z` for a pure `z`, over every commutative ring.
* `Tower.czMatrix_mulVec_repr`: `C_z z = 0` for a pure `z`, over every commutative ring; the sum
  over the nonzero indices cancels in pairs `c <-> r ^^^ c` without dividing by 2.
-/

@[expose] public section

namespace CayleyDickson

namespace Tower

universe u

open Matrix

variable {R : Type u} [CommRing R] [StarRing R] [TrivialStar R] {k : ℕ}

/-- The sign of `e p * e (p ^^^ q)` is that of `e p * e q` reversed, for `p ≠ 0`. -/
theorem sign_xor_right {p : BitVec k} (hp : p ≠ 0#k) (q : BitVec k) :
    sign k p (p ^^^ q) = -sign k p q := by
  cases h : negSign k p q <;> simp [sign, negSign_xor_right, hp, h]

/-- Exchanging two distinct nonzero indices reverses the sign of the product. -/
theorem sign_swap {p q : BitVec k} (hp : p ≠ 0#k) (hq : q ≠ 0#k) (hpq : p ≠ q) :
    sign k q p = -sign k p q := by
  rw [sign, sign, negSign_swap k p q hp hq hpq]
  cases negSign k p q <;> simp

theorem xor_xor_cancel_right' (a c : BitVec k) : (a ^^^ c) ^^^ c = a := by
  rw [BitVec.xor_assoc, BitVec.xor_self, BitVec.xor_zero]

/-- The coordinate of `z * e c` at `r` is `sign (r ^^^ c) c` times the coordinate of `z` at
`r ^^^ c`, because right multiplication by `e c` sends `e p` to `sign p c • e (p ^^^ c)`. -/
theorem repr_mul_e (z : Tower R k) (c r : BitVec k) :
    (basis R k).repr (z * e R k c) r =
      (sign k (r ^^^ c) c : R) * (basis R k).repr z (r ^^^ c) := by
  let mr : Tower R k →ₗ[R] Tower R k :=
    { toFun := fun y => y * e R k c
      map_add' := fun x y => add_mul x y _
      map_smul' := fun a y => smul_mul_assoc' a y _ }
  let F : Tower R k →ₗ[R] R := (basis R k).coord r ∘ₗ mr
  let G : Tower R k →ₗ[R] R := (sign k (r ^^^ c) c : R) • (basis R k).coord (r ^^^ c)
  have hFG : F = G := by
    refine (basis R k).ext fun p => ?_
    simp only [F, G, mr, LinearMap.comp_apply, LinearMap.coe_mk, AddHom.coe_mk,
      Module.Basis.coord_apply, LinearMap.smul_apply, basis_apply, smul_eq_mul]
    rw [e_mul_e]
    by_cases h : p = r ^^^ c
    · subst h
      rw [xor_xor_cancel_right']
      cases hn : negSign k (r ^^^ c) c <;> simp [sign, hn, repr_e]
    · have h' : p ^^^ c ≠ r := fun h2 => h (by rw [← h2, xor_xor_cancel_right'])
      cases hn : negSign k p c <;> simp [repr_e, h, h']
  have := LinearMap.congr_fun hFG z
  simpa [F, G, mr] using this

/-- The nonzero indices of level `k`: the basis `e_1, ..., e_(2^k - 1)` of the pure part. -/
abbrev NonzeroIndex (k : ℕ) : Type := {p : BitVec k // p ≠ 0#k}

/-- The matrix of left multiplication by `z` from the span of `e_c` (`c ≠ 0`) to the
coordinates at `e_r` (`r ≠ 0`): the entry at `(r, c)` is the coordinate at `r` of
`z * e c`. It is `_c_matrix` of `holomorphic_kernel_lemma.py`. -/
noncomputable def czMatrix (z : Tower R k) : Matrix (NonzeroIndex k) (NonzeroIndex k) R :=
  fun r c => (basis R k).repr (z * e R k c.1) r.1

/-- The entry of `czMatrix z` at `(r, c)` is `sign (r ^^^ c) c * z_(r ^^^ c)`, the
`cd_sign(16, r xor c, c) * z_(r xor c)` of `_c_matrix` at level 4. -/
theorem czMatrix_apply (z : Tower R k) (r c : NonzeroIndex k) :
    czMatrix z r c = (sign k (r.1 ^^^ c.1) c.1 : R) * (basis R k).repr z (r.1 ^^^ c.1) :=
  repr_mul_e z c.1 r.1

omit [TrivialStar R] in
/-- One entry of the skewness: the entries at `(c, r)` and `(r, c)` of a pure element
add to zero, because the signs of `e p * e c` and `e p * e (p ^^^ c)` are opposite. -/
theorem sign_mul_repr_skew {z : Tower R k} (hz : (basis R k).repr z 0#k = 0) (r c : BitVec k) :
    (sign k (c ^^^ r) r : R) * (basis R k).repr z (c ^^^ r) =
      -((sign k (r ^^^ c) c : R) * (basis R k).repr z (r ^^^ c)) := by
  obtain ⟨p, rfl⟩ : ∃ p, r = p ^^^ c := ⟨r ^^^ c, (xor_xor_cancel_right' r c).symm⟩
  have h1 : c ^^^ (p ^^^ c) = p := by
    rw [BitVec.xor_comm p c, ← BitVec.xor_assoc, BitVec.xor_self, BitVec.zero_xor]
  rw [h1, xor_xor_cancel_right']
  by_cases hp : p = 0#k
  · subst hp
    simp [hz]
  · rw [sign_xor_right hp]
    push_cast
    ring

/-- For a pure `z` the matrix `C_z` is skew: `(C_z)^T = -C_z`, over every commutative ring
whose star is the identity. -/
theorem czMatrix_transpose {z : Tower R k} (hz : (basis R k).repr z 0#k = 0) :
    (czMatrix z).transpose = -czMatrix z := by
  ext r c
  simp only [Matrix.transpose_apply, Matrix.neg_apply, czMatrix_apply]
  exact sign_mul_repr_skew hz r.1 c.1

/-- `C_z z = 0` for a pure `z`, where `z` is the vector of its coordinates at the nonzero
indices: the terms at `c` and `r ^^^ c` of row `r` cancel by the reversal of the sign of
two distinct nonzero basis elements, and the terms at `c = 0` and `c = r` carry the coordinate
of `z` at `0`. -/
theorem czMatrix_mulVec_repr {z : Tower R k} (hz : (basis R k).repr z 0#k = 0) :
    czMatrix z *ᵥ (fun c : NonzeroIndex k => (basis R k).repr z c.1) = 0 := by
  classical
  funext r
  simp only [Matrix.mulVec, dotProduct, Pi.zero_apply]
  set t : BitVec k → R := fun c =>
    (sign k (r.1 ^^^ c) c : R) * (basis R k).repr z (r.1 ^^^ c) * (basis R k).repr z c with ht
  have ht0 : t 0#k = 0 := by simp [ht, hz]
  have hrr : t r.1 = 0 := by simp [ht, hz]
  have hsub : ∑ c : NonzeroIndex k, t c.1 =
      ∑ c ∈ Finset.univ.filter (fun c : BitVec k => c ≠ 0#k), t c :=
    (Finset.sum_subtype (Finset.univ.filter (fun c : BitVec k => c ≠ 0#k)) (by simp) t).symm
  have hall : ∑ c ∈ Finset.univ.filter (fun c : BitVec k => c ≠ 0#k), t c = ∑ c, t c := by
    rw [Finset.sum_filter]
    refine Finset.sum_congr rfl fun c _ => ?_
    by_cases hc : c = 0#k
    · simp [hc, ht0]
    · simp [hc]
  have hcz : (∑ c : NonzeroIndex k, czMatrix z r c * (basis R k).repr z c.1) =
      ∑ c : NonzeroIndex k, t c.1 :=
    Finset.sum_congr rfl fun c _ => by simp only [czMatrix_apply, ht]
  rw [hcz, hsub, hall]
  refine Finset.sum_ninvolution (fun a => r.1 ^^^ a) ?_ ?_ (fun a => Finset.mem_univ _) ?_
  · intro a
    have hxx : r.1 ^^^ (r.1 ^^^ a) = a := by
      rw [← BitVec.xor_assoc, BitVec.xor_self, BitVec.zero_xor]
    by_cases ha0 : a = 0#k
    · subst ha0
      simp [ht0, hrr, BitVec.xor_zero]
    by_cases har : a = r.1
    · subst har
      simp [ht0, hrr]
    have hb : r.1 ^^^ a ≠ 0#k := fun h => har (BitVec.xor_eq_zero_iff.mp h).symm
    have hne : r.1 ^^^ a ≠ a := fun h => r.2 (by
      have h2 : (r.1 ^^^ a) ^^^ a = a ^^^ a := by rw [h]
      rwa [xor_xor_cancel_right', BitVec.xor_self] at h2)
    have hs := sign_swap (k := k) hb ha0 hne
    simp only [ht, hxx]
    rw [hs]
    push_cast
    ring
  · intro a _ h
    apply r.2
    have h2 : (r.1 ^^^ a) ^^^ a = a ^^^ a := by rw [h]
    rwa [xor_xor_cancel_right', BitVec.xor_self] at h2
  · intro a
    rw [← BitVec.xor_assoc, BitVec.xor_self, BitVec.zero_xor]

end Tower

end CayleyDickson
