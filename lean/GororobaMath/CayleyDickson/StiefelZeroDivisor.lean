/- SPDX-License-Identifier: Apache-2.0 -/
module

public import GororobaMath.CayleyDickson.PureDoublingTransport
public import GororobaMath.LinearAlgebra.PfaffianSixteenSchur
public import GororobaMath.LinearAlgebra.PfaffianForm

/-!
# Every A_5 Stiefel element is a zero divisor over a field with a square root of `-1`

Convention: `Tower K k` is the Cayley-Dickson tower of `GororobaMath.CayleyDickson.Tower` over a
field `K` whose star is the identity, `dot k` is its trace form (the bilinear sum of products of
coordinates, with no conjugation), and `re k` is the coordinate of `1`. An element `mk p q` of
`Tower K 5` has `p` and `q` pure when `re 4 p = re 4 q = 0`. `ι : K` satisfies `ι * ι = -1`.
Coordinates are read at `BitVec.ofNat 4 n` for `n < 16`, as in
`GororobaMath.CayleyDickson.PureDoublingTransport`; `z = p + ι q` and `w = p - ι q`.

The proof composes three results. `Q (z) = dot p p - dot q q + 2 ι dot p q = 0`, so the identity
`PfaffianSixteenSchur.pfaffian_sixteen` makes the Pfaffian of `borderedA z w` zero;
`Matrix.exists_mulVec_eq_zero_of_pfaffian_eq_zero` gives a nonzero kernel vector `v`; and
`x = mk (v / 2) (ι star (v / 2))` has `Ψ = v` and `r + ι star s = 0`, so the two halves of the
transport (`phi_mul_coord_sixteen`, `psi_mul_coord_sixteen`) put both `φ (y x)` and `ψ (y x)` at
zero, which makes `y x = 0` when `2 ≠ 0`.

## Main results

* `Tower.stiefel_zero_divisor`: over a field with `2 ≠ 0` and `ι * ι = -1`, for pure `p`, `q` of
  `Tower K 4` with `dot p p = dot q q` and `dot p q = 0`, some `x ≠ 0` of `Tower K 5` has
  `mk p q * x = 0`.
-/

@[expose] public section

namespace CayleyDickson

namespace Tower

universe u

variable {K : Type u} [Field K] [StarRing K] [TrivialStar K]

omit [TrivialStar K] in
/-- The trace form of level `4` as a sum over the nonzero indices when the first factor is pure. -/
theorem dot_four_eq (u v : Tower K 4) (hu : (basis K 4).repr u 0#4 = 0) :
    dot 4 u v = ∑ k ∈ Finset.range 15, (basis K 4).repr u (BitVec.ofNat 4 (k + 1)) *
      (basis K 4).repr v (BitVec.ofNat 4 (k + 1)) := by
  rw [dot_eq_sum_repr]
  have h := Fintype.sum_bijective (fun a : Fin 16 => BitVec.ofNat 4 a.val) ofNat_four_bijective
    (fun a : Fin 16 => (basis K 4).repr u (BitVec.ofNat 4 a.val) *
      (basis K 4).repr v (BitVec.ofNat 4 a.val))
    (fun b => (basis K 4).repr u b * (basis K 4).repr v b) (fun _ => rfl)
  rw [← h, Fin.sum_univ_eq_sum_range (fun n => (basis K 4).repr u (BitVec.ofNat 4 n) *
    (basis K 4).repr v (BitVec.ofNat 4 n)) 16, Finset.sum_range_succ']
  simp only [hu, zero_mul, add_zero]

/-- The zero-divisor theorem at level `5`: for pure `p`, `q` of equal norm and zero dot product the
bordered quadratic vanishes, `pfaffian_sixteen` gives the Pfaffian `0`, a kernel vector `v` of the
skew bordered matrix exists, and `x = mk (v/2) (ι • star (v/2))` is annihilated by `mk p q`. -/
theorem stiefel_zero_divisor (h2 : (2 : K) ≠ 0) (ι : K) (hι : ι * ι = -1) {p q : Tower K 4}
    (hp : re 4 p = 0) (hq : re 4 q = 0) (hpp : dot 4 p p = dot 4 q q) (hpq : dot 4 p q = 0) :
    ∃ x : Tower K 5, x ≠ 0 ∧ mk p q * x = 0 := by
  have hp0 : (basis K 4).repr p 0#4 = 0 := by rw [← re_eq_repr_zero, hp]
  have hq0 : (basis K 4).repr q 0#4 = 0 := by rw [← re_eq_repr_zero, hq]
  have hι0 : ι ≠ 0 := fun h => by rw [h] at hι; simp at hι
  let z : ℕ → K := fun n => (basis K 4).repr p (BitVec.ofNat 4 n) +
    ι * (basis K 4).repr q (BitVec.ofNat 4 n)
  let w : ℕ → K := fun n => (basis K 4).repr p (BitVec.ofNat 4 n) -
    ι * (basis K 4).repr q (BitVec.ofNat 4 n)
  have hQ : PfaffianSixteen.qv z = 0 := by
    have e1 := dot_four_eq p p hp0
    have e2 := dot_four_eq q q hq0
    have e3 := dot_four_eq p q hp0
    have hterm : ∀ k : ℕ, z (k + 1) * z (k + 1) =
        (basis K 4).repr p (BitVec.ofNat 4 (k + 1)) * (basis K 4).repr p (BitVec.ofNat 4 (k + 1)) +
        2 * ι * ((basis K 4).repr p (BitVec.ofNat 4 (k + 1)) *
          (basis K 4).repr q (BitVec.ofNat 4 (k + 1))) -
        (basis K 4).repr q (BitVec.ofNat 4 (k + 1)) * (basis K 4).repr q (BitVec.ofNat 4 (k + 1)) :=
      fun k => by
        simp only [z]
        linear_combination ((basis K 4).repr q (BitVec.ofNat 4 (k + 1)) ^ 2) * hι
    simp only [PfaffianSixteen.qv, hterm, Finset.sum_sub_distrib, Finset.sum_add_distrib,
      ← Finset.mul_sum]
    rw [← e1, ← e2, ← e3, hpq, hpp]
    ring
  have hpf : Matrix.pfaffian (PfaffianSixteenSchur.A16 z w) = 0 := by
    have h := PfaffianSixteenSchur.pfaffian_sixteen z w
    rw [PfaffianSixteen.rhsv, hQ] at h
    change Matrix.pfaffian (Matrix.of fun a b : Fin 16 => PfaffianSixteen.borderedA z w a b) = 0
    simpa using h
  obtain ⟨v, hv0, hv⟩ := Matrix.exists_mulVec_eq_zero_of_pfaffian_eq_zero h2
    (PfaffianSixteenSchur.A16 z w) (PfaffianSixteenSchur.A16_skew z w) hpf
  let f : BitVec 4 → K := fun b => v ((Equiv.ofBijective _ ofNat_four_bijective).symm b) / 2
  let r : Tower K 4 := (basis K 4).repr.symm (Finsupp.equivFunOnFinite.symm f)
  have hr : ∀ b, (basis K 4).repr r b = f b := fun b => by
    simp [r]
  have hrv : ∀ e : Fin 16, (basis K 4).repr r (BitVec.ofNat 4 e.val) = v e / 2 := fun e => by
    rw [hr]
    have : (Equiv.ofBijective _ ofNat_four_bijective).symm (BitVec.ofNat 4 e.val) = e :=
      (Equiv.symm_apply_eq _).mpr rfl
    simp only [f, this]
  let s : Tower K 4 := ι • star r
  have hs : star s = ι • r := by simp only [s, star_smul', star_star]
  have hΨ : r - ι • star s = (2 : K) • r := by
    rw [hs, smul_smul, hι]
    module
  have hΦ : r + ι • star s = 0 := by
    rw [hs, smul_smul, hι]
    module
  have hphi : ∀ m : Fin 16,
      (basis K 4).repr (phi ι (mk p q * mk r s)) (BitVec.ofNat 4 m.val) = 0 := by
    intro m
    have key := phi_mul_coord_sixteen ι hι hp0 hq0 r s m
    rw [key]
    have hm := congrFun hv m
    simp only [Matrix.mulVec, dotProduct, Pi.zero_apply] at hm
    rw [← hm]
    refine Finset.sum_congr rfl fun e _ => ?_
    rw [hΨ]
    simp only [map_smul, Finsupp.smul_apply, smul_eq_mul, hrv]
    simp only [PfaffianSixteenSchur.A16, Matrix.of_apply, z, w]
    congr 1
    field_simp
  have hpsi : ∀ m : Fin 16,
      (basis K 4).repr (phi (-ι) (mk p q * mk r s)) (BitVec.ofNat 4 m.val) = 0 := by
    intro m
    rw [psi_mul_coord_sixteen ι hι hp0 hq0 r s m, hΦ]
    simp
  have hall : ∀ (c : K) (hc : ∀ m : Fin 16, (basis K 4).repr (phi c (mk p q * mk r s))
      (BitVec.ofNat 4 m.val) = 0), phi c (mk p q * mk r s) = 0 := by
    intro c hc
    refine (basis K 4).ext_elem fun b => ?_
    obtain ⟨m, hm⟩ := ofNat_four_bijective.2 b
    simp only at hm
    rw [← hm, hc m]
    simp
  have h1 := hall ι hphi
  have h2' := hall (-ι) hpsi
  rw [mk_mul_mk, phi_mk] at h1 h2'
  set A' : Tower K 4 := p * r - star s * q
  set B' : Tower K 4 := s * p + q * star r
  have hB : star B' = 0 := by
    have : (2 * ι) • star B' = 0 := by
      rw [show (2 * ι) • star B' = (A' + ι • star B') - (A' + (-ι) • star B') by module]
      rw [h1, h2', sub_zero]
    rcases smul_eq_zero.mp this with h | h
    · exact absurd h (mul_ne_zero h2 hι0)
    · exact h
  have hA : A' = 0 := by
    have : (2 : K) • A' = 0 := by
      rw [show (2 : K) • A' = (A' + ι • star B') + (A' + (-ι) • star B') by module, h1, h2',
        add_zero]
    rcases smul_eq_zero.mp this with h | h
    · exact absurd h h2
    · exact h
  have hB' : B' = 0 := by
    have := congrArg star hB
    rwa [star_star, star_zero] at this
  refine ⟨mk r s, ?_, ?_⟩
  · intro hx
    have hr0 : r = 0 := ((mk_inj (a := r) (b := s) (c := 0) (d := 0)).mp
      (by rw [hx]; rfl)).1
    apply hv0
    funext e
    have := hrv e
    rw [hr0] at this
    simp only [map_zero, Finsupp.zero_apply] at this
    have h3 : v e / 2 = 0 := this.symm
    simpa [h2] using h3
  · rw [mk_mul_mk]
    change mk A' B' = 0
    rw [hA, hB']
    rfl

end Tower

end CayleyDickson
