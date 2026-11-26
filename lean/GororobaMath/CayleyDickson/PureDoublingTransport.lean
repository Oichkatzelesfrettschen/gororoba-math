/- SPDX-License-Identifier: Apache-2.0 -/
module

public import GororobaMath.CayleyDickson.AnnihilatorSymmetry
public import GororobaMath.CayleyDickson.TowerModule
public import GororobaMath.CayleyDickson.TraceForm
public import GororobaMath.CayleyDickson.CzMatrix
public import GororobaMath.LinearAlgebra.PfaffianSixteen

/-!
# The doubling product of a pure pair, read through the element `Z = p + ι q`

Convention. `Tower R k` is the Cayley-Dickson tower of `GororobaMath.CayleyDickson.Tower` over a
commutative ring `R` whose star is the identity, with the product
`mk a b * mk c d = mk (a * c - star d * b) (d * a + b * star c)` (`Tower.mk_mul_mk`). An element is
pure when its coordinate of `1` (`re k`) vanishes, so its star is its negative. `ι : R` satisfies
`ι * ι = -1`. For `y = mk p q` and `x = mk r s` the two halves of `x` enter through
`Ψ = r - ι • star s`, and the two halves of `y` through `Z = p + ι • q`; the coordinate `φ (u)` of
an element `u = mk a b` of level `k + 1` is `a + ι • star b`.

## Main results

* `Tower.mul_add_mul_of_re_eq_zero`: for pure `q`, `q * u + u * q = (2 re u) • q - (2 dot q u) • 1`.
* `Tower.phi_mul_mk`: for pure `p`, `q` at any level `k`,
  `φ (mk p q * mk r s) = Z * Ψ - ι • (q * Ψ + Ψ * q)`.
* `Tower.phi_coord`: the coordinates of that element are the rows of `Tower.borderedBV z w`
  applied to the coordinates of `Ψ`, at every level `k`.
* `Tower.phi_mul_coord_sixteen`, `Tower.psi_mul_coord_sixteen`: at level `k = 4` (so `Tower R 5`
  for the product) the rows are those of `PfaffianSixteen.borderedA z w` and
  `PfaffianSixteen.borderedA w z`, composing with `PfaffianSixteenSchur.pfaffian_sixteen`.
  The Rocq partners are `transport_phi` and `transport_psi` of `StiefelTransport` in
  `rocq/quantum/StiefelA5Transport.v`, whose `phi`, `psi`, `zc`, `wc` are `φ`, `φ` at `-ι`,
  `z`, `w` here.
-/

@[expose] public section

namespace CayleyDickson

namespace Tower

universe u

variable {R : Type u} [CommRing R] [StarRing R] [TrivialStar R]

omit [TrivialStar R] in
private theorem re_smul_aux {k : ℕ} (r : R) (x : Tower R k) : re k (r • x) = r * re k x := by
  rw [← dot_one_right, dot_smul_left, dot_one_right]

omit [TrivialStar R] in
private theorem re_one_aux : ∀ k : ℕ, re k (1 : Tower R k) = 1
  | 0 => rfl
  | k + 1 => by rw [one_eq_mk, re_mk, re_one_aux k]

/-- Two pure elements anticommute up to the trace form: `q * u + u * q = -((2 dot q u) • 1)`. -/
theorem mul_add_mul_of_pure {k : ℕ} {q u : Tower R k} (hq : re k q = 0) (hu : re k u = 0) :
    q * u + u * q = -((2 * dot k q u) • (1 : Tower R k)) := by
  have hqu : re k (q + u) = 0 := by rw [re_add, hq, hu, add_zero]
  have h1 := (mul_star_eq_dot k (q + u)).1
  have h2 := (mul_star_eq_dot k q).1
  have h3 := (mul_star_eq_dot k u).1
  rw [star_eq_neg_of_re_eq_zero hqu, mul_neg, neg_eq_iff_eq_neg] at h1
  rw [star_eq_neg_of_re_eq_zero hq, mul_neg, neg_eq_iff_eq_neg] at h2
  rw [star_eq_neg_of_re_eq_zero hu, mul_neg, neg_eq_iff_eq_neg] at h3
  have h4 : dot k (q + u) (q + u) = dot k q q + dot k q u + dot k q u + dot k u u := by
    rw [dot_add_left, dot_add_right, dot_add_right, dot_comm k u q]
    ring
  have h5 : (q + u) * (q + u) = q * q + (q * u + u * q) + u * u := by
    rw [mul_add, add_mul, add_mul]
    abel
  rw [h4, h5, h2, h3] at h1
  calc q * u + u * q
      = (-(dot k q q • (1 : Tower R k)) + (q * u + u * q) + -(dot k u u • (1 : Tower R k))) +
        dot k q q • (1 : Tower R k) + dot k u u • (1 : Tower R k) := by abel
    _ = -((2 * dot k q u) • (1 : Tower R k)) := by rw [h1]; module

/-- For pure `q`: `q * u + u * q = (2 re u) • q - (2 dot q u) • 1`. -/
theorem mul_add_mul_of_re_eq_zero {k : ℕ} {q : Tower R k} (hq : re k q = 0) (u : Tower R k) :
    q * u + u * q = (2 * re k u) • q - (2 * dot k q u) • (1 : Tower R k) := by
  have hu : re k (u - re k u • (1 : Tower R k)) = 0 := by
    rw [re_sub, re_smul_aux, re_one_aux, mul_one, sub_self]
  have h := mul_add_mul_of_pure hq hu
  have hd : dot k q (u - re k u • (1 : Tower R k)) = dot k q u := by
    rw [dot_sub_right, dot_smul_right, dot_one_right, hq, mul_zero, sub_zero]
  rw [hd] at h
  have hsplit : u = (u - re k u • (1 : Tower R k)) + re k u • (1 : Tower R k) := by abel
  calc q * u + u * q
      = (q * (u - re k u • (1 : Tower R k)) + (u - re k u • (1 : Tower R k)) * q) +
        (2 * re k u) • q := by
        conv_lhs => rw [hsplit]
        rw [mul_add, add_mul, mul_smul_comm', smul_mul_assoc', mul_one, one_mul]
        module
    _ = _ := by rw [h]; module

/-- The coordinate `φ` of a doubled product: for pure `p` and `q`, with `ι * ι = -1`,
`(p * r - star s * q) + ι • star (s * p + q * star r) = Z * Ψ - ι • (q * Ψ + Ψ * q)` where
`Z = p + ι • q` and `Ψ = r - ι • star s`. The left side is `φ (mk p q * mk r s)` by
`Tower.mk_mul_mk` and `phi_mk`; the theorem itself is the expanded equation, since `phi` is
defined after it. -/
theorem phi_mul_mk {k : ℕ} (ι : R) (hι : ι * ι = -1) {p q : Tower R k} (hp : re k p = 0)
    (hq : re k q = 0) (r s : Tower R k) :
    (p * r - star s * q) + ι • star (s * p + q * star r) =
      (p + ι • q) * (r - ι • star s) - ι • (q * (r - ι • star s) + (r - ι • star s) * q) := by
  have hι' : ∀ X : Tower R k, ι • ι • X = -X := fun X => by
    rw [smul_smul, hι, neg_smul, one_smul]
  rw [star_add, star_mul, star_mul, star_star, star_eq_neg_of_re_eq_zero hp,
    star_eq_neg_of_re_eq_zero hq]
  simp only [mul_sub, sub_mul, add_mul, smul_mul_assoc', mul_smul_comm', smul_sub, smul_add,
    neg_mul, mul_neg, smul_neg, hι']
  module

omit [TrivialStar R] in
/-- The coordinate of `1` is the coordinate at the index `0`. -/
theorem re_eq_repr_zero {k : ℕ} (x : Tower R k) : re k x = (basis R k).repr x 0#k := by
  have h1 : (1 : Tower R k) = e R k 0#k := by simp
  rw [← dot_one_right, dot_eq_sum_repr, h1]
  simp only [repr_e, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq, Finset.mem_univ, ↓reduceIte]

omit [TrivialStar R] in
/-- The coordinates of `1`. -/
theorem repr_one_apply {k : ℕ} (m : BitVec k) :
    (basis R k).repr (1 : Tower R k) m = if 0#k = m then 1 else 0 := by
  have h1 : (1 : Tower R k) = e R k 0#k := by simp
  rw [h1, repr_e]

/-- The coordinate of a product at `m` is the sum over the right factor's coordinates of the signed
coordinate of the left factor at `m ^^^ e`. -/
theorem repr_mul_apply {k : ℕ} (Z Ψ : Tower R k) (m : BitVec k) :
    (basis R k).repr (Z * Ψ) m =
      ∑ e, (basis R k).repr Ψ e * ((sign k (m ^^^ e) e : R) * (basis R k).repr Z (m ^^^ e)) := by
  conv_lhs => rw [← (basis R k).sum_repr Ψ]
  rw [Finset.mul_sum, map_sum]
  simp only [Finsupp.coe_finsetSum, Finset.sum_apply, mul_smul_comm', map_smul,
    Finsupp.smul_apply, smul_eq_mul, basis_apply, repr_mul_e]

/-- The bordered matrix of the tower at an arbitrary level, on `BitVec k` indices: the border
carries `-w` in row `0` and `w` in column `0`, the rest is the signed coordinate of `z` at
`m ^^^ e`. -/
def borderedBV {k : ℕ} (z w : BitVec k → R) (m e : BitVec k) : R :=
  if m = e then 0 else if m = 0#k then -w e else if e = 0#k then w m
  else (sign k (m ^^^ e) e : R) * z (m ^^^ e)

/-- The coordinate form of the transport: for pure `p`, `q` the coordinate of
`(p * r - star s * q) + ι • star (s * p + q * star r)` at `m` is the row `m` of
`borderedBV z w` applied to the coordinates of `Ψ = r - ι • star s`, with
`z = p + ι q` and `w = p - ι q`. -/
theorem phi_coord {k : ℕ} (ι : R) (hι : ι * ι = -1) {p q : Tower R k}
    (hp : (basis R k).repr p 0#k = 0) (hq : (basis R k).repr q 0#k = 0) (r s : Tower R k)
    (m : BitVec k) :
    (basis R k).repr ((p * r - star s * q) + ι • star (s * p + q * star r)) m =
      ∑ e, borderedBV (fun a => (basis R k).repr p a + ι * (basis R k).repr q a)
        (fun a => (basis R k).repr p a - ι * (basis R k).repr q a) m e *
        (basis R k).repr (r - ι • star s) e := by
  have hpre : re k p = 0 := by rw [re_eq_repr_zero, hp]
  have hqre : re k q = 0 := by rw [re_eq_repr_zero, hq]
  rw [phi_mul_mk ι hι hpre hqre r s, mul_add_mul_of_re_eq_zero hqre]
  generalize hΨe : r - ι • star s = Ψe
  simp only [map_sub, map_smul, map_add, Finsupp.sub_apply, Finsupp.add_apply,
    Finsupp.smul_apply, smul_eq_mul, repr_mul_apply, repr_one_apply, re_eq_repr_zero,
    dot_eq_sum_repr]
  have hz0 : (basis R k).repr p 0#k + ι * (basis R k).repr q 0#k = 0 := by rw [hp, hq]; ring
  generalize hΨ : (basis R k).repr Ψe = Ψ
  have hA : ι * (2 * Ψ 0#k * (basis R k).repr q m) =
      ∑ e : BitVec k, if e = 0#k then ι * (2 * Ψ 0#k * (basis R k).repr q m) else 0 := by
    simp
  have hC : ι * ((2 * ∑ e, (basis R k).repr q e * Ψ e) * (if 0#k = m then (1 : R) else 0)) =
      ∑ e : BitVec k, if 0#k = m then ι * (2 * (basis R k).repr q e * Ψ e) else 0 := by
    split_ifs
    · rw [mul_one, Finset.mul_sum, Finset.mul_sum]
      exact Finset.sum_congr rfl fun e _ => by ring
    · simp
  have sgSelf : ∀ e : BitVec k, e ≠ 0#k → ((sign k e e : ℤ) : R) = -1 := fun e he => by
    simp [sign, negSign_self k e he]
  have sgZero : ∀ m : BitVec k, ((sign k m 0#k : ℤ) : R) = 1 := fun m => by
    simp [sign, negSign_zero_right]
  have hsum : (∑ e, Ψ e * ((sign k (m ^^^ e) e : R) * ((basis R k).repr p (m ^^^ e) +
        ι * (basis R k).repr q (m ^^^ e)))) -
      ι * (2 * Ψ 0#k * (basis R k).repr q m -
        (2 * ∑ e, (basis R k).repr q e * Ψ e) * (if 0#k = m then (1 : R) else 0)) =
      ∑ e, (Ψ e * ((sign k (m ^^^ e) e : R) * ((basis R k).repr p (m ^^^ e) +
        ι * (basis R k).repr q (m ^^^ e))) -
        (if e = 0#k then ι * (2 * Ψ 0#k * (basis R k).repr q m) else 0) +
        (if 0#k = m then ι * (2 * (basis R k).repr q e * Ψ e) else 0)) := by
    rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← hA, ← hC]
    ring
  rw [hsum]
  refine Finset.sum_congr rfl fun e _ => ?_
  by_cases hm : m = 0#k <;> by_cases he : e = 0#k
  · subst hm; subst he
    simp [borderedBV, hq, hp]
  · subst hm
    simp only [BitVec.zero_xor, sgSelf e he, neg_mul, one_mul, neg_add_rev, he, ↓reduceIte,
      sub_zero, borderedBV, Ne.symm he, neg_sub]
    ring
  · subst he
    simp only [BitVec.xor_zero, sgZero, one_mul, ↓reduceIte, Ne.symm hm, add_zero, borderedBV, hm]
    ring
  · by_cases hme : m = e
    · subst hme
      simp [borderedBV, hm, Ne.symm hm, hz0]
    · simp only [he, ↓reduceIte, sub_zero, Ne.symm hm, add_zero, borderedBV, hme, hm]
      ring

/-- The coordinate `φ` of an element `mk a b` of level `k + 1`: `a + ι • star b`. -/
def phi {k : ℕ} (ι : R) : Tower R (k + 1) → Tower R k
  | ⟨a, b⟩ => a + ι • star b

omit [TrivialStar R] in
/-- `φ` of `mk a b` is `a + ι • star b` by the definition of `phi`. -/
theorem phi_mk {k : ℕ} (ι : R) (a b : Tower R k) : phi ι (mk a b) = a + ι • star b := rfl

/-- Injectivity of the reading of `0, ..., 15` as `BitVec 4` (256 cases, one `decide +kernel`,
0.66 s measured with Lean 4.35.0). -/
theorem ofNat_four_inj :
    ∀ a b : Fin 16, BitVec.ofNat 4 a.val = BitVec.ofNat 4 b.val ↔ a.val = b.val := by
  decide +kernel

/-- The index `0` of `BitVec 4` is the reading of `0` (16 cases, one `decide +kernel`, 0.66 s
measured with Lean 4.35.0). -/
theorem ofNat_four_zero : ∀ a : Fin 16, BitVec.ofNat 4 a.val = 0#4 ↔ a.val = 0 := by
  decide +kernel

/-- The exclusive or of natural numbers below `16` is the exclusive or of their readings (256
cases, one `decide +kernel`, 0.67 s measured with Lean 4.35.0). -/
theorem ofNat_four_xor : ∀ a b : Fin 16,
    BitVec.ofNat 4 (a.val ^^^ b.val) = BitVec.ofNat 4 a.val ^^^ BitVec.ofNat 4 b.val := by
  decide +kernel

/-- The reading of `0, ..., 15` as `BitVec 4` is a bijection (injectivity from `ofNat_four_inj`,
surjectivity 16 cases by one `decide +kernel`; the declaration takes 0.68 s measured with
Lean 4.35.0). -/
theorem ofNat_four_bijective : Function.Bijective (fun a : Fin 16 => BitVec.ofNat 4 a.val) :=
  ⟨fun a b h => Fin.ext ((ofNat_four_inj a b).mp h), by decide +kernel⟩

omit [StarRing R] [TrivialStar R] in
/-- The bordered matrix of `PfaffianSixteen` is `borderedBV` on the `BitVec 4` readings of its
indices. -/
theorem borderedA_eq_borderedBV (z w : BitVec 4 → R) (a b : Fin 16) :
    PfaffianSixteen.borderedA (fun n => z (BitVec.ofNat 4 n)) (fun n => w (BitVec.ofNat 4 n)) a b =
      borderedBV z w (BitVec.ofNat 4 a.val) (BitVec.ofNat 4 b.val) := by
  simp only [PfaffianSixteen.borderedA, borderedBV, ofNat_four_inj, ofNat_four_zero,
    ofNat_four_xor]

/-- The transport of the level-5 product onto the bordered matrix of `PfaffianSixteen`: for
`y = mk p q` and `x = mk r s` with `p`, `q` pure, `ι * ι = -1`, `z = p + ι q`, `w = p - ι q` and
`Ψ = r - ι • star s` (coordinates as functions of `ℕ`), the coordinate `m` of
`φ (y * x)` is the row `m` of `borderedA z w` applied to the coordinates of `Ψ`. -/
theorem phi_mul_coord_sixteen (ι : R) (hι : ι * ι = -1) {p q : Tower R 4}
    (hp : (basis R 4).repr p 0#4 = 0) (hq : (basis R 4).repr q 0#4 = 0) (r s : Tower R 4)
    (m : Fin 16) :
    (basis R 4).repr (phi ι (mk p q * mk r s)) (BitVec.ofNat 4 m.val) =
      ∑ e : Fin 16, PfaffianSixteen.borderedA
        (fun n => (basis R 4).repr p (BitVec.ofNat 4 n) + ι * (basis R 4).repr q (BitVec.ofNat 4 n))
        (fun n => (basis R 4).repr p (BitVec.ofNat 4 n) - ι * (basis R 4).repr q (BitVec.ofNat 4 n))
        m e * (basis R 4).repr (r - ι • star s) (BitVec.ofNat 4 e.val) := by
  rw [mk_mul_mk, phi_mk, phi_coord ι hι hp hq r s]
  refine (Fintype.sum_bijective _ ofNat_four_bijective _ _ fun e => ?_).symm
  rw [borderedA_eq_borderedBV (fun a => (basis R 4).repr p a + ι * (basis R 4).repr q a)
    (fun a => (basis R 4).repr p a - ι * (basis R 4).repr q a) m e]

/-- The `ψ` half: the same identity at `-ι`, so `z` and `w` swap and `Ψ` becomes
`r + ι • star s`. -/
theorem psi_mul_coord_sixteen (ι : R) (hι : ι * ι = -1) {p q : Tower R 4}
    (hp : (basis R 4).repr p 0#4 = 0) (hq : (basis R 4).repr q 0#4 = 0) (r s : Tower R 4)
    (m : Fin 16) :
    (basis R 4).repr (phi (-ι) (mk p q * mk r s)) (BitVec.ofNat 4 m.val) =
      ∑ e : Fin 16, PfaffianSixteen.borderedA
        (fun n => (basis R 4).repr p (BitVec.ofNat 4 n) - ι * (basis R 4).repr q (BitVec.ofNat 4 n))
        (fun n => (basis R 4).repr p (BitVec.ofNat 4 n) + ι * (basis R 4).repr q (BitVec.ofNat 4 n))
        m e * (basis R 4).repr (r + ι • star s) (BitVec.ofNat 4 e.val) := by
  have h := phi_mul_coord_sixteen (-ι) (by rw [neg_mul_neg]; exact hι) hp hq r s m
  simpa only [neg_mul, sub_neg_eq_add, neg_smul, ← sub_eq_add_neg] using h

end Tower

end CayleyDickson
