/- SPDX-License-Identifier: Apache-2.0 -/
module

public import GororobaMath.LinearAlgebra.PfaffianCross
public import GororobaMath.LinearAlgebra.PfaffianSixteen

/-!
# The Pfaffian adjugate of the Schur block of the bordered sixteen-by-sixteen matrix

Convention: `z : ℕ → R` is read at `1, ..., 15` as in `GororobaMath.LinearAlgebra.PfaffianSixteen`:
`u = (z_1, ..., z_7)` is `z` itself read at `1, ..., 7`, `μ = z_8`, and `v = vV z` is
`(z_9, ..., z_15)` read at `1, ..., 7`. `U = uv z`, `V = vv z`, `W = wv z`, `Q = qv z` and
`G = gv z` are the sums of `PfaffianSixteen`, `m = mV z = u × v` is the cross product of
`GororobaMath.LinearAlgebra.PfaffianCross`, and `comb α β γ z = α u + β v + γ m`. The Schur block
of the bordered matrix on the indices `1, ..., 7` is `crossMat a + wedge x v` with
`a = aV z = (U - V + μ²) u + 2 W v - 2 μ m` and `x = xV z = 2 m - 2 μ u` (computed exactly; the
identification with `borderedA` is not stated here).

## Main results

* `PfaffianSchur.dot_comb_comb`, `PfaffianSchur.cross_comb_v`, `PfaffianSchur.cross_comb_comb`:
  the Gram values and cross products of `u`, `v` and `m`, from `⟨u, m⟩ = ⟨v, m⟩ = 0`,
  `⟨m, m⟩ = U V - W²`, `u × m = W u - U v` and `v × m = V u - W v`.
* `PfaffianSchur.adjRhs_aV_xV`: the right-hand side of `PfaffianCross.adjPf_crossMat_add_wedge` at
  `a`, `x`, `v` is `U Q G z_f`.
* `PfaffianSchur.adjPf_schur`: `(-1) ^ (f - 1)` times the six-index Pfaffian of
  `crossMat a + wedge x v` without `f` is `U Q G z_f` for `f = 1, ..., 7`.
-/

@[expose] public section

namespace PfaffianSchur

open PfaffianCross PfaffianSixteen

attribute [local simp]
  PfaffianCross.octSign_1_1 PfaffianCross.octSign_1_2 PfaffianCross.octSign_1_3
  PfaffianCross.octSign_1_4 PfaffianCross.octSign_1_5 PfaffianCross.octSign_1_6
  PfaffianCross.octSign_1_7 PfaffianCross.octSign_2_1 PfaffianCross.octSign_2_2
  PfaffianCross.octSign_2_3 PfaffianCross.octSign_2_4 PfaffianCross.octSign_2_5
  PfaffianCross.octSign_2_6 PfaffianCross.octSign_2_7 PfaffianCross.octSign_3_1
  PfaffianCross.octSign_3_2 PfaffianCross.octSign_3_3 PfaffianCross.octSign_3_4
  PfaffianCross.octSign_3_5 PfaffianCross.octSign_3_6 PfaffianCross.octSign_3_7
  PfaffianCross.octSign_4_1 PfaffianCross.octSign_4_2 PfaffianCross.octSign_4_3
  PfaffianCross.octSign_4_4 PfaffianCross.octSign_4_5 PfaffianCross.octSign_4_6
  PfaffianCross.octSign_4_7 PfaffianCross.octSign_5_1 PfaffianCross.octSign_5_2
  PfaffianCross.octSign_5_3 PfaffianCross.octSign_5_4 PfaffianCross.octSign_5_5
  PfaffianCross.octSign_5_6 PfaffianCross.octSign_5_7 PfaffianCross.octSign_6_1
  PfaffianCross.octSign_6_2 PfaffianCross.octSign_6_3 PfaffianCross.octSign_6_4
  PfaffianCross.octSign_6_5 PfaffianCross.octSign_6_6 PfaffianCross.octSign_6_7
  PfaffianCross.octSign_7_1 PfaffianCross.octSign_7_2 PfaffianCross.octSign_7_3
  PfaffianCross.octSign_7_4 PfaffianCross.octSign_7_5 PfaffianCross.octSign_7_6
  PfaffianCross.octSign_7_7

variable {R : Type*} [CommRing R]

/-- The second imaginary half `v = (z_9, ..., z_15)`, read at `1, ..., 7`. -/
def vV (z : ℕ → R) (i : ℕ) : R := z (i + 8)

/-- The cross product `m = u × v`. -/
def mV (z : ℕ → R) : ℕ → R := cross z (vV z)

/-- The combination `α u + β v + γ m`. -/
def comb (α β γ : R) (z : ℕ → R) (i : ℕ) : R := α * z i + β * vV z i + γ * mV z i

/-- The cross-product vector of the Schur block, `(U - V + μ²) u + 2 W v - 2 μ m`. -/
def aV (z : ℕ → R) (i : ℕ) : R :=
  (uv z - vv z + z 8 ^ 2) * z i + 2 * wv z * vV z i - 2 * z 8 * mV z i

/-- The rank-two vector of the Schur block, `2 m - 2 μ u`. -/
def xV (z : ℕ → R) (i : ℕ) : R := 2 * mV z i - 2 * z 8 * z i

/-- `Q = U + μ² + V`. -/
theorem qv_split (z : ℕ → R) : qv z = uv z + z 8 ^ 2 + vv z := by
  simp [qv, uv, vv, Finset.sum_range_succ]
  ring

/-- The bilinear sum of two combinations: `⟨u, m⟩ = ⟨v, m⟩ = 0` and `⟨m, m⟩ = U V - W²`. -/
theorem dot_comb_comb (z : ℕ → R) (α β γ α' β' γ' : R) :
    dot7 (comb α β γ z) (comb α' β' γ' z) =
      α * α' * uv z + (α * β' + β * α') * wv z + β * β' * vv z +
        γ * γ' * (uv z * vv z - wv z ^ 2) := by
  simp [dot7, comb, mV, vV, cross, crossMat, uv, vv, wv, Finset.sum_range_succ]
  ring

/-- The bilinear sum of a combination with `v`. -/
theorem dot_comb_v (z : ℕ → R) (α β γ : R) :
    dot7 (comb α β γ z) (vV z) = α * wv z + β * vv z := by
  simp [dot7, comb, mV, vV, cross, crossMat, vv, wv, Finset.sum_range_succ]
  ring

/-- The cross product of a combination with `v`: `u × v = m`, `v × v = 0` and
`m × v = W v - V u`. -/
theorem cross_comb_v (z : ℕ → R) (α β γ : R) {f : ℕ} (h1 : 1 ≤ f) (h7 : f ≤ 7) :
    cross (comb α β γ z) (vV z) f = α * mV z f + γ * (wv z * vV z f - vv z * z f) := by
  interval_cases f <;> simp [comb, mV, vV, cross, crossMat, vv, wv, Finset.sum_range_succ] <;> ring

/-- The cross product of a combination with `ε u + δ m`: `u × m = W u - U v`,
`v × m = V u - W v`, `v × u = -m`, `m × u = U v - W u` and `m × m = 0`. -/
theorem cross_comb_comb (z : ℕ → R) (α β γ ε δ : R) {f : ℕ} (h1 : 1 ≤ f) (h7 : f ≤ 7) :
    cross (comb α β γ z) (comb ε 0 δ z) f =
      (α * δ * wv z + β * δ * vv z - γ * ε * wv z) * z f +
        (γ * ε * uv z - α * δ * uv z - β * δ * wv z) * vV z f - β * ε * mV z f := by
  interval_cases f <;>
    simp [comb, mV, vV, cross, crossMat, uv, vv, wv, Finset.sum_range_succ] <;> ring

/-- `dot7` reads its second argument only at `1, ..., 7`. -/
theorem dot7_congr_right (y p q : ℕ → R) (h : ∀ i, 1 ≤ i → i ≤ 7 → p i = q i) :
    dot7 y p = dot7 y q := by
  unfold dot7
  refine Finset.sum_congr rfl fun k hk => ?_
  rw [Finset.mem_range] at hk
  rw [h (k + 1) (by omega) (by omega)]

/-- The pairing of a combination with `(ε u + δ m) × v`. -/
theorem dot_comb_cross (z : ℕ → R) (α β γ ε δ : R) :
    dot7 (comb α β γ z) (cross (comb ε 0 δ z) (vV z)) =
      dot7 (comb α β γ z) (comb (-(δ * vv z)) (δ * wv z) ε z) := by
  refine dot7_congr_right _ _ _ fun i h1 h7 => ?_
  rw [cross_comb_v z ε 0 δ h1 h7]
  unfold comb
  ring

/-- The right-hand side of the cross-matrix adjugate at `a`, `x` and `v` is `U Q G z_f`: every
pairing and cross product reduces to `u`, `v` and `m`, and the coefficients of `v` and `m`
cancel. -/
theorem adjRhs_aV_xV (z : ℕ → R) {f : ℕ} (h1 : 1 ≤ f) (h7 : f ≤ 7) :
    adjRhs (aV z) (xV z) (vV z) f = uv z * qv z * gv z * z f := by
  have ha : aV z = comb (uv z - vv z + z 8 ^ 2) (2 * wv z) (-2 * z 8) z := by
    funext i
    unfold aV comb
    ring
  have hx : xV z = comb (-2 * z 8) 0 2 z := by
    funext i
    unfold xV comb
    ring
  rw [ha, hx]
  unfold adjRhs
  rw [dot_comb_cross, dot_comb_comb, dot_comb_comb, dot_comb_comb, dot_comb_v,
    cross_comb_v z _ _ _ h1 h7, cross_comb_comb z _ _ _ _ _ h1 h7]
  unfold gv comb
  rw [qv_split]
  ring

/-- The Pfaffian adjugate of the Schur block in closed form: `(-1) ^ (f - 1)` times the
six-index Pfaffian of `crossMat a + wedge x v` without `f` is `U Q G z_f`. -/
theorem adjPf_schur (z : ℕ → R) {f : ℕ} (h1 : 1 ≤ f) (h7 : f ≤ 7) :
    (-1) ^ (f - 1) * Matrix.pfaffianAux (fun a b => crossMat (aV z) a b + wedge (xV z) (vV z) a b)
      ((List.range' 1 7).erase f) = uv z * qv z * gv z * z f := by
  rw [adjPf_crossMat_add_wedge _ _ _ h1 h7, adjRhs_aV_xV z h1 h7]

end PfaffianSchur
