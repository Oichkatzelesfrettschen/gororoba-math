/- SPDX-License-Identifier: Apache-2.0 -/
module

public import GororobaMath.CayleyDickson.TraceForm
public import Mathlib.LinearAlgebra.Matrix.ToLin

/-!
# The matrix of left multiplication by the conjugate is the transpose

Convention: the product of `Tower R k` is the Cayley-Dickson product of
`GororobaMath.CayleyDickson.Tower` over a commutative ring with the identity as star, and
`Tower.basis R k` is the basis of `GororobaMath.CayleyDickson.TowerModule`, indexed by `BitVec k`.
The matrix of a linear map `f` has entry `(i, j)` equal to the coordinate at `i` of `f (e j)`
(`LinearMap.toMatrix_apply`).

The standard basis is orthonormal for the trace form `Tower.dot` (`Tower.dot_e_e`), so the
coordinate of `y` at `i` is `dot y (e i)`; the adjoint identity `Tower.dot_mul_adjoint` then moves
`a` across `dot` as `star a`.

## Main results

* `Tower.dot_e_right`: `dot x (e i) = (basis).repr x i`.
* `Tower.toMatrix_mulLeft_star`: `L_(star a) = (L_a)ᵀ` in the basis, the matrix form of the
  adjoint identity `L_a^T = L_conj(a)`.
-/

@[expose] public section

namespace CayleyDickson

namespace Tower

universe u

variable {R : Type u} [CommRing R] [StarRing R] [TrivialStar R] {k : ℕ}

omit [TrivialStar R] in
/-- The coordinate of `x` at `i` is its trace form with the basis unit `e i`. -/
theorem dot_e_right (x : Tower R k) (i : BitVec k) : dot k x (e R k i) = (basis R k).repr x i := by
  rw [dot_eq_sum_repr, ← basis_apply, Module.Basis.repr_self]
  simp [Finsupp.single_apply]

/-- The matrix of left multiplication by `star a` in the basis of `Tower.basis` is the transpose
of the matrix of left multiplication by `a`, at every level over every commutative ring with the
identity as star. -/
theorem toMatrix_mulLeft_star (a : Tower R k) :
    LinearMap.toMatrix (basis R k) (basis R k) (mulLeft R k (star a)) =
      (LinearMap.toMatrix (basis R k) (basis R k) (mulLeft R k a)).transpose := by
  ext i j
  simp only [LinearMap.toMatrix_apply, Matrix.transpose_apply, mulLeft_apply, basis_apply]
  rw [← dot_e_right, ← dot_e_right, (dot_mul_adjoint k a (e R k i) (e R k j)).1]
  exact dot_comm k _ _

end Tower

end CayleyDickson
