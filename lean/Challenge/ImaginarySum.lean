/- SPDX-License-Identifier: Apache-2.0 -/
module

public import GororobaMath.CayleyDickson.TraceForm

/-!
# Challenge: the sum of the imaginary basis elements

This file restates, with `sorry` as each proof, the headline theorems that the solution
module proves and that the "Lean library" table of `README.md` names, with the
definitions those statements use. It imports the library modules that the solution
module imports. `lake comparator --config` with the JSON file beside this one checks
that each named theorem of the solution module has the statement written here and
depends only on `propext`, `Classical.choice` and `Quot.sound`. No library module
imports this file, and the admission gate does not build it.
-/

@[expose] public section

namespace CayleyDickson

namespace Tower

universe u

variable {R : Type u} [CommRing R] [StarRing R]

variable (R) in
/-- The imaginary sum, the sum of the basis units other than `1`. -/
def isum (k : ℕ) : Tower R k := ∑ p ∈ Finset.univ.erase (0#k), e R k p

section Trivial

variable [TrivialStar R]

/-- For the imaginary sum `s`, `s (s x) = (x s) s = -(2 ^ k - 1) x` and `s (x s) = (s x) s` at
every level. The Rocq original is `isum_laws` of `rocq/quantum/CdImaginarySumConference.v`. -/
theorem isum_laws (k : ℕ) (x : Tower R k) :
    isum R k * (isum R k * x) = (-(2 ^ k - 1 : R)) • x ∧
      x * isum R k * isum R k = (-(2 ^ k - 1 : R)) • x ∧
      isum R k * (x * isum R k) = isum R k * x * isum R k := by
  sorry

/-- Left and right multiplication by the imaginary sum are skew for the trace form at every
level. The Rocq original is `isum_skew` of `rocq/quantum/CdImaginarySumConference.v`. -/
theorem dot_isum_mul (k : ℕ) (x y : Tower R k) :
    dot k (isum R k * x) y = -dot k x (isum R k * y) ∧
      dot k (x * isum R k) y = -dot k x (y * isum R k) := by
  sorry

/-- Right multiplication by the imaginary sum scales the trace form by `2 ^ k - 1`, a skew
conference matrix. The Rocq original is `isum_conference` of
`rocq/quantum/CdImaginarySumConference.v`. -/
theorem dot_mul_isum_mul_isum (k : ℕ) (x y : Tower R k) :
    dot k (x * isum R k) (y * isum R k) = (2 ^ k - 1 : R) * dot k x y := by
  sorry

/-- `I + R_s` is a skew Hadamard matrix at every level. The Rocq original is
`isum_skew_hadamard` of `rocq/quantum/CdImaginarySumConference.v`. -/
theorem dot_add_mul_isum (k : ℕ) (x y : Tower R k) :
    dot k (x + x * isum R k) (y + y * isum R k) = (2 ^ k : R) * dot k x y := by
  sorry

/-- The map `α I + β R_s` scales the trace form by `α ^ 2 + (2 ^ k - 1) β ^ 2`. The Rocq original
is `isum_scaled_isometry` of `rocq/quantum/CdTowerBasisSign.v`. -/
theorem dot_smul_add_smul_mul_isum (k : ℕ) (α β : R) (x y : Tower R k) :
    dot k (α • x + β • (x * isum R k)) (α • y + β • (y * isum R k)) =
      (α * α + (2 ^ k - 1) * (β * β)) * dot k x y := by
  sorry

omit [TrivialStar R] in
/-- The arc matrix of right multiplication by the imaginary sum: the coordinate of `e a * s` at
index `a ^^^ b` is `sign k a b` for `b ≠ 0`. The Rocq original is `arc_entry` of
`rocq/quantum/CdTowerBasisSign.v`, whose index `a < 2 ^ k` is `a.toNat` here. -/
theorem repr_e_mul_isum {k : ℕ} (a b : BitVec k) (hb : b ≠ 0#k) :
    (basis R k).repr (e R k a * isum R k) (a ^^^ b) = (Tower.sign k a b : R) := by
  sorry

end Trivial

end Tower

end CayleyDickson
