/- SPDX-License-Identifier: Apache-2.0 -/
module

public import GororobaMath.CayleyDickson.TowerModule

/-!
# Challenge: sparse support and the sector decomposition of the kernel

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

variable {R : Type u} [CommRing R] [StarRing R] [TrivialStar R]

/-- Operands supported on XOR cosets `s ^^^ G` and `t ^^^ G` of a subgroup `G` have a product
supported on `s ^^^ t ^^^ G`. The Rocq original is `sparse_support_transport` of
`rocq/open/theories/CDSparseBlockTransport.v`. -/
theorem repr_mul_ne_zero_mem {k : ℕ} {G : Set (BitVec k)} (hG0 : 0#k ∈ G)
    (hG : ∀ a ∈ G, ∀ b ∈ G, a ^^^ b ∈ G) {y v : Tower R k} {s t : BitVec k}
    (hy : ∀ p, (basis R k).repr y p ≠ 0 → s ^^^ p ∈ G)
    (hv : ∀ p, (basis R k).repr v p ≠ 0 → t ^^^ p ∈ G) (p : BitVec k)
    (hp : (basis R k).repr (y * v) p ≠ 0) : s ^^^ t ^^^ p ∈ G := by
  sorry

open scoped Classical in
/-- The part of `v` supported on the coset `c ^^^ G`. -/
noncomputable def sectorProj {k : ℕ} (G : Set (BitVec k)) (c : BitVec k) (v : Tower R k) :
    Tower R k :=
  ∑ p ∈ Finset.univ.filter fun p => c ^^^ p ∈ G, (basis R k).repr v p • e R k p

/-- For an operand supported on one coset, a vector is annihilated exactly when each of its
sector projections is. The Rocq originals are `sparse_kernel_decomposition` of
`rocq/open/theories/CDSparseBlockTransport.v` (row 98) and the kernel form of
`sparse_field_rank_decomposition` of `rocq/open/theories/CDSparseMatrixTransport.v` (row 99,
the matrix-shape restatement, which has no separate Lean declaration). -/
theorem mul_eq_zero_iff_forall_sector {k : ℕ} {G : Set (BitVec k)} (hG0 : 0#k ∈ G)
    (hG : ∀ a ∈ G, ∀ b ∈ G, a ^^^ b ∈ G) {y : Tower R k} {s : BitVec k}
    (hy : ∀ p, (basis R k).repr y p ≠ 0 → s ^^^ p ∈ G) (v : Tower R k) :
    y * v = 0 ↔ ∀ c, y * sectorProj G c v = 0 := by
  sorry

end Tower

end CayleyDickson
