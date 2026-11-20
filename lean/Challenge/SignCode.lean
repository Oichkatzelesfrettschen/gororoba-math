/- SPDX-License-Identifier: Apache-2.0 -/
module

public import GororobaMath.CayleyDickson.Tower
public import GororobaMath.CayleyDickson.AssociatorPhase

/-!
# Challenge: the code spanned by the Schreier sign cocycles

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

/-- The Schreier exponent of the triple `(l, r, x)`. -/
def schreier {k : ℕ} (l r x : BitVec k) : Bool :=
  negSign k r x ^^ negSign k l (r ^^^ x) ^^ negSign k (l ^^^ r) x

/-- The Schreier exponent normalized at `x = 0` is the coboundary of the sign cochain. The Rocq
original is `normalized_schreier_is_coboundary` of
`rocq/open/theories/BooleanCochainFiltration.v`. -/
theorem schreier_xor_schreier_zero {k : ℕ} (l r x : BitVec k) :
    (schreier l r x ^^ schreier l r 0#k) =
      (negSign k r x ^^ negSign k l (r ^^^ x) ^^ negSign k (l ^^^ r) x ^^ negSign k l r) := by
  sorry

/-- The Schreier sign span of order `k`: the `ZMod 2`-span of the functions `x ↦ schreier l r x`.
The Rocq original is `sign_span` of `rocq/open/theories/SchreierSignCode.v`, an inductive
predicate on Boolean functions closed under pointwise xor. -/
def signSpan (k : ℕ) : Submodule (ZMod 2) (BitVec k → ZMod 2) :=
  Submodule.span (ZMod 2) (Set.range fun lr : BitVec k × BitVec k =>
    fun x => if schreier lr.1 lr.2 x then (1 : ZMod 2) else 0)

/-- At order `k + 3` the Schreier sign span is the set of even-weight functions of the lower
bits plus a multiple of the top bit. The Rocq original is `schreier_span_characterization` of
`rocq/open/theories/SchreierSignCode.v`, whose `sign_span` is the same span as an inductive
predicate on Boolean functions. -/
theorem mem_signSpan_iff {k : ℕ} (f : BitVec (k + 3) → ZMod 2) :
    f ∈ signSpan (k + 3) ↔ ∃ (g : BitVec (k + 2) → ZMod 2) (c : ZMod 2), ∑ y, g y = 0 ∧
      ∀ x, f x = g (x.setWidth (k + 2)) + c * (if x.msb then 1 else 0) := by
  sorry

section Cardinality

open Module

/-- The map `(g, c) ↦ (x ↦ g (x.setWidth (k + 2)) + c * [x.msb])` of the code parameters to the
functions of order `k + 3`. -/
def codeMap (k : ℕ) : ((BitVec (k + 2) → ZMod 2) × ZMod 2) →ₗ[ZMod 2] (BitVec (k + 3) → ZMod 2) :=
  (LinearMap.funLeft (ZMod 2) (ZMod 2) (fun x : BitVec (k + 3) => x.setWidth (k + 2))).comp
      (LinearMap.fst (ZMod 2) _ _) +
    (LinearMap.toSpanSingleton (ZMod 2) (BitVec (k + 3) → ZMod 2)
      (fun x => if x.msb then (1 : ZMod 2) else 0)).comp (LinearMap.snd (ZMod 2) _ _)

/-- The values of a function of the low bits at `0` and its sum. -/
def valueSum (k : ℕ) : (BitVec (k + 2) → ZMod 2) →ₗ[ZMod 2] ZMod 2 × ZMod 2 :=
  (LinearMap.proj (0#(k + 2))).prod (∑ y, LinearMap.proj y)

/-- The normalized Schreier span of order `k + 3` has `2 ^ (2 ^ (k + 2) - 1)` elements. The Rocq
original is `normalized_code_cardinality` of `rocq/open/theories/SignCodeCardinality.v`, which
counts a duplicate-free list of tables; Lean counts the elements of the submodule with
`Nat.card`. -/
theorem card_normalizedSignSpan (k : ℕ) :
    Nat.card (signSpan (k + 3) ⊓
      LinearMap.ker (LinearMap.proj (R := ZMod 2) (φ := fun _ : BitVec (k + 3) => ZMod 2)
        0#(k + 3)) : Submodule (ZMod 2) (BitVec (k + 3) → ZMod 2)) = 2 ^ (2 ^ (k + 2) - 1) := by
  sorry

end Cardinality

end Tower

end CayleyDickson
