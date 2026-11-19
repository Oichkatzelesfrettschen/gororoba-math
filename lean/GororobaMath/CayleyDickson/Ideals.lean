/- SPDX-License-Identifier: Apache-2.0 -/
module

public import Mathlib.RingTheory.Ideal.Operations

/-!
# Ideals and a square root of minus one

Convention: `S` is a commutative ring and `i : S` satisfies `i * i = -1`. An ideal `I` of `S`
contains `re + i * im` and `re - i * im` exactly when it contains `re` and `im`, provided `2` is a
unit of `S`: the sum is `2 * re`, and `i` times the difference is `-2 * im`.

## Main results

* `Ideal.add_mul_mem_and_sub_mul_mem_iff`: the Rocq original is `ideal_exchange` of the module
  `Twisted` in `rocq/quantum/CdTwistedProduct.v`, there a polynomial identity over the integers
  adjoined with `i`.
-/

@[expose] public section

namespace Ideal

variable {S : Type*} [CommRing S]

/-- With `i * i = -1` and `2` a unit, an ideal holds `re + i * im` and `re - i * im` exactly when
it holds `re` and `im`. The Rocq original is `ideal_exchange` of the module `Twisted` in
`rocq/quantum/CdTwistedProduct.v`. -/
theorem add_mul_mem_and_sub_mul_mem_iff (I : Ideal S) (i : S) (hi : i * i = -1)
    (h2 : IsUnit (2 : S)) (re im : S) :
    (re + i * im ∈ I ∧ re - i * im ∈ I) ↔ (re ∈ I ∧ im ∈ I) := by
  constructor
  · rintro ⟨h1, h3⟩
    obtain ⟨u, hu⟩ := h2
    have hsum : (2 : S) * re ∈ I := by
      have := I.add_mem h1 h3
      rwa [show re + i * im + (re - i * im) = 2 * re by ring] at this
    have hdiff : (2 : S) * im ∈ I := by
      have := I.mul_mem_left (-i) (I.sub_mem h1 h3)
      rwa [show -i * (re + i * im - (re - i * im)) = 2 * (i * i * -im) + 0 * re by ring, hi,
        show (2 : S) * (-1 * -im) + 0 * re = 2 * im by ring] at this
    have key : ∀ t : S, (2 : S) * t ∈ I → t ∈ I := fun t ht => by
      have := I.mul_mem_left (↑u⁻¹ : S) ht
      rwa [← mul_assoc, ← hu, Units.inv_mul, one_mul] at this
    exact ⟨key _ hsum, key _ hdiff⟩
  · rintro ⟨h1, h3⟩
    exact ⟨I.add_mem h1 (I.mul_mem_left i h3), I.sub_mem h1 (I.mul_mem_left i h3)⟩

end Ideal
