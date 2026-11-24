/- SPDX-License-Identifier: Apache-2.0 -/
module

public import Mathlib.RingTheory.Ideal.Operations

/-!
# A separating element forces an ideal between two ideals to equal the lower one

Convention: `K`, `L`, `A` and `R` are ideals of a commutative ring `S`, with `K ≤ L ≤ R`. The
ideal `A` is the annihilator-like ideal of the quotient `R / K`: the elements of `A` carry `R`
into `K`, and an element outside `A` is a nonzerodivisor on `R / K` (the torsion-free
condition). The rank-one condition is stated elementwise: every `r ∈ R` is dependent on one fixed
element `y ∈ R` with a coefficient `a ∉ A` on `r`, that is `a r - b y ∈ K`. The element `y`
separates `L` when `c y ∈ L` forces `c ∈ A`.

The proof uses no domain, no module structure and no polynomial ring, and `L ≤ rad K` enters
only through `L ≤ R` (with `R = rad K` in the application).

## Main results

* `FiberCone.le_of_separating`: under the hypotheses above, `L ≤ K`.
* `FiberCone.eq_of_separating`: with `K ≤ L`, `L = K`.
-/

@[expose] public section

namespace FiberCone

variable {S : Type*} [CommRing S]

/-- An element `l` of `L` is dependent on `y`: `a l - b y` lies in `K ≤ L`, so `b y` lies in
`L`, `b` lies in `A`, `b y` lies in `K`, hence `a l` lies in `K` and `l` does. -/
theorem le_of_separating (K L A R : Ideal S) (y : S) (hKL : K ≤ L) (hLR : L ≤ R)
    (hAR : ∀ c ∈ A, ∀ r ∈ R, c * r ∈ K)
    (htf : ∀ c, c ∉ A → ∀ r ∈ R, c * r ∈ K → r ∈ K)
    (hy : y ∈ R) (hdep : ∀ r ∈ R, ∃ a b : S, a ∉ A ∧ a * r - b * y ∈ K)
    (hsep : ∀ c : S, c * y ∈ L → c ∈ A) : L ≤ K := by
  intro l hl
  obtain ⟨a, b, haA, hab⟩ := hdep l (hLR hl)
  have hbyL : b * y ∈ L := by
    have h1 : a * l - (a * l - b * y) ∈ L := L.sub_mem (L.mul_mem_left a hl) (hKL hab)
    simpa using h1
  have hbA : b ∈ A := hsep b hbyL
  have hbyK : b * y ∈ K := hAR b hbA y hy
  have halK : a * l ∈ K := by
    have h1 : a * l - b * y + b * y ∈ K := K.add_mem hab hbyK
    simpa using h1
  exact htf a haA l (hLR hl) halK

/-- With `K ≤ L`, the separating hypotheses give `L = K`. -/
theorem eq_of_separating (K L A R : Ideal S) (y : S) (hKL : K ≤ L) (hLR : L ≤ R)
    (hAR : ∀ c ∈ A, ∀ r ∈ R, c * r ∈ K)
    (htf : ∀ c, c ∉ A → ∀ r ∈ R, c * r ∈ K → r ∈ K)
    (hy : y ∈ R) (hdep : ∀ r ∈ R, ∃ a b : S, a ∉ A ∧ a * r - b * y ∈ K)
    (hsep : ∀ c : S, c * y ∈ L → c ∈ A) : L = K :=
  le_antisymm (le_of_separating K L A R y hKL hLR hAR htf hy hdep hsep) hKL

end FiberCone
