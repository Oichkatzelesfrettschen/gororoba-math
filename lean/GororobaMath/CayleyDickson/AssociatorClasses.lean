/- SPDX-License-Identifier: Apache-2.0 -/
module

public import GororobaMath.CayleyDickson.AssociatorPhase

/-!
# The three associativity classes of a triad and the parity of their phases

Convention: `Tower.assocPhase p q x` is `true` when `(e p * e q) * e x` and `e p * (e q * e x)`
carry opposite signs, that is when the associator of the three basis elements is nonzero
(`GororobaMath.CayleyDickson.AssociatorPhase`, `Tower.e_mul_e_mul_e`); `Tower.commPhase a b` is
`true` when `e a` and `e b` anticommute. Indices are `BitVec k` with `^^^` the product of
basis labels up to sign.

Wilmot, "Structure of the Cayley-Dickson algebras" (arXiv 2505.11747v4), Theorem 2 (Table 1) and
Theorem 5, call a triad `b, c, d` of basis elements associative in Class 1, 2 or 3 when
`b d c = b (d c)`, `b c d = b (c d)` and `c b d = c (b d)` respectively. The dictionary is

* Class 1 fails exactly when `assocPhase b d c` holds (`Tower.class1`),
* Class 2 fails exactly when `assocPhase b c d` holds (`Tower.class2`),
* Class 3 fails exactly when `assocPhase c b d` holds (`Tower.class3`).

Theorem 5 reads: if a triad is not associative, either all three classes fail or exactly one
fails. Evaluation at levels 3, 4 and 5 over the triads `0 < b < c < d` shows, for triads with
`b ^^^ c ≠ d` (independent), only the patterns "all three fail" and "exactly one fails" (never
"none" and never "exactly two"), and for `b ^^^ c = d` (dependent) only "none fails"; the
parity of the three phases is therefore the invariant: odd on independent triads, even on dependent
ones, and it equals a sum of three commutation phases at every level.

## Main results

* `Tower.class_parity`: for all `b c d` the sum of the three class phases is
  `commPhase b c ^^ commPhase c d ^^ commPhase (b ^^^ d) c`, a four-sign cancellation of
  `Tower.assocPhase_eq`.
* `Tower.class_parity_of_independent`: for distinct nonzero `b, c, d` with `b ^^^ c ≠ d` the sum
  is `true`.
* `Tower.class_parity_of_dependent`: for `d = b ^^^ c` the sum is `false`.
* `Tower.nonassociative_classes`: Wilmot's Theorem 5 on an independent triad: no triad is
  associative in all three classes, and exactly two classes never fail.
* `Tower.card_triads_all_fail_four`, `Tower.card_triads_exactly_one_fail_four`: the counts at
  level 4.
-/

@[expose] public section

namespace CayleyDickson

namespace Tower

/-- Class 1 of the triad `b, c, d` fails: `(e b * e d) * e c ≠ e b * (e d * e c)`. -/
def class1 {k : ℕ} (b c d : BitVec k) : Bool := assocPhase b d c

/-- Class 2 of the triad `b, c, d` fails: `(e b * e c) * e d ≠ e b * (e c * e d)`. -/
def class2 {k : ℕ} (b c d : BitVec k) : Bool := assocPhase b c d

/-- Class 3 of the triad `b, c, d` fails: `(e c * e b) * e d ≠ e c * (e b * e d)`. -/
def class3 {k : ℕ} (b c d : BitVec k) : Bool := assocPhase c b d

/-- The parity of the three class phases is a sum of three commutation phases. -/
theorem class_parity {k : ℕ} (b c d : BitVec k) :
    (class1 b c d ^^ class2 b c d ^^ class3 b c d) =
      (commPhase b c ^^ commPhase c d ^^ commPhase (b ^^^ d) c) := by
  have h1 : c ^^^ b = b ^^^ c := BitVec.xor_comm _ _
  have h2 : d ^^^ c = c ^^^ d := BitVec.xor_comm _ _
  have h3 : b ^^^ d = d ^^^ b := BitVec.xor_comm _ _
  unfold class1 class2 class3 commPhase
  rw [assocPhase_eq, assocPhase_eq, assocPhase_eq]
  simp only [h1, h2]
  generalize negSign k b d = s1
  generalize negSign k (b ^^^ d) c = s2
  generalize negSign k d c = s3
  generalize negSign k b (c ^^^ d) = s4
  generalize negSign k b c = s5
  generalize negSign k (b ^^^ c) d = s6
  generalize negSign k c d = s7
  generalize negSign k c b = s8
  generalize negSign k c (b ^^^ d) = s9
  revert s1 s2 s3 s4 s5 s6 s7 s8 s9
  decide

end Tower

end CayleyDickson
