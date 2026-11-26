/- SPDX-License-Identifier: Apache-2.0 -/
module

public import GororobaMath.LinearAlgebra.SparsePoly
public import GororobaMath.LinearAlgebra.Pfaffian

/-!
# Memoized Pfaffians over sparse polynomials, checked in the kernel

Convention: a matrix of polynomials is a function `A : ℕ → ℕ → Poly` (see `SparsePoly`), and an
index list `l : List ℕ` is read as in `Matrix.pfaffianAux`: `pfaffianAux B (x :: r)` is the sum
over the positions `k` of `r` of `(-1) ^ k * B x r[k] * pfaffianAux B (r.eraseIdx k)`. A table
`tbl : Tr (List ℕ × Poly)` is a binary trie keyed by `mask l`, the sum of `2 ^ i` over the
indices of `l`, and stores each list beside its polynomial; `lookupP` returns the polynomial
only for the stored list itself, so a key collision never yields a wrong entry.

`expand tbl l` computes the Pfaffian polynomial of `l` from the entries of the lists one index
shorter than the tail of `l`. `checkTbl tbl` requires every stored entry to equal its own
expansion over stored entries, a traversal of the trie. `build N` fills the table
for the even-size subsets of the indices `1, ..., N` in increasing key order, so each entry
finds its children already stored.

## Main results

* `PfaffianTable.snd_of_check`: if `checkTbl tbl` holds, every entry of `tbl` evaluates, at every
  `env` in every commutative ring, to `pfaffianAux` of the evaluated matrix on its list.
* `PfaffianTable.ev_expand`: the same for the expansion of a list whose children are stored.
-/

@[expose] public section

namespace PfaffianTable

open SparsePoly

/-- A binary trie of optional values: the key's bits, low first, pick the branch. -/
inductive Tr (α : Type) where
  | nil : Tr α
  | node : Tr α → Option α → Tr α → Tr α

/-- The value stored at `k`, reading at most `n` bits. -/
def Tr.find {α : Type} : ℕ → Tr α → ℕ → Option α
  | _, .nil, _ => none
  | 0, .node _ v _, _ => v
  | n + 1, .node l v r, k =>
      if k = 0 then v else if k % 2 = 0 then Tr.find n l (k / 2) else Tr.find n r (k / 2)

/-- Store `a` at `k`, reading at most `n` bits. -/
def Tr.ins {α : Type} : ℕ → ℕ → α → Tr α → Tr α
  | 0, _, a, .nil => .node .nil (some a) .nil
  | 0, _, a, .node l _ r => .node l (some a) r
  | n + 1, k, a, t =>
      let l := match t with | .nil => Tr.nil | .node l _ _ => l
      let v := match t with | .nil => none | .node _ v _ => v
      let r := match t with | .nil => Tr.nil | .node _ _ r => r
      if k = 0 then .node l (some a) r
      else if k % 2 = 0 then .node (Tr.ins n (k / 2) a l) v r
      else .node l v (Tr.ins n (k / 2) a r)

/-- Whether `f` holds on every stored value. -/
def Tr.all {α : Type} (f : α → Bool) : Tr α → Bool
  | .nil => true
  | .node l v r => (match v with | none => true | some a => f a) && Tr.all f l && Tr.all f r

/-- A value found in a trie satisfies every predicate that holds on the whole trie. -/
theorem Tr.find_all {α : Type} (f : α → Bool) : ∀ (n : ℕ) (t : Tr α) (k : ℕ) (a : α),
    t.find n k = some a → t.all f = true → f a = true := by
  intro n
  induction n with
  | zero =>
    intro t k a h hall
    cases t with
    | nil => simp [Tr.find] at h
    | node l v r =>
      simp only [Tr.find] at h
      subst h
      simp only [Tr.all, Bool.and_eq_true] at hall
      simpa using hall.1.1
  | succ n ih =>
    intro t k a h hall
    cases t with
    | nil => simp [Tr.find] at h
    | node l v r =>
      simp only [Tr.all, Bool.and_eq_true] at hall
      obtain ⟨⟨hv, hl⟩, hr⟩ := hall
      simp only [Tr.find] at h
      split_ifs at h with h1 h2
      · subst h
        simpa using hv
      · exact ih l _ a h hl
      · exact ih r _ a h hr

/-- The key bound of a table. -/
def keyBound : ℕ := 2 ^ 16

/-- The key of an index list: the sum of `2 ^ i`. -/
def mask (l : List ℕ) : ℕ := (l.map fun i => 2 ^ i).sum

/-- The polynomial stored for the list `l` itself. -/
def lookupP (tbl : Tr (List ℕ × Poly)) (l : List ℕ) : Option Poly :=
  if mask l < keyBound then
    match tbl.find 17 (mask l) with
    | some (l', p) => if l = l' then some p else none
    | none => none
  else none

/-- The sign `(-1) ^ k` as an integer. -/
def sgnZ (k : ℕ) : ℤ := if k % 2 = 0 then 1 else -1

/-- The scalar multiple of a polynomial. -/
def pscale (s : ℤ) (p : Poly) : Poly := p.map fun t => (t.1, s * t.2)

section Expansion

variable (A : ℕ → ℕ → Poly) (tbl : Tr (List ℕ × Poly))

/-- The first `n` terms of the expansion along `x` over the tail `r`. -/
def children (x : ℕ) (r : List ℕ) : ℕ → Option Poly
  | 0 => some []
  | k + 1 =>
      match children x r k, lookupP tbl (r.eraseIdx k) with
      | some acc, some q => some (padd acc (pmul (pscale (sgnZ k) (A x (r.getD k 0))) q))
      | _, _ => none

/-- The Pfaffian polynomial of a list from the stored entries of its children. -/
def expand : List ℕ → Option Poly
  | [] => some [(0, 1)]
  | x :: r => children A tbl x r r.length

/-- Every stored entry equals its own expansion. -/
def checkTbl : Bool :=
  tbl.all fun e => decide (expand A tbl e.1 = some e.2)

end Expansion

/-- The indices among `1, ..., N` whose bit is set in `m`. -/
def bitsOf (N m : ℕ) : List ℕ := (List.range' 1 N).filter fun i => m.testBit i

/-- A key that stores an even-size subset of `1, ..., N`. -/
def validMask (N m : ℕ) : Bool := !m.testBit 0 && (bitsOf N m).length % 2 == 0

/-- The table of all even-size subsets of `1, ..., N`, in increasing key order. -/
def build (A : ℕ → ℕ → Poly) (N : ℕ) : Tr (List ℕ × Poly) :=
  (List.range (2 ^ (N + 1))).foldl (fun tbl m =>
    if validMask N m then
      let l := bitsOf N m
      tbl.ins 17 (mask l) (l, (expand A tbl l).getD [])
    else tbl) .nil

section Soundness

variable {R : Type*} [CommRing R] (env : ℕ → R) (A : ℕ → ℕ → Poly)

/-- The evaluated matrix. -/
def AR (a b : ℕ) : R := evP env (A a b)

theorem evP_pscale (s : ℤ) (p : Poly) : evP env (pscale s p) = (s : R) * evP env p := by
  induction p with
  | nil => simp [pscale]
  | cons t p ih =>
    simp only [pscale, List.map_cons, evP_cons] at ih ⊢
    rw [ih]; push_cast; ring

theorem sgnZ_cast (n : ℕ) : ((sgnZ n : ℤ) : R) = (-1) ^ n := by
  unfold sgnZ
  rcases Nat.even_or_odd n with he | ho
  · have h0 : n % 2 = 0 := Nat.even_iff.mp he
    simp [h0, he.neg_one_pow]
  · have h0 : n % 2 ≠ 0 := by have := Nat.odd_iff.mp ho; omega
    simp [h0, ho.neg_one_pow]

/-- The entries of `tbl` on lists shorter than `n` evaluate to the Pfaffian of the evaluated
matrix. -/
def Snd (tbl : Tr (List ℕ × Poly)) (n : ℕ) : Prop :=
  ∀ l p, l.length < n → lookupP tbl l = some p → evP env p = Matrix.pfaffianAux (AR env A) l

theorem ev_children (tbl : Tr (List ℕ × Poly)) (x : ℕ) (r : List ℕ) (h : Snd env A tbl r.length) :
    ∀ n, n ≤ r.length → ∀ P, children A tbl x r n = some P →
      evP env P = ∑ k ∈ Finset.range n,
        (-1) ^ k * AR env A x (r.getD k 0) * Matrix.pfaffianAux (AR env A) (r.eraseIdx k) := by
  intro n
  induction n with
  | zero =>
    intro _ P hP
    simp only [children, Option.some.injEq] at hP
    subst hP; simp
  | succ n ih =>
    intro hn P hP
    simp only [children] at hP
    rcases hc : children A tbl x r n with _ | acc <;>
      rcases hq : lookupP tbl (r.eraseIdx n) with _ | q <;> simp only [hc, hq] at hP
    · cases hP
    · cases hP
    · cases hP
    · cases hP
      have hlen : (r.eraseIdx n).length < r.length := by
        have := List.length_eraseIdx_of_lt (show n < r.length by omega)
        omega
      rw [Finset.sum_range_succ, evP_padd, evP_pmul, evP_pscale, ih (by omega) acc hc,
        h _ q hlen hq, sgnZ_cast]
      rfl

theorem ev_expand (tbl : Tr (List ℕ × Poly)) (x : ℕ) (r : List ℕ) (h : Snd env A tbl r.length)
    (P : Poly) (hP : expand A tbl (x :: r) = some P) :
    evP env P = Matrix.pfaffianAux (AR env A) (x :: r) := by
  have h1 := ev_children env A tbl x r h r.length le_rfl P hP
  rw [h1, Matrix.pfaffianAux_cons,
    ← Fin.sum_univ_eq_sum_range (fun k => (-1) ^ k * AR env A x (r.getD k 0) *
      Matrix.pfaffianAux (AR env A) (r.eraseIdx k)) r.length]
  refine Finset.sum_congr rfl fun k _ => ?_
  simp [List.getD_eq_getElem?_getD]

theorem lookupP_spec {tbl : Tr (List ℕ × Poly)} {l : List ℕ} {p : Poly}
    (h : lookupP tbl l = some p) : mask l < keyBound ∧ tbl.find 17 (mask l) = some (l, p) := by
  unfold lookupP at h
  split_ifs at h with h1
  · rcases hf : tbl.find 17 (mask l) with _ | ⟨l', q⟩
    · simp [hf] at h
    · rw [hf] at h
      simp only at h
      split_ifs at h with h2
      · cases h
        subst h2
        exact ⟨h1, rfl⟩

theorem expand_of_check {tbl : Tr (List ℕ × Poly)} (hc : checkTbl A tbl = true) {l : List ℕ}
    {p : Poly} (hl : lookupP tbl l = some p) : expand A tbl l = some p := by
  obtain ⟨hm, hf⟩ := lookupP_spec hl
  unfold checkTbl at hc
  have := Tr.find_all _ 17 tbl (mask l) (l, p) hf hc
  simpa using this

/-- A table that passes `checkTbl` is sound at every list length. -/
theorem snd_of_check {tbl : Tr (List ℕ × Poly)} (hc : checkTbl A tbl = true) :
    ∀ n, Snd env A tbl n := by
  intro n
  induction n with
  | zero => intro l p hl; omega
  | succ n ih =>
    intro l p hl hlk
    rcases Nat.lt_succ_iff_lt_or_eq.mp hl with h | h
    · exact ih l p h hlk
    · have hex := expand_of_check A hc hlk
      cases l with
      | nil =>
        simp only [expand, Option.some.injEq] at hex
        subst hex
        simp [evP, monEv, Matrix.pfaffianAux_nil]
      | cons x r =>
        refine ev_expand env A tbl x r (fun l' p' hl' hlk' => ih l' p' ?_ hlk') p hex
        simp only [List.length_cons] at h
        omega

end Soundness

end PfaffianTable
