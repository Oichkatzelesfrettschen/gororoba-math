/- SPDX-License-Identifier: Apache-2.0 -/
module

public import GororobaMath.CayleyDickson.AssociatorPhase

/-!
# Census of the associator phases by algebraic degree

Convention: indices are `p q : BitVec k` as in `GororobaMath.CayleyDickson.AssociatorPhase`,
read as integers through `BitVec.toNat`; a pair `(p, q)` of the census satisfies
`0 < p.toNat < q.toNat`, an unordered pair of distinct nonzero indices listed once with the
smaller index first. `Tower.assocPhase p q` is the Boolean function `x ↦ assocPhase p q x` and
its degree is `Tower.anfDegree` of `GororobaMath.CayleyDickson.BooleanAnf`.

By `Tower.anfDegree_assocPhase` the degree of the pair is `max 1 (log2 q - 1)`, so the pairs
of degree `d ≥ 2` are exactly those whose larger index `q` has `log2 q = d + 1`. The number of
pairs `0 < p < q` with a fixed larger index `q` is `q - 1`, and the indices with
`log2 q = D` form the interval `[2^D, 2^(D+1))`, so the count of that class is a sum of
`q - 1` over an interval (`Tower.card_pairs_log2`).

## Main results

* `Tower.card_anfDegree_assocPhase_eq`: for `3 ≤ k` and `2 ≤ d ≤ k - 2` exactly
  `3 * 2^d * (2^(d+1) - 1)` pairs have degree `d`. The Rocq original is `census_degree` of
  `rocq/quantum/CdAssociatorCensus.v`.
* `Tower.card_anfDegree_assocPhase_eq_one`: for `3 ≤ k` exactly `21` pairs have degree `1`,
  the Rocq `census_degree_one`.
* `Tower.sum_card_anfDegree_assocPhase`: the counts over all degrees add up to
  `(2^k - 1) * (2^k - 2) / 2`, stated as twice the sum, the Rocq `census_total`.
* `Tower.card_assocPhase_true`: at order `k + 1` with `n = 2^(k + 1)`, twice the number of
  non-associating ordered basis triples is `(n - 2) (n - 4) (n + 6)`, the Rocq
  `associator_census_formula` of `rocq/open/theories/CDAssociatorCensus.v`.
-/

@[expose] public section

namespace CayleyDickson

namespace Tower

/-- A sum over `BitVec k` of a function of `toNat` is the sum over `range (2 ^ k)`. -/
theorem sum_bitVec_toNat {M : Type*} [AddCommMonoid M] (k : ℕ) (g : ℕ → M) :
    ∑ q : BitVec k, g q.toNat = ∑ i ∈ Finset.range (2 ^ k), g i := by
  rw [← Fin.sum_univ_eq_sum_range g (2 ^ k)]
  exact Fintype.sum_equiv BitVec.equivFin.toEquiv _ _ fun q => rfl

/-- The pairs `0 < p < b` with `p` below `2 ^ k` number `b - 1`. -/
theorem card_below {k b : ℕ} (hb : b ≤ 2 ^ k) :
    (Finset.univ.filter fun p : BitVec k => 0 < p.toNat ∧ p.toNat < b).card = b - 1 := by
  rw [Finset.card_filter, sum_bitVec_toNat k (fun i => if 0 < i ∧ i < b then 1 else 0),
    ← Finset.card_filter]
  have : (Finset.range (2 ^ k)).filter (fun i => 0 < i ∧ i < b) = Finset.Ioo 0 b := by
    ext i
    simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Ioo]
    omega
  rw [this, Nat.card_Ioo]
  omega

/-- The census pairs whose larger index satisfies `P` number the sum of `q - 1` over the
indices `q < 2 ^ k` with `P q`. -/
theorem card_pairs (k : ℕ) (P : ℕ → Prop) [DecidablePred P] :
    (Finset.univ.filter fun pq : BitVec k × BitVec k =>
        0 < pq.1.toNat ∧ pq.1.toNat < pq.2.toNat ∧ P pq.2.toNat).card =
      ∑ b ∈ Finset.range (2 ^ k), if P b then b - 1 else 0 := by
  rw [Finset.card_filter, Fintype.sum_prod_type_right]
  rw [← sum_bitVec_toNat k (fun b => if P b then b - 1 else 0)]
  refine Finset.sum_congr rfl fun q _ => ?_
  by_cases hP : P q.toNat
  · simp only [hP, ↓reduceIte]
    rw [← card_below (k := k) (le_of_lt q.isLt), Finset.card_filter]
    refine Finset.sum_congr rfl fun p _ => ?_
    simp
  · simp only [hP, ↓reduceIte]
    refine Finset.sum_eq_zero fun p _ => ?_
    simp

/-- Twice the sum of `b - 1` over `[a, 2a)` is `3 a (a - 1)`. -/
theorem sum_Ico_pred_mul_two {a : ℕ} (ha : 1 ≤ a) :
    2 * ∑ b ∈ Finset.Ico a (2 * a), (b - 1) = 3 * a * (a - 1) := by
  have e : 2 * a - a = a := by omega
  rw [Finset.sum_Ico_eq_sum_range, e]
  have h : ∀ t, a + t - 1 = (a - 1) + t := fun t => by omega
  simp only [h]
  rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_range, smul_eq_mul]
  have := Finset.sum_range_id_mul_two a
  rw [show 3 * a * (a - 1) = 3 * (a * (a - 1)) by ring]
  generalize a * (a - 1) = X at *
  generalize ∑ i ∈ Finset.range a, i = S at *
  omega

/-- Twice the sum of `b - 1` over `[0, N)` is `(N - 1) (N - 2)`. -/
theorem sum_range_pred_mul_two (N : ℕ) : 2 * ∑ b ∈ Finset.range N, (b - 1) = (N - 1) * (N - 2) := by
  cases N with
  | zero => simp
  | succ n =>
    rw [Finset.sum_range_succ']
    simp only [Nat.add_sub_cancel, Nat.zero_sub, add_zero]
    have := Finset.sum_range_id_mul_two n
    rw [mul_comm]
    rw [this]
    cases n <;> simp

/-- The pairs whose larger index has `Nat.log2 = D`, for `1 ≤ D < k`, number
`3 * 2^(D - 1) * (2^D - 1)`. -/
theorem card_pairs_log2 {k D : ℕ} (hD : 1 ≤ D) (hDk : D < k) :
    (Finset.univ.filter fun pq : BitVec k × BitVec k =>
        0 < pq.1.toNat ∧ pq.1.toNat < pq.2.toNat ∧ Nat.log2 pq.2.toNat = D).card =
      3 * 2 ^ (D - 1) * (2 ^ D - 1) := by
  rw [card_pairs k (fun b => Nat.log2 b = D), ← Finset.sum_filter]
  have hk2 : 2 ^ (D + 1) ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) (by omega)
  have hs : (Finset.range (2 ^ k)).filter (fun b => Nat.log2 b = D) =
      Finset.Ico (2 ^ D) (2 * 2 ^ D) := by
    ext b
    simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Ico]
    have hpow : 2 ^ (D + 1) = 2 * 2 ^ D := pow_succ' 2 D
    constructor
    · rintro ⟨hb, hl⟩
      have hb0 : b ≠ 0 := by
        rintro rfl
        simp at hl
        omega
      have := (Nat.log2_eq_iff hb0).1 hl
      omega
    · rintro ⟨h1, h2⟩
      have hpos : 0 < 2 ^ D := by positivity
      have hb0 : b ≠ 0 := by omega
      exact ⟨by omega, (Nat.log2_eq_iff hb0).2 ⟨h1, by omega⟩⟩
  rw [hs]
  have h := sum_Ico_pred_mul_two (a := 2 ^ D) Nat.one_le_two_pow
  obtain ⟨E, rfl⟩ : ∃ E, D = E + 1 := ⟨D - 1, by omega⟩
  rw [Nat.add_sub_cancel]
  rw [pow_succ] at h ⊢
  generalize 2 ^ E = t at *
  generalize ∑ b ∈ Finset.Ico (t * 2) (2 * (t * 2)), (b - 1) = S at *
  have h2 : 2 * S = 2 * (3 * t * (t * 2 - 1)) := by
    rw [h]
    ring
  exact Nat.eq_of_mul_eq_mul_left (by norm_num) h2

theorem anfDegree_assocPhase_of_lt {k : ℕ} (hk : 3 ≤ k) {p q : BitVec k} (hp : 0 < p.toNat)
    (hpq : p.toNat < q.toNat) :
    anfDegree (assocPhase p q) = max 1 (Nat.log2 q.toNat - 1) := by
  have hp0 : p ≠ 0#k := fun h => by simp [h] at hp
  have hq0 : q ≠ 0#k := fun h => by simp [h] at hpq
  have hne : p ≠ q := fun h => by simp [h] at hpq
  rw [anfDegree_assocPhase hk hp0 hq0 hne, max_eq_right hpq.le]

/-- For `3 ≤ k` and `2 ≤ d ≤ k - 2`, exactly `3 * 2^d * (2^(d+1) - 1)` pairs `0 < p < q < 2^k`
have associator-phase degree `d`. The Rocq original is `census_degree` of
`rocq/quantum/CdAssociatorCensus.v`: by `anfDegree_assocPhase` the degree is `d` exactly when
`log2 q = d + 1`, and `card_pairs_log2` counts those pairs. -/
theorem card_anfDegree_assocPhase_eq {k d : ℕ} (hk : 3 ≤ k) (hd : 2 ≤ d) (hdk : d + 2 ≤ k) :
    (Finset.univ.filter fun pq : BitVec k × BitVec k =>
        0 < pq.1.toNat ∧ pq.1.toNat < pq.2.toNat ∧
          anfDegree (assocPhase pq.1 pq.2) = d).card =
      3 * 2 ^ d * (2 ^ (d + 1) - 1) := by
  have h := card_pairs_log2 (k := k) (D := d + 1) (by omega) (by omega)
  rw [Nat.add_sub_cancel] at h
  rw [← h]
  congr 1
  refine Finset.filter_congr fun pq _ => ?_
  refine and_congr_right fun h1 => and_congr_right fun h2 => ?_
  rw [anfDegree_assocPhase_of_lt hk h1 h2]
  omega

/-- For `3 ≤ k` exactly `21` pairs `0 < p < q < 2^k` have associator-phase degree `1`. The Rocq
original is `census_degree_one` of `rocq/quantum/CdAssociatorCensus.v`: the degree is `1`
exactly when `q < 8`. -/
theorem card_anfDegree_assocPhase_eq_one {k : ℕ} (hk : 3 ≤ k) :
    (Finset.univ.filter fun pq : BitVec k × BitVec k =>
        0 < pq.1.toNat ∧ pq.1.toNat < pq.2.toNat ∧
          anfDegree (assocPhase pq.1 pq.2) = 1).card = 21 := by
  have h8 : 2 ^ 3 ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) hk
  have hc := card_pairs k (fun b => b < 8)
  have hs : (Finset.range (2 ^ k)).filter (fun b => b < 8) = Finset.range 8 := by
    ext b
    simp only [Finset.mem_filter, Finset.mem_range]
    omega
  rw [← Finset.sum_filter, hs] at hc
  have h21 : ∑ b ∈ Finset.range 8, (b - 1) = 21 := by decide
  rw [h21] at hc
  rw [← hc]
  congr 1
  refine Finset.filter_congr fun pq _ => ?_
  refine and_congr_right fun h1 => and_congr_right fun h2 => ?_
  rw [anfDegree_assocPhase_of_lt hk h1 h2]
  have hq0 : pq.2.toNat ≠ 0 := by omega
  have := Nat.log2_lt hq0 (k := 3)
  omega

/-- Twice the sum over all degrees of the number of pairs `0 < p < q < 2^k` of that degree is
`(2^k - 1) (2^k - 2)`, the number of ordered pairs of distinct nonzero indices. The Rocq original is
`census_total` of `rocq/quantum/CdAssociatorCensus.v`. -/
theorem sum_card_anfDegree_assocPhase {k : ℕ} (hk : 3 ≤ k) :
    2 * ∑ d ∈ Finset.range k,
      (Finset.univ.filter fun pq : BitVec k × BitVec k =>
        0 < pq.1.toNat ∧ pq.1.toNat < pq.2.toNat ∧
          anfDegree (assocPhase pq.1 pq.2) = d).card = (2 ^ k - 1) * (2 ^ k - 2) := by
  set s : Finset (BitVec k × BitVec k) :=
    Finset.univ.filter fun pq => 0 < pq.1.toNat ∧ pq.1.toNat < pq.2.toNat with hs
  have hfib := Finset.card_eq_sum_card_fiberwise (s := s) (t := Finset.range k)
    (f := fun pq : BitVec k × BitVec k => anfDegree (assocPhase pq.1 pq.2)) (by
      intro pq hpq
      simp only [hs, Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and] at hpq
      simp only [Finset.mem_coe, Finset.mem_range]
      rw [anfDegree_assocPhase_of_lt hk hpq.1 hpq.2]
      have hq0 : pq.2.toNat ≠ 0 := by omega
      have := (Nat.log2_lt hq0 (k := k)).2 pq.2.isLt
      omega)
  have hfil : ∀ d, (s.filter fun pq => anfDegree (assocPhase pq.1 pq.2) = d) =
      Finset.univ.filter fun pq : BitVec k × BitVec k =>
        0 < pq.1.toNat ∧ pq.1.toNat < pq.2.toNat ∧ anfDegree (assocPhase pq.1 pq.2) = d := by
    intro d
    simp only [hs, Finset.filter_filter, and_assoc]
  simp only [hfil] at hfib
  have htot : s.card = ∑ b ∈ Finset.range (2 ^ k), (b - 1) := by
    have := card_pairs k (fun _ => True)
    simpa [hs] using this
  rw [← hfib, htot]
  exact sum_range_pred_mul_two (2 ^ k)

section Triples

theorem commPhase_eq_false_iff {k : ℕ} (a b : BitVec k) :
    commPhase a b = false ↔ (a = 0#k ∨ b = 0#k ∨ a = b) := by
  rw [commPhase_eq, decide_eq_false_iff_not]
  tauto

/-- For `m ≠ 0` exactly the two completions `0` and `m` make a pair degenerate. -/
theorem sum_degenerate_right {k : ℕ} (m : BitVec k) :
    (∑ r : BitVec k, if (m = 0#k ∨ r = 0#k ∨ m = r) then 1 else 0) =
      if m = 0#k then 2 ^ k else 2 := by
  by_cases hm : m = 0#k
  · simp [hm, card_bitVec]
  · have hset : (Finset.univ.filter fun r : BitVec k => m = 0#k ∨ r = 0#k ∨ m = r) =
        {0#k, m} := by
      ext r
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert,
        Finset.mem_singleton, hm, false_or]
      rw [eq_comm (a := m)]
    rw [← Finset.card_filter, hset, Finset.card_pair (Ne.symm hm)]
    simp [hm]

theorem sum_degenerate_pairs (k : ℕ) :
    (∑ m : BitVec k, ∑ r : BitVec k, if (m = 0#k ∨ r = 0#k ∨ m = r) then 1 else 0) =
      3 * 2 ^ k - 2 := by
  simp only [sum_degenerate_right]
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ (0#k))]
  have h : ∑ m ∈ Finset.univ.erase (0#k), (if m = 0#k then 2 ^ k else 2) =
      ∑ m ∈ Finset.univ.erase (0#k), 2 :=
    Finset.sum_congr rfl fun m hm => by simp [Finset.ne_of_mem_erase hm]
  rw [h, Finset.sum_const, Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ,
    card_bitVec]
  have := Nat.one_le_two_pow (n := k)
  simp only [↓reduceIte, smul_eq_mul]
  omega

theorem sum_thin_ne_zero {k : ℕ} {l : BitVec k} (hl : l ≠ 0#k) :
    (∑ m : BitVec k, ∑ r : BitVec k,
      if ((m = 0#k ∨ r = 0#k ∨ m = r) ∧ (l = 0#k ∨ m = 0#k ∨ l = m) ∧
        (l = 0#k ∨ m ^^^ r = 0#k ∨ l = m ^^^ r)) then 1 else 0) = 4 := by
  rw [Finset.sum_eq_add (0#k) l (Ne.symm hl)]
  · have hset : ∀ P : BitVec k → Prop, ∀ [DecidablePred P], (∀ r, P r ↔ (r = 0#k ∨ r = l)) →
        (∑ r : BitVec k, if P r then 1 else 0) = 2 := by
      intro P _ hP
      have : (Finset.univ.filter P) = {0#k, l} := by
        ext r
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert,
          Finset.mem_singleton]
        exact hP r
      rw [← Finset.card_filter, this, Finset.card_pair (Ne.symm hl)]
    rw [hset, hset]
    · intro r
      simp only [hl, false_or, or_true, true_and]
      constructor
      · rintro ⟨h | h, _⟩
        · exact Or.inl h
        · exact Or.inr h.symm
      · rintro (h | h)
        · subst h
          exact ⟨Or.inl rfl, Or.inr (by simp)⟩
        · subst h
          exact ⟨Or.inr rfl, Or.inl (by simp)⟩
    · intro r
      simp only [BitVec.zero_xor, hl, true_or, or_true, true_and, false_or]
      exact or_congr Iff.rfl eq_comm
  · intro m _ hm
    refine Finset.sum_eq_zero fun r _ => ?_
    have h1 : ¬(l = 0#k ∨ m = 0#k ∨ l = m) := by
      rintro (h | h | h)
      · exact hl h
      · exact hm.1 h
      · exact hm.2 h.symm
    simp [h1]
  · intro h
    exact absurd (Finset.mem_univ _) h
  · intro h
    exact absurd (Finset.mem_univ _) h

/-- The number of triples `(l, m, r)` of `BitVec k` whose three pairs
`(m, r)`, `(l, m)`, `(l, m ^^^ r)` are all degenerate (a zero member or two equal members) is
`7 * 2^k - 6`. -/
theorem sum_thin (k : ℕ) :
    (∑ l : BitVec k, ∑ m : BitVec k, ∑ r : BitVec k,
      if (commPhase m r = false ∧ commPhase l m = false ∧ commPhase l (m ^^^ r) = false)
        then 1 else 0) = 7 * 2 ^ k - 6 := by
  simp only [commPhase_eq_false_iff]
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ (0#k))]
  have h0 : (∑ m : BitVec k, ∑ r : BitVec k,
      if ((m = 0#k ∨ r = 0#k ∨ m = r) ∧ (0#k = 0#k ∨ m = 0#k ∨ 0#k = m) ∧
        (0#k = 0#k ∨ m ^^^ r = 0#k ∨ 0#k = m ^^^ r)) then 1 else 0) = 3 * 2 ^ k - 2 := by
    rw [← sum_degenerate_pairs k]
    refine Finset.sum_congr rfl fun m _ => Finset.sum_congr rfl fun r _ => ?_
    simp
  have h1 : ∀ l ∈ Finset.univ.erase (0#k),
      (∑ m : BitVec k, ∑ r : BitVec k,
        if ((m = 0#k ∨ r = 0#k ∨ m = r) ∧ (l = 0#k ∨ m = 0#k ∨ l = m) ∧
          (l = 0#k ∨ m ^^^ r = 0#k ∨ l = m ^^^ r)) then 1 else 0) = 4 :=
    fun l hl => sum_thin_ne_zero (Finset.ne_of_mem_erase hl)
  rw [h0, Finset.sum_congr rfl h1, Finset.sum_const, Finset.card_erase_of_mem (Finset.mem_univ _),
    Finset.card_univ, card_bitVec, smul_eq_mul]
  have := Nat.one_le_two_pow (n := k)
  omega

/-- The sum over the eight choices of top bits of the Boolean phase at level `k + 1`: `0` when the
three constants vanish, and `4` otherwise, since a nonzero linear form in the top bits is
balanced. The constant `φ` is the phase of the low parts, which vanishes when `x2` does. -/
theorem sum_top_bits : ∀ φ x1 x2 x3 : Bool, (x2 = false → φ = false) →
    (∑ L : Bool, ∑ M : Bool, ∑ N : Bool,
      if (φ ^^ (L && x1) ^^ (M && (x2 ^^ x3)) ^^ (N && x2)) = true then 1 else 0) =
      if (x1 = false ∧ x2 = false ∧ x3 = false) then 0 else 4 := by
  intro φ x1 x2 x3 h
  simp only [Fintype.sum_bool]
  revert φ x1 x2 x3
  decide

theorem sum_top_bits_phase {k : ℕ} (l m r : BitVec k) :
    (∑ L : Bool, ∑ M : Bool, ∑ N : Bool,
      if assocPhase (BitVec.cons L l) (BitVec.cons M m) (BitVec.cons N r) then 1 else 0) =
      if (commPhase m r = false ∧ commPhase l m = false ∧ commPhase l (m ^^^ r) = false)
        then 0 else 4 := by
  simp only [assocPhase_cons, commPhase_xor_triple]
  rw [← commPhase_eq_cst m r, ← commPhase_eq_cst l m]
  refine sum_top_bits _ _ _ _ fun h => ?_
  exact assocPhase_eq_false_of_degenerate ((commPhase_eq_false_iff l m).1 h) r

/-- The number of triples of `BitVec k` with associator phase `true`, as a sum. -/
def phaseCount (k : ℕ) : ℕ :=
  ∑ l : BitVec k, ∑ m : BitVec k, ∑ r : BitVec k, if assocPhase l m r then 1 else 0

theorem phaseCount_succ (k : ℕ) :
    phaseCount (k + 1) = ∑ l : BitVec k, ∑ m : BitVec k, ∑ r : BitVec k,
      if (commPhase m r = false ∧ commPhase l m = false ∧ commPhase l (m ^^^ r) = false)
        then 0 else 4 := by
  unfold phaseCount
  simp only [sum_cons, ← sum_top_bits_phase, Fintype.sum_bool, Finset.sum_add_distrib]
  abel

theorem card_assocPhase_true_eq (k : ℕ) :
    (Finset.univ.filter fun t : BitVec k × BitVec k × BitVec k =>
        assocPhase t.1 t.2.1 t.2.2 = true).card = phaseCount k := by
  rw [Finset.card_filter, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [Fintype.sum_prod_type]

/-- At order `k + 1` with `n = 2^(k+1)` the number of non-associating ordered basis triples is
`(n - 2) (n - 4) (n + 6) / 2`, stated as twice the count. The Rocq original is
`associator_census_formula` of `rocq/open/theories/CDAssociatorCensus.v`, whose
`associator_phase order l m r` is `assocPhase l m r` (value `168` at the octonions). The proof sums
over the three top bits: by `assocPhase_cons` a triple of the low parts contributes `4` unless its
three pairs are degenerate, in which case it contributes `0`, and `7 * 2^k - 6` triples are of the
second kind (`sum_thin`). -/
theorem card_assocPhase_true (k : ℕ) :
    2 * ((Finset.univ.filter fun t : BitVec (k + 1) × BitVec (k + 1) × BitVec (k + 1) =>
        assocPhase t.1 t.2.1 t.2.2 = true).card : ℤ) =
      (2 ^ (k + 1) - 2) * (2 ^ (k + 1) - 4) * (2 ^ (k + 1) + 6) := by
  rw [card_assocPhase_true_eq, phaseCount_succ]
  set S : ℕ := ∑ l : BitVec k, ∑ m : BitVec k, ∑ r : BitVec k,
    if (commPhase m r = false ∧ commPhase l m = false ∧ commPhase l (m ^^^ r) = false)
      then 0 else 4 with hSdef
  have hpt : ∀ l m r : BitVec k,
      (if (commPhase m r = false ∧ commPhase l m = false ∧ commPhase l (m ^^^ r) = false)
        then 0 else 4) +
      4 * (if (commPhase m r = false ∧ commPhase l m = false ∧ commPhase l (m ^^^ r) = false)
        then 1 else 0) = 4 := by
    intro l m r
    split_ifs <;> simp
  have hS : S + 4 * (7 * 2 ^ k - 6) = 4 * (2 ^ k) ^ 3 := by
    rw [← sum_thin k, hSdef, Finset.mul_sum, ← Finset.sum_add_distrib]
    have : ∀ l : BitVec k, (∑ m : BitVec k, ∑ r : BitVec k,
        if (commPhase m r = false ∧ commPhase l m = false ∧ commPhase l (m ^^^ r) = false)
          then 0 else 4) +
        4 * (∑ m : BitVec k, ∑ r : BitVec k,
          if (commPhase m r = false ∧ commPhase l m = false ∧ commPhase l (m ^^^ r) = false)
            then 1 else 0) = 4 * (2 ^ k) ^ 2 := by
      intro l
      rw [Finset.mul_sum, ← Finset.sum_add_distrib]
      have : ∀ m : BitVec k, (∑ r : BitVec k,
          if (commPhase m r = false ∧ commPhase l m = false ∧ commPhase l (m ^^^ r) = false)
            then 0 else 4) +
          4 * (∑ r : BitVec k,
            if (commPhase m r = false ∧ commPhase l m = false ∧ commPhase l (m ^^^ r) = false)
              then 1 else 0) = 4 * 2 ^ k := by
        intro m
        rw [Finset.mul_sum, ← Finset.sum_add_distrib]
        rw [Finset.sum_congr rfl fun r _ => hpt l m r]
        simp [card_bitVec, mul_comm]
      rw [Finset.sum_congr rfl fun m _ => this m]
      simp [card_bitVec]
      ring
    rw [Finset.sum_congr rfl fun l _ => this l]
    simp [card_bitVec]
    ring
  have h6 : 6 ≤ 7 * 2 ^ k := by
    have := Nat.one_le_two_pow (n := k)
    omega
  have hZ : (S : ℤ) + 4 * (7 * 2 ^ k - 6) = 4 * (2 ^ k) ^ 3 := by
    have := congrArg (Nat.cast : ℕ → ℤ) hS
    push_cast [Nat.cast_sub h6] at this
    exact this
  rw [pow_succ]
  linear_combination 2 * hZ

end Triples

end Tower

end CayleyDickson
