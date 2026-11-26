/- SPDX-License-Identifier: Apache-2.0 -/
module

public import GororobaMath.LinearAlgebra.PfaffianTable
public import GororobaMath.LinearAlgebra.PfaffianForm
public import GororobaMath.CayleyDickson.Tower

/-!
# The bordered sixteen-by-sixteen Pfaffian: statement, and its reduction to two kernel checks

Convention: `borderedA z t` is the matrix of the level-4 left multiplication by a pure element
bordered by a vector: row and column `0` carry `-t b` and `t a`, and for `a ≠ b` both nonzero the
entry is `Tower.sign 4 (a ^^^ b) b * z (a ^^^ b)`, the `e_(a xor b) * e_b` coefficient times the
coordinate of `z` at `a ^^^ b`, which is `cd_sign(16, a xor b, b) * z_(a xor b)`. The vectors `z`
and `t` are functions `ℕ → R` read at `1, ..., 15`. With `Q = z.z`, `U = u.u`, `V = v.v`,
`W = u.v` for `u = (z_1, ..., z_7)` and `v = (z_9, ..., z_15)`, `Δ = U V - W²` and `G = Q² - 4 Δ`,
the Pfaffian of `borderedA z t` on the indices `0, ..., 15` is `-(z.t) Q G`.

The identity is proved by a certificate: a table of polynomial Pfaffians of the even subsets of
`1, ..., 15` over the variables `z_1, ..., z_15, t_1, ..., t_15` (the primes `primes30`), whose
local consistency `checkTbl` and whose root agreement `rootCheck` are two kernel evaluations.
`pfaffian_sixteen_of_certificates` derives the identity over every commutative ring from them.

The Rocq partner is `Amat`, `memo` and `check_table` of `rocq/quantum/StiefelA5Certificate.v`.

## Main results

* `PfaffianSixteen.pfaffian_sixteen_of_certificates`: the identity over every commutative ring,
  given the two checks.
-/

@[expose] public section

namespace PfaffianSixteen

open SparsePoly PfaffianTable

/-- The thirty variable primes: `z_k` is the `k`-th, `t_k` the `(15 + k)`-th. -/
def primes30 : List ℕ :=
  [2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47, 53, 59, 61, 67, 71, 73, 79, 83, 89, 97,
    101, 103, 107, 109, 113]

/-- The prime of the variable `k`, for `1 ≤ k ≤ 30`. -/
def vp (k : ℕ) : ℕ := primes30.getD (k - 1) 2

/-- The polynomial entry `(a, b)` of the bordered matrix. -/
def Aent (a b : ℕ) : Poly :=
  if a = b then []
  else if a = 0 then [(varCode (vp (15 + b)), -1)]
  else if b = 0 then [(varCode (vp (15 + a)), 1)]
  else [(varCode (vp (a ^^^ b)),
    CayleyDickson.Tower.sign 4 (BitVec.ofNat 4 (a ^^^ b)) (BitVec.ofNat 4 b))]

/-- The index list `0, 1, ..., 15`. -/
def rootList : List ℕ := 0 :: List.range' 1 15

/-- The sum of `f 0, ..., f (n - 1)` as a polynomial. -/
def sumRange (n : ℕ) (f : ℕ → Poly) : Poly := psum ((List.range n).map f)

/-- The polynomial of `z_k`. -/
def zv (k : ℕ) : Poly := varP (vp k)

/-- The polynomial of `t_k`. -/
def tv (k : ℕ) : Poly := varP (vp (15 + k))

/-- `Q = z.z`. -/
def QP : Poly := sumRange 15 fun k => pmul (zv (k + 1)) (zv (k + 1))
/-- `U = u.u`. -/
def UP : Poly := sumRange 7 fun k => pmul (zv (k + 1)) (zv (k + 1))
/-- `V = v.v`. -/
def VP : Poly := sumRange 7 fun k => pmul (zv (k + 9)) (zv (k + 9))
/-- `W = u.v`. -/
def WP : Poly := sumRange 7 fun k => pmul (zv (k + 1)) (zv (k + 9))
/-- `G = Q² - 4 (U V - W²)`. -/
def GP : Poly := padd (pmul QP QP) (pmul (constP (-4)) (padd (pmul UP VP) (pneg (pmul WP WP))))
/-- `-(z.t) Q G`. -/
def rhsP : Poly :=
  pneg (pmul (sumRange 15 fun k => pmul (zv (k + 1)) (tv (k + 1))) (pmul QP GP))

/-- The root agreement: the expansion of the root list over the table, minus `rhsP`, is zero. -/
def rootCheck (tbl : Tr (List ℕ × Poly)) : Bool :=
  decide ((expand Aent tbl rootList).map (fun p => padd p (pneg rhsP)) = some [])

variable {R : Type*} [CommRing R]

/-- The bordered matrix over `R`. -/
def borderedA (z t : ℕ → R) (a b : ℕ) : R :=
  if a = b then 0 else if a = 0 then -t b else if b = 0 then t a
  else (CayleyDickson.Tower.sign 4 (BitVec.ofNat 4 (a ^^^ b)) (BitVec.ofNat 4 b) : R) * z (a ^^^ b)

/-- `Q = z.z` over `R`. -/
def qv (z : ℕ → R) : R := ∑ k ∈ Finset.range 15, z (k + 1) * z (k + 1)
/-- `U = u.u` over `R`. -/
def uv (z : ℕ → R) : R := ∑ k ∈ Finset.range 7, z (k + 1) * z (k + 1)
/-- `V = v.v` over `R`. -/
def vv (z : ℕ → R) : R := ∑ k ∈ Finset.range 7, z (k + 9) * z (k + 9)
/-- `W = u.v` over `R`. -/
def wv (z : ℕ → R) : R := ∑ k ∈ Finset.range 7, z (k + 1) * z (k + 9)
/-- `G = Q² - 4 (U V - W²)` over `R`. -/
def gv (z : ℕ → R) : R := qv z ^ 2 - 4 * (uv z * vv z - wv z ^ 2)
/-- The right-hand side `-(z.t) Q G` over `R`. -/
def rhsv (z t : ℕ → R) : R := -(∑ k ∈ Finset.range 15, z (k + 1) * t (k + 1)) * qv z * gv z

/-- The value of variable `k`: `z_k` up to `15`, then `t_(k - 15)`. -/
def vOf (z t : ℕ → R) (k : ℕ) : R := if k ≤ 15 then z k else t (k - 15)

/-- The environment sending the `k`-th prime of `primes30` to `v k`. -/
def envOf (v : ℕ → R) (p : ℕ) : R := v (primes30.idxOf p + 1)

theorem vp_prime {k : ℕ} (h1 : 1 ≤ k) (h2 : k ≤ 30) : (vp k).Prime := by
  interval_cases k <;> (unfold vp primes30; norm_num)

theorem idxOf_vp {k : ℕ} (h1 : 1 ≤ k) (h2 : k ≤ 30) : primes30.idxOf (vp k) + 1 = k := by
  interval_cases k <;> decide

omit [CommRing R] in
theorem envOf_vp (v : ℕ → R) {k : ℕ} (h1 : 1 ≤ k) (h2 : k ≤ 30) : envOf v (vp k) = v k := by
  unfold envOf
  rw [idxOf_vp h1 h2]

theorem evP_single (env : ℕ → R) {p : ℕ} (hp : p.Prime) (s : ℤ) :
    evP env [(varCode p, s)] = s * env p := by
  simp [evP, monEv_varCode env hp]

theorem evP_zv (z t : ℕ → R) {k : ℕ} (h1 : 1 ≤ k) (h2 : k ≤ 15) :
    evP (envOf (vOf z t)) (zv k) = z k := by
  unfold zv
  rw [evP_varP _ (vp_prime h1 (by omega)), envOf_vp _ h1 (by omega)]
  simp [vOf, h2]

theorem evP_tv (z t : ℕ → R) {k : ℕ} (h1 : 1 ≤ k) (h2 : k ≤ 15) :
    evP (envOf (vOf z t)) (tv k) = t k := by
  unfold tv
  rw [evP_varP _ (vp_prime (by omega) (by omega)), envOf_vp _ (by omega) (by omega)]
  simp [vOf]
  omega

theorem evP_Aent (z t : ℕ → R) {a b : ℕ} (ha : a < 16) (hb : b < 16) :
    evP (envOf (vOf z t)) (Aent a b) = borderedA z t a b := by
  unfold Aent borderedA
  by_cases hab : a = b
  · simp [hab]
  by_cases ha0 : a = 0
  · have hb0 : 1 ≤ b := by omega
    subst ha0
    simp only [hab, ↓reduceIte]
    rw [evP_single _ (vp_prime (by omega) (by omega)), envOf_vp _ (by omega) (by omega)]
    simp [vOf]
    omega
  by_cases hb0 : b = 0
  · have ha1 : 1 ≤ a := by omega
    subst hb0
    simp only [hab, ↓reduceIte]
    rw [evP_single _ (vp_prime (by omega) (by omega)), envOf_vp _ (by omega) (by omega)]
    simp [vOf]
    omega
  · simp only [hab, ha0, hb0, ↓reduceIte]
    have hx : a ^^^ b < 16 := Nat.xor_lt_two_pow (n := 4) (by omega) (by omega)
    have hx1 : 1 ≤ a ^^^ b := by
      rcases Nat.eq_zero_or_pos (a ^^^ b) with h | h
      · exfalso
        apply hab
        have h2 : a ^^^ b ^^^ b = a := by simp
        rw [h, Nat.zero_xor] at h2
        exact h2.symm
      · exact h
    rw [evP_single _ (vp_prime hx1 (by omega)), envOf_vp _ hx1 (by omega)]
    simp [vOf, show a ^^^ b ≤ 15 by omega]

theorem list_sum_range (g : ℕ → R) (n : ℕ) :
    ((List.range n).map g).sum = ∑ k ∈ Finset.range n, g k := by
  induction n with
  | zero => simp
  | succ n ih => simp [List.range_succ, Finset.sum_range_succ, ih]

theorem evP_sumRange (env : ℕ → R) (n : ℕ) (f : ℕ → Poly) :
    evP env (sumRange n f) = ∑ k ∈ Finset.range n, evP env (f k) := by
  unfold sumRange
  rw [evP_psum, List.map_map, ← list_sum_range]
  rfl

theorem evP_rhsP (z t : ℕ → R) : evP (envOf (vOf z t)) rhsP = rhsv z t := by
  have hz : ∀ k ∈ Finset.range 15, ∀ j, j = k + 1 → evP (envOf (vOf z t)) (zv j) = z j := by
    intro k hk j hj
    rw [Finset.mem_range] at hk
    exact evP_zv z t (by omega) (by omega)
  have hz9 : ∀ k ∈ Finset.range 7, evP (envOf (vOf z t)) (zv (k + 9)) = z (k + 9) := fun k hk =>
    evP_zv z t (by omega) (by rw [Finset.mem_range] at hk; omega)
  have hz1 : ∀ k ∈ Finset.range 7, evP (envOf (vOf z t)) (zv (k + 1)) = z (k + 1) := fun k hk =>
    evP_zv z t (by omega) (by rw [Finset.mem_range] at hk; omega)
  have hQ : evP (envOf (vOf z t)) QP = qv z := by
    unfold QP qv
    rw [evP_sumRange]
    refine Finset.sum_congr rfl fun k hk => ?_
    rw [evP_pmul, hz k hk _ rfl]
  have hU : evP (envOf (vOf z t)) UP = uv z := by
    unfold UP uv
    rw [evP_sumRange]
    refine Finset.sum_congr rfl fun k hk => ?_
    rw [evP_pmul, hz1 k hk]
  have hV : evP (envOf (vOf z t)) VP = vv z := by
    unfold VP vv
    rw [evP_sumRange]
    refine Finset.sum_congr rfl fun k hk => ?_
    rw [evP_pmul, hz9 k hk]
  have hW : evP (envOf (vOf z t)) WP = wv z := by
    unfold WP wv
    rw [evP_sumRange]
    refine Finset.sum_congr rfl fun k hk => ?_
    rw [evP_pmul, hz1 k hk, hz9 k hk]
  have hG : evP (envOf (vOf z t)) GP = gv z := by
    unfold GP gv
    rw [evP_padd, evP_pmul, evP_pmul, evP_constP, evP_padd, evP_pmul, evP_pneg, evP_pmul, hQ, hU,
      hV, hW]
    push_cast
    ring
  unfold rhsP rhsv
  rw [evP_pneg, evP_pmul, evP_pmul, evP_sumRange, hQ, hG]
  have : ∑ k ∈ Finset.range 15, evP (envOf (vOf z t)) (pmul (zv (k + 1)) (tv (k + 1))) =
      ∑ k ∈ Finset.range 15, z (k + 1) * t (k + 1) := by
    refine Finset.sum_congr rfl fun k hk => ?_
    rw [Finset.mem_range] at hk
    rw [evP_pmul, evP_zv z t (by omega) (by omega), evP_tv z t (by omega) (by omega)]
  rw [this]
  ring

/-- The identity `Pf A(z, t) = -(z.t) Q G` over every commutative ring, from the two kernel
checks of the table. -/
theorem pfaffian_sixteen_of_certificates (tbl : Tr (List ℕ × Poly))
    (hc : checkTbl Aent tbl = true) (hr : rootCheck tbl = true)
    (z t : ℕ → R) :
    Matrix.pfaffian (Matrix.of fun a b : Fin 16 => borderedA z t a b) = rhsv z t := by
  set env : ℕ → R := envOf (vOf z t) with henv
  unfold rootCheck at hr
  rw [decide_eq_true_iff] at hr
  rcases hex : expand Aent tbl rootList with _ | P
  · rw [hex] at hr; simp at hr
  · rw [hex] at hr
    simp only [Option.map_some, Option.some.injEq] at hr
    have hs := snd_of_check env Aent hc 15
    have h1 : evP env P = Matrix.pfaffianAux (AR env Aent) rootList :=
      ev_expand env Aent _ 0 (List.range' 1 15) (by simpa using hs) P hex
    have h2 : evP env P = rhsv z t := by
      have h3 := congrArg (evP env) hr
      rw [evP_padd, evP_pneg, evP_nil, evP_rhsP] at h3
      linear_combination h3
    have h5 := Matrix.pfaffianAux_reindex (AR env Aent) (Fin.val : Fin 16 → ℕ) 16
      (List.finRange 16) (by simp)
    have h7 : (List.finRange 16).map (Fin.val : Fin 16 → ℕ) = rootList := by decide
    rw [h7] at h5
    have h6 : (fun a b : Fin 16 => AR env Aent a.val b.val) =
        fun a b : Fin 16 => borderedA z t a b := by
      funext a b
      exact evP_Aent z t a.isLt b.isLt
    rw [h6] at h5
    unfold Matrix.pfaffian
    rw [← h2, h1, ← h5]
    rfl

end PfaffianSixteen
