/- SPDX-License-Identifier: Apache-2.0 -/
module

public import GororobaMath.CayleyDickson.Map
public import GororobaMath.CayleyDickson.BasisExt

/-!
# Base change of a linear map of the Cayley-Dickson tower

Convention: `Tower R k` is the `k`-fold Cayley-Dickson double of a commutative ring `R` whose
star is the identity (`TrivialStar R`), with the basis `Tower.e R k p`, `p : BitVec k`, of
`GororobaMath.CayleyDickson.Tower`. For a ring homomorphism `φ : R →+* S` between two such
rings, `Tower.map φ k` applies `φ` to every coordinate: level `0` is `φ` and level `k + 1` is
`CayleyDickson.map` of level `k`, so it is a non-unital ring homomorphism that sends `e R k p` to
`e S k p`. For a linear map `F` of `Tower R k`, `Tower.baseChange φ F` is the `S`-linear map
of `Tower S k` that sends `e S k p` to `map φ k (F (e R k p))`: the transport of the matrix of
`F` along `φ`.

## Main results

* `Tower.baseChange_mul`: a scaled multiplicativity `F (e i) * F (e j) = c • F (e i * e j)` on
  the basis pairs over `R` gives `baseChange φ F x * baseChange φ F y = φ c • baseChange φ F (x * y)`
  over `S`. The Rocq original is `scaled_multiplicative_transport` of the functor `BaseChange`
  in `rocq/quantum/CdTowerRingBaseChange.v`.
* `Tower.baseChange_leibniz`: the Leibniz rule on the basis pairs over `R` gives the Leibniz rule
  for `baseChange φ F` over `S`. The Rocq original is `derivation_transport` of the same
  functor.
-/

@[expose] public section

namespace CayleyDickson

namespace Tower

universe u v

variable {R : Type u} {S : Type v} [CommRing R] [StarRing R] [TrivialStar R]
  [CommRing S] [StarRing S] [TrivialStar S]

/-- The coordinatewise image of an element of `Tower R k` under `φ`. -/
def map (φ : R →+* S) : (k : ℕ) → Tower R k → Tower S k
  | 0, x => φ x
  | k + 1, x => mk (map φ k x.re) (map φ k x.im)

omit [StarRing R] [TrivialStar R] [StarRing S] [TrivialStar S] in
theorem map_mk (φ : R →+* S) {k : ℕ} (a b : Tower R k) :
    map φ (k + 1) (mk a b) = mk (map φ k a) (map φ k b) := rfl

omit [TrivialStar R] [TrivialStar S] in
theorem map_zero (φ : R →+* S) : ∀ k : ℕ, map φ k (0 : Tower R k) = 0
  | 0 => _root_.map_zero φ
  | k + 1 => by
    rw [zero_eq_mk, map_mk, map_zero φ k, zero_eq_mk]

omit [TrivialStar R] [TrivialStar S] in
theorem map_one (φ : R →+* S) : ∀ k : ℕ, map φ k (1 : Tower R k) = 1
  | 0 => _root_.map_one φ
  | k + 1 => by
    rw [one_eq_mk, map_mk, map_one φ k, map_zero, one_eq_mk]

omit [TrivialStar R] [TrivialStar S] in
theorem map_neg (φ : R →+* S) : ∀ (k : ℕ) (x : Tower R k), map φ k (-x) = -map φ k x
  | 0, x => _root_.map_neg φ x
  | k + 1, x => by
    obtain ⟨a, b⟩ := x
    change map φ (k + 1) (-mk a b) = -mk (map φ k a) (map φ k b)
    rw [neg_mk, map_mk, map_neg φ k, map_neg φ k, neg_mk]

omit [TrivialStar R] [TrivialStar S] in
theorem map_add (φ : R →+* S) :
    ∀ (k : ℕ) (x y : Tower R k), map φ k (x + y) = map φ k x + map φ k y
  | 0, x, y => _root_.map_add φ x y
  | k + 1, x, y => by
    obtain ⟨a, b⟩ := x
    obtain ⟨c, d⟩ := y
    change map φ (k + 1) (mk (a + c) (b + d)) = mk (map φ k a) (map φ k b) + mk (map φ k c) (map φ k d)
    rw [map_mk, map_add φ k, map_add φ k]
    rfl

omit [TrivialStar R] [TrivialStar S] in
theorem map_sub (φ : R →+* S) (k : ℕ) (x y : Tower R k) :
    map φ k (x - y) = map φ k x - map φ k y := by
  rw [sub_eq_add_neg, map_add, map_neg, ← sub_eq_add_neg]

theorem map_star (φ : R →+* S) : ∀ (k : ℕ) (x : Tower R k), map φ k (star x) = star (map φ k x)
  | 0, x => by
    exact (congrArg φ (star_trivial (R := R) x)).trans (star_trivial (R := S) (φ x)).symm
  | k + 1, x => by
    obtain ⟨a, b⟩ := x
    change map φ (k + 1) (star (mk a b)) = star (mk (map φ k a) (map φ k b))
    rw [star_mk, map_mk, map_star φ k, map_neg φ k, star_mk]

theorem map_mul (φ : R →+* S) : ∀ (k : ℕ) (x y : Tower R k), map φ k (x * y) = map φ k x * map φ k y
  | 0, x, y => _root_.map_mul φ x y
  | k + 1, x, y => by
    obtain ⟨a, b⟩ := x
    obtain ⟨c, d⟩ := y
    change map φ (k + 1) (mk a b * mk c d) = mk (map φ k a) (map φ k b) * mk (map φ k c) (map φ k d)
    rw [mk_mul_mk, mk_mul_mk, map_mk, map_sub, map_add, map_mul φ k, map_mul φ k, map_mul φ k,
      map_mul φ k, map_star, map_star]

omit [TrivialStar R] [TrivialStar S] in
theorem map_smul (φ : R →+* S) : ∀ (k : ℕ) (c : R) (z : Tower R k),
    map φ k (c • z) = φ c • map φ k z
  | 0, c, z => by
    exact _root_.map_mul φ c (show R from z)
  | k + 1, c, z => by
    obtain ⟨a, b⟩ := z
    change map φ (k + 1) (c • mk a b) = φ c • mk (map φ k a) (map φ k b)
    rw [smul_mk, map_mk, map_smul φ k c a, map_smul φ k c b, smul_mk]

omit [TrivialStar R] [TrivialStar S] in
theorem map_e (φ : R →+* S) : ∀ (k : ℕ) (p : BitVec k), map φ k (e R k p) = e S k p
  | 0, p => by
    change φ 1 = 1
    exact _root_.map_one φ
  | k + 1, p => by
    cases h : p.msb
    · rw [e_succ_of_not_msb h, e_succ_of_not_msb h, map_mk, map_e φ k, map_zero]
    · rw [e_succ_of_msb h, e_succ_of_msb h, map_mk, map_e φ k, map_zero]

theorem map_e_mul_e (φ : R →+* S) {k : ℕ} (i j : BitVec k) :
    e S k i * e S k j = map φ k (e R k i * e R k j) := by
  rw [map_mul, map_e, map_e]

/-- The transport of a linear map of `Tower R k` along `φ`. -/
noncomputable def baseChange (φ : R →+* S) {k : ℕ} (F : Tower R k →ₗ[R] Tower R k) :
    Tower S k →ₗ[S] Tower S k :=
  (basis S k).constr S fun i => map φ k (F (e R k i))

omit [TrivialStar R] [TrivialStar S] in
theorem baseChange_e (φ : R →+* S) {k : ℕ} (F : Tower R k →ₗ[R] Tower R k) (i : BitVec k) :
    baseChange φ F (e S k i) = map φ k (F (e R k i)) := by
  rw [← basis_apply, baseChange, Module.Basis.constr_basis]

omit [TrivialStar R] [TrivialStar S] in
theorem baseChange_e_mul_e (φ : R →+* S) {k : ℕ} (F : Tower R k →ₗ[R] Tower R k)
    (i j : BitVec k) :
    baseChange φ F (e S k i * e S k j) = map φ k (F (e R k i * e R k j)) := by
  rw [e_mul_e, e_mul_e]
  split_ifs
  · rw [_root_.map_neg, _root_.map_neg, map_neg, baseChange_e]
  · exact baseChange_e φ F _

/-- A scaled multiplicativity of `F` on the basis pairs over `R` transports to every pair over
`S`. The Rocq original is `scaled_multiplicative_transport` of the functor `BaseChange` in
`rocq/quantum/CdTowerRingBaseChange.v`. -/
theorem baseChange_mul (φ : R →+* S) {k : ℕ} (F : Tower R k →ₗ[R] Tower R k) (c : R)
    (h : ∀ i j, F (e R k i) * F (e R k j) = c • F (e R k i * e R k j)) (x y : Tower S k) :
    baseChange φ F x * baseChange φ F y = φ c • baseChange φ F (x * y) := by
  have hb : ∀ i j, baseChange φ F (e S k i) * baseChange φ F (e S k j) =
      φ c • baseChange φ F (e S k i * e S k j) := by
    intro i j
    rw [baseChange_e, baseChange_e, baseChange_e_mul_e, ← map_mul, h, map_smul]
  have hrow : ∀ i z, baseChange φ F (e S k i) * baseChange φ F z =
      φ c • baseChange φ F (e S k i * z) := by
    intro i
    have hl : mulLeft S k (baseChange φ F (e S k i)) ∘ₗ baseChange φ F =
        φ c • (baseChange φ F ∘ₗ mulLeft S k (e S k i)) :=
      (basis S k).ext fun j => by
        simp only [LinearMap.comp_apply, LinearMap.smul_apply, mulLeft_apply, basis_apply, hb]
    exact fun z => LinearMap.congr_fun hl z
  have hr : mulRight S k (baseChange φ F y) ∘ₗ baseChange φ F =
      φ c • (baseChange φ F ∘ₗ mulRight S k y) :=
    (basis S k).ext fun i => by
      simp only [LinearMap.comp_apply, LinearMap.smul_apply, mulRight_apply, basis_apply, hrow]
  exact LinearMap.congr_fun hr x

/-- The Leibniz rule of `F` on the basis pairs over `R` transports to every pair over `S`. The
Rocq original is `derivation_transport` of the functor `BaseChange` in
`rocq/quantum/CdTowerRingBaseChange.v`. -/
theorem baseChange_leibniz (φ : R →+* S) {k : ℕ} (F : Tower R k →ₗ[R] Tower R k)
    (h : ∀ i j, F (e R k i * e R k j) = F (e R k i) * e R k j + e R k i * F (e R k j))
    (x y : Tower S k) :
    baseChange φ F (x * y) = baseChange φ F x * y + x * baseChange φ F y := by
  refine leibniz_of_leibniz_e (baseChange φ F) (fun i j => ?_) x y
  rw [baseChange_e_mul_e, h, map_add, map_mul, map_mul, map_e, map_e, baseChange_e, baseChange_e]

end Tower

end CayleyDickson
