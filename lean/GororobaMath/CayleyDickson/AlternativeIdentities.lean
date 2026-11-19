/- SPDX-License-Identifier: Apache-2.0 -/
module

public import GororobaMath.CayleyDickson.Alternative
public import GororobaMath.CayleyDickson.AlternativeCoordinates
public import GororobaMath.CayleyDickson.NormMultiplicative

/-!
# Identities of alternative algebras in the tower, levels up to 3

Convention: the product of `Tower R k` is the Cayley-Dickson product
`(a, b) (c, d) = (a c - star d b, d a + b star c)` of `GororobaMath.CayleyDickson.Basic`,
the associator is `associator a b c = (a * b) * c - a * (b * c)` and the commutator is
`commutator a b = a * b - b * a`. The level results read over a commutative ring `R` with the
identity as star, the failure results over a ring in which `2 ≠ 0`.

## Main results

* `commutator_commutator_cyclic_sum`: in every non-associative ring the cyclic sum of the double
  commutators `[[a, b], c]` is the cyclic sum of the associators minus the anticyclic sum.
* `Tower.commutator_commutator_cyclic_sum_of_le_three`: with the alternating associator of
  levels up to 3, that cyclic sum is `6 A(a, b, c)`; `Tower.jacobi_of_le_three` is the Jacobi sum
  `[a, [b, c]] + [b, [c, a]] + [c, [a, b]] = -6 A(a, b, c)`, which vanishes at levels up to 2.
* `Tower.associator_cyclic_sum_of_le_three`: `A(a, b, c) + A(b, c, a) + A(c, a, b) = 3 A(a, b, c)`.
* `Tower.associator_add_swap_eq_zero_of_le_three`, `Tower.dot_alt_add_dot_sym`: the symmetric part
  of the associator in its first two slots vanishes, and the two parts of the split satisfy the
  parallelogram law at every level.
* `Tower.innerDer_leibniz_of_le_three`: `D(a, b)(x) = [[a, b], x] - 3 A(a, b, x)` satisfies the
  Leibniz rule at levels up to 3.
* `Tower.mulLeft_sq_of_le_three`: `L_a^2 = L_(a a)` at levels up to 3, and
  `Tower.mulLeft_sq_iff`: it holds at every `a` exactly at the levels up to 3.
* `Tower.star_mul_mul_of_le_three`: the left inverse property `star x * (x * y) = dot x x • y`.
-/

@[expose] public section

namespace CayleyDickson

/-- The commutator `a * b - b * a`. -/
def commutator {A : Type*} [Mul A] [Sub A] (a b : A) : A := a * b - b * a

section Abstract

variable {A : Type*} [NonAssocRing A]

theorem commutator_anticomm (a b : A) : commutator a b = -commutator b a :=
  (neg_sub _ _).symm

/-- The cyclic sum of the double commutators is the cyclic sum of the associators minus the
anticyclic sum, in every non-associative ring. -/
theorem commutator_commutator_cyclic_sum (a b c : A) :
    commutator (commutator a b) c + commutator (commutator b c) a +
        commutator (commutator c a) b =
      (associator a b c + associator b c a + associator c a b) -
        (associator b a c + associator c b a + associator a c b) := by
  simp only [commutator, associator, mul_sub, sub_mul]
  abel

/-- The defect of the Leibniz rule for the commutator with `c` is a sum of associators with `c`. -/
theorem commutator_mul_sub (c x y : A) :
    commutator c (x * y) - commutator c x * y - x * commutator c y =
      -associator c x y - associator x y c + associator x c y := by
  simp only [commutator, associator, mul_sub, sub_mul]
  abel

theorem commutator_neg_left (a b : A) : commutator (-a) b = -commutator a b := by
  simp only [commutator, neg_mul, mul_neg]
  abel

theorem commutator_zsmul_left (n : ℤ) (a b : A) : commutator (n • a) b = n • commutator a b := by
  simp only [commutator, smul_mul_assoc, mul_smul_comm, smul_sub]

/-- The inner derivation `D(a, b)(x) = [[a, b], x] - 3 A(a, b, x)`. -/
def innerDer (a b x : A) : A := commutator (commutator a b) x - (3 : ℤ) • associator a b x

theorem innerDer_zsmul_right (n : ℤ) (a b x : A) :
    innerDer a b (n • x) = n • innerDer a b x := by
  simp only [innerDer, commutator, associator, mul_smul_comm, smul_mul_assoc, smul_sub,
    smul_comm n (3 : ℤ)]

/-- The sum of three double commutators, `[[a, b], x] + [[a, x], b] + [[x, b], a]`. -/
def innerDerSum (a b x : A) : A :=
  commutator (commutator a b) x + commutator (commutator a x) b + commutator (commutator x b) a

theorem innerDerSum_zsmul_right (n : ℤ) (a b x : A) :
    innerDerSum a b (n • x) = n • innerDerSum a b x := by
  simp only [innerDerSum, commutator, sub_mul, mul_sub, mul_smul_comm, smul_mul_assoc, smul_sub,
    smul_add]

end Abstract

namespace Tower

universe u

section LevelThree

variable {R : Type u} [CommRing R] [StarRing R] [TrivialStar R] {k : ℕ}

/-- The associator vanishes at levels up to 2. -/
theorem associator_eq_zero_of_le_two (hk : k ≤ 2) (x y z : Tower R k) : associator x y z = 0 := by
  interval_cases k
  · exact (associator_lift_eq_zero_iff 0 2 x y z).1 (associator_two _ _ _)
  · exact (associator_lift_eq_zero_iff 1 1 x y z).1 (associator_two _ _ _)
  · exact associator_two x y z

/-- The cyclic sum of the associator is three times the associator at levels up to 3. -/
theorem associator_cyclic_sum_of_le_three (hk : k ≤ 3) (a b c : Tower R k) :
    associator a b c + associator b c a + associator c a b = (3 : ℤ) • associator a b c := by
  have h1 := (associator_cyclic_of_le_three hk a b c).symm
  have h2 := (associator_cyclic_of_le_three hk b c a).symm.trans h1
  rw [h1, h2]
  abel

/-- The anticyclic sum of the associator is minus three times the associator at levels up to 3. -/
theorem associator_anticyclic_sum_of_le_three (hk : k ≤ 3) (a b c : Tower R k) :
    associator b a c + associator c b a + associator a c b = (-3 : ℤ) • associator a b c := by
  have h1 := eq_neg_of_add_eq_zero_right (associator_add_swap_left_of_le_three hk a b c)
  have h2 := eq_neg_of_add_eq_zero_left (associator_add_swap_left_of_le_three hk c b a)
  have h3 := eq_neg_of_add_eq_zero_right (associator_add_swap_right_of_le_three hk a b c)
  rw [h1, h2, h3, ← associator_cyclic_of_le_three hk a b c]
  abel

/-- The cyclic sum of the double commutators is six times the associator at levels up to 3. -/
theorem commutator_commutator_cyclic_sum_of_le_three (hk : k ≤ 3) (a b c : Tower R k) :
    commutator (commutator a b) c + commutator (commutator b c) a +
        commutator (commutator c a) b = (6 : ℤ) • associator a b c := by
  rw [commutator_commutator_cyclic_sum, associator_cyclic_sum_of_le_three hk,
    associator_anticyclic_sum_of_le_three hk]
  abel

/-- The Jacobi sum is minus six times the associator at levels up to 3. -/
theorem jacobi_of_le_three (hk : k ≤ 3) (a b c : Tower R k) :
    commutator a (commutator b c) + commutator b (commutator c a) +
        commutator c (commutator a b) = (-6 : ℤ) • associator a b c := by
  have h := commutator_commutator_cyclic_sum_of_le_three hk a b c
  rw [commutator_anticomm a (commutator b c), commutator_anticomm b (commutator c a),
    commutator_anticomm c (commutator a b)]
  have e : ∀ u v w : Tower R k, -u + -v + -w = -(w + u + v) := by
    intro u v w
    abel
  rw [e, h]
  abel

/-- The Jacobi sum vanishes at levels up to 2, where the product is associative. -/
theorem jacobi_eq_zero_of_le_two (hk : k ≤ 2) (a b c : Tower R k) :
    commutator a (commutator b c) + commutator b (commutator c a) +
        commutator c (commutator a b) = 0 := by
  rw [jacobi_of_le_three (by omega), associator_eq_zero_of_le_two hk, smul_zero]


/-- The identity behind the Leibniz rule of the inner derivation at level 3
(`associator_commutator_mul_three`). -/
theorem associator_commutator_mul_of_three (a b x y : Tower R 3) :
    associator (commutator a b) x y + associator a b (x * y) =
      associator a b x * y + x * associator a b y :=
  associator_commutator_mul_three a b x y

omit [TrivialStar R] in
/-- The parallelogram law for the split of two vectors into the difference and the sum, at every
level: the identity `|Alt|² + |Sym|² = 2 (|A|² + |B|²)` for `Alt = A - B` and `Sym = A + B`. -/
theorem dot_sub_self_add_dot_add_self (x y : Tower R k) :
    dot k (x - y) (x - y) + dot k (x + y) (x + y) = 2 * (dot k x x + dot k y y) := by
  simp only [dot_sub_left, dot_sub_right, dot_add_left, dot_add_right, dot_comm k y x]
  ring

/-- At levels up to 3 the alternating part of the associator in its first two slots is twice
the associator. -/
theorem associator_sub_swap_of_le_three (hk : k ≤ 3) (a b c : Tower R k) :
    associator a b c - associator b a c = (2 : ℤ) • associator a b c := by
  rw [eq_neg_of_add_eq_zero_right (associator_add_swap_left_of_le_three hk a b c)]
  abel

/-- At levels up to 3 the squared trace norm of the alternating part is four times that of the
associator. -/
theorem dot_alt_of_le_three (hk : k ≤ 3) (a b c : Tower R k) :
    dot k (associator a b c - associator b a c) (associator a b c - associator b a c) =
      4 * dot k (associator a b c) (associator a b c) := by
  rw [eq_neg_of_add_eq_zero_right (associator_add_swap_left_of_le_three hk a b c), sub_neg_eq_add]
  simp only [dot_add_left, dot_add_right]
  ring

/-- Left multiplication squares to left multiplication by the square at levels up to 3. -/
theorem mulLeft_sq_of_le_three (hk : k ≤ 3) (a : Tower R k) :
    mulLeft R k a * mulLeft R k a = mulLeft R k (a * a) :=
  LinearMap.ext fun y => left_alternative_of_le_three hk a y

/-- Left multiplication squares to left multiplication by the square for every element
exactly at the levels up to 3, over a ring in which `2 ≠ 0`. -/
theorem mulLeft_sq_iff (h2 : (2 : R) ≠ 0) :
    (∀ a : Tower R k, mulLeft R k a * mulLeft R k a = mulLeft R k (a * a)) ↔ k ≤ 3 := by
  refine ⟨fun h => ?_, fun hk a => mulLeft_sq_of_le_three hk a⟩
  by_contra hk
  obtain ⟨x, y, hxy⟩ := exists_left_alternative_ne h2 k (by omega)
  exact hxy (congrArg (fun f => f y) (h x)).symm

/-- The defect of the left inverse property is the defect of the left alternative law, at every
level: `star x * (x * y) - dot x x • y = (x x) y - x (x y)`. -/
theorem star_mul_mul_sub_eq (x y : Tower R k) :
    star x * (x * y) - dot k x x • y = x * x * y - x * (x * y) := by
  rw [star_eq_smul_one_sub x, mul_self_eq_smul_sub x]
  simp only [sub_mul, smul_mul_assoc', one_mul]
  abel

/-- The left inverse property `star x * (x * y) = dot x x • y` at levels up to 3. -/
theorem star_mul_mul_of_le_three (hk : k ≤ 3) (x y : Tower R k) :
    star x * (x * y) = dot k x x • y := by
  have h := star_mul_mul_sub_eq x y
  rw [left_alternative_of_le_three hk x y, sub_self] at h
  exact sub_eq_zero.1 h

/-- The right inverse property `(y * x) * star x = dot x x • y` at levels up to 3. -/
theorem mul_mul_star_of_le_three (hk : k ≤ 3) (x y : Tower R k) :
    y * x * star x = dot k x x • y := by
  have h := right_alternative_of_le_three hk x y
  rw [star_eq_smul_one_sub x, mul_sub, mul_smul_comm', mul_one, h, mul_self_eq_smul_sub x]
  simp only [mul_sub, mul_smul_comm', mul_one]
  abel

/-- The identity behind the Leibniz rule of the inner derivation at levels up to 3. -/
theorem associator_commutator_mul_of_le_three (hk : k ≤ 3) (a b x y : Tower R k) :
    associator (commutator a b) x y + associator a b (x * y) =
      associator a b x * y + x * associator a b y := by
  by_cases h2 : k ≤ 2
  · simp only [associator_eq_zero_of_le_two h2, zero_mul, mul_zero, add_zero]
  · obtain rfl : k = 3 := by omega
    exact associator_commutator_mul_of_three a b x y

/-- The inner derivation `D(a, b)(x) = [[a, b], x] - 3 A(a, b, x)` satisfies the Leibniz rule
`D(x y) = D(x) y + x D(y)` at levels up to 3. -/
theorem innerDer_leibniz_of_le_three (hk : k ≤ 3) (a b x y : Tower R k) :
    innerDer a b (x * y) = innerDer a b x * y + x * innerDer a b y := by
  have hG := associator_commutator_mul_of_le_three hk a b x y
  have h1 := commutator_mul_sub (commutator a b) x y
  have e1 : associator x y (commutator a b) = associator (commutator a b) x y :=
    (associator_cyclic_of_le_three hk (commutator a b) x y).symm
  have e2 : associator x (commutator a b) y = -associator (commutator a b) x y :=
    eq_neg_of_add_eq_zero_left (associator_add_swap_left_of_le_three hk x (commutator a b) y)
  rw [e1, e2] at h1
  have h3 : commutator (commutator a b) (x * y) = commutator (commutator a b) x * y +
      x * commutator (commutator a b) y + (-3 : ℤ) • associator (commutator a b) x y := by
    rw [show (-3 : ℤ) • associator (commutator a b) x y = -associator (commutator a b) x y -
      associator (commutator a b) x y + -associator (commutator a b) x y by abel, ← h1]
    abel
  have h2 : associator a b (x * y) = associator a b x * y + x * associator a b y -
      associator (commutator a b) x y := by
    rw [← hG]
    abel
  simp only [innerDer, sub_mul, mul_sub, smul_mul_assoc, mul_smul_comm, h3, h2]
  abel

/-- The sum of three double commutators is twice the inner derivation at levels up to 3. -/
theorem innerDerSum_eq_two_smul_of_le_three (hk : k ≤ 3) (a b x : Tower R k) :
    innerDerSum a b x = (2 : ℤ) • innerDer a b x := by
  have h := commutator_commutator_cyclic_sum_of_le_three hk a b x
  have e1 : commutator (commutator a x) b = -commutator (commutator x a) b := by
    rw [commutator_anticomm a x, commutator_neg_left]
  have e2 : commutator (commutator x b) a = -commutator (commutator b x) a := by
    rw [commutator_anticomm x b, commutator_neg_left]
  unfold innerDerSum innerDer
  rw [e1, e2]
  have h' : commutator (commutator a b) x + -commutator (commutator x a) b +
      -commutator (commutator b x) a = (2 : ℤ) • commutator (commutator a b) x -
        (commutator (commutator a b) x + commutator (commutator b x) a +
          commutator (commutator x a) b) := by
    abel
  rw [h', h]
  abel

/-- The sum of three double commutators satisfies the Leibniz rule at levels up to 3. -/
theorem innerDerSum_leibniz_of_le_three (hk : k ≤ 3) (a b x y : Tower R k) :
    innerDerSum a b (x * y) = innerDerSum a b x * y + x * innerDerSum a b y := by
  rw [innerDerSum_eq_two_smul_of_le_three hk, innerDerSum_eq_two_smul_of_le_three hk,
    innerDerSum_eq_two_smul_of_le_three hk, innerDer_leibniz_of_le_three hk, smul_add,
    smul_mul_assoc, mul_smul_comm]

/-- The associator `A(a, b, c)` is orthogonal to `c` for the trace form at levels up to 3. -/
theorem dot_associator_self_right_of_le_three (hk : k ≤ 3) (a b c : Tower R k) :
    dot k (associator a b c) c = 0 := by
  unfold associator
  rw [dot_sub_left, (dot_mul_adjoint k (a * b) c c).2, (dot_mul_adjoint k a (b * c) c).2,
    (mul_star_eq_dot k c).1, star_mul, mul_star_mul_left, star_mul_mul_of_le_three hk,
    dot_smul_right, dot_smul_right, (dot_mul_adjoint k a b 1).2, one_mul, sub_self]

/-- The map `c ↦ A(a, b, c)` is skew-symmetric for the trace form at levels up to 3. -/
theorem dot_associator_add_dot_associator_of_le_three (hk : k ≤ 3) (a b c d : Tower R k) :
    dot k (associator a b c) d + dot k c (associator a b d) = 0 := by
  have h := dot_associator_self_right_of_le_three hk a b (c + d)
  rw [associator_add_right, dot_add_left, dot_add_right, dot_add_right,
    dot_associator_self_right_of_le_three hk, dot_associator_self_right_of_le_three hk,
    zero_add, add_zero, dot_comm k (associator a b d) c] at h
  exact h

end LevelThree

section Field

variable {K : Type u} [Field K] [StarRing K] [TrivialStar K] {k : ℕ}

/-- The inverse of `x` by its trace norm, `(dot x x)⁻¹ • star x`; a two-sided inverse of `x` at
every level when `dot x x ≠ 0`. -/
def normInv (x : Tower K k) : Tower K k := (dot k x x)⁻¹ • star x

/-- The left inverse property `x⁻¹ * (x * y) = y` at levels up to 3. -/
theorem normInv_mul_mul_of_le_three (hk : k ≤ 3) {x : Tower K k} (hx : dot k x x ≠ 0)
    (y : Tower K k) : normInv x * (x * y) = y := by
  unfold normInv
  rw [smul_mul_assoc', star_mul_mul_of_le_three hk, smul_smul, inv_mul_cancel₀ hx, one_smul]

/-- The right inverse property `(y * x) * x⁻¹ = y` at levels up to 3. -/
theorem mul_mul_normInv_of_le_three (hk : k ≤ 3) {x : Tower K k} (hx : dot k x x ≠ 0)
    (y : Tower K k) : y * x * normInv x = y := by
  unfold normInv
  rw [mul_smul_comm', mul_mul_star_of_le_three hk, smul_smul, inv_mul_cancel₀ hx, one_smul]

/-- The inverse of a product reverses the factors at levels up to 3: `(a b)⁻¹ = b⁻¹ a⁻¹`. -/
theorem normInv_mul_of_le_three (hk : k ≤ 3) (a b : Tower K k) :
    normInv (a * b) = normInv b * normInv a := by
  unfold normInv
  rw [dot_mul_self_of_le_three hk, star_mul, smul_mul_assoc', mul_smul_comm', smul_smul,
    mul_inv, mul_comm]

end Field

section Failure

variable {R : Type u} [NonAssocRing R] [StarRing R]

theorem lift_zsmul (j m : ℕ) (n : ℤ) (x : Tower R j) : lift j m (n • x) = n • lift j m x := by
  induction m with
  | zero => rfl
  | succ m ih =>
    change mk (lift j m (n • x)) 0 = n • mk (lift j m x) 0
    rw [ih]
    exact mk_inj.2 ⟨rfl, (smul_zero n).symm⟩

theorem lift_innerDer (j m : ℕ) (a b x : Tower R j) :
    lift j m (innerDer a b x) = innerDer (lift j m a) (lift j m b) (lift j m x) := by
  simp only [innerDer, commutator, lift_sub, lift_mul, lift_zsmul, lift_associator]

/-- A nonzero integer multiple of a basis element is nonzero. -/
theorem zsmul_e_ne_zero {n : ℤ} (hn : (n : R) ≠ 0) :
    ∀ (k : ℕ) (p : BitVec k), n • e R k p ≠ 0
  | 0, p => by
    intro h
    apply hn
    have h' : n • (1 : R) = 0 := h
    simpa using h'
  | k + 1, p => by
    intro h
    by_cases hp : p.msb
    · rw [e_succ_of_msb hp] at h
      have h' : mk (n • (0 : Tower R k)) (n • e R k (p.setWidth k)) = mk 0 0 := h
      exact zsmul_e_ne_zero hn k _ (mk_inj.1 h').2
    · rw [e_succ_of_not_msb (by simpa using hp)] at h
      have h' : mk (n • e R k (p.setWidth k)) (n • (0 : Tower R k)) = mk 0 0 := h
      exact zsmul_e_ne_zero hn k _ (mk_inj.1 h').1

/-- Two integer multiples of one basis element differ when the difference is nonzero in `R`. -/
theorem zsmul_e_ne_zsmul_e {n m d : ℤ} (hd : n - m = d) (hR : (d : R) ≠ 0) (k : ℕ)
    (p : BitVec k) : n • e R k p ≠ m • e R k p := fun h =>
  zsmul_e_ne_zero hR k p (by rw [← hd, sub_smul, h, sub_self])

/-- The commutator of two basis elements. -/
theorem commutator_e_e (k : ℕ) (p q : BitVec k) :
    commutator (e R k p) (e R k q) = (sign k p q - sign k q p) • e R k (p ^^^ q) := by
  unfold commutator
  rw [e_mul_e_sign, e_mul_e_sign, BitVec.xor_comm q p, sub_smul]

/-- The integer coefficient of the double commutator of three basis elements. -/
def ccCoeff (k : ℕ) (p q r : BitVec k) : ℤ :=
  (sign k p q - sign k q p) * (sign k (p ^^^ q) r - sign k r (p ^^^ q))

theorem commutator_commutator_e_e_e (k : ℕ) (p q r : BitVec k) :
    commutator (commutator (e R k p) (e R k q)) (e R k r) =
      ccCoeff k p q r • e R k (p ^^^ q ^^^ r) := by
  rw [commutator_e_e, commutator_zsmul_left, commutator_e_e, smul_smul, ccCoeff]

/-- The inner derivation of three basis elements. -/
theorem innerDer_e_e_e (k : ℕ) (p q r : BitVec k) :
    innerDer (e R k p) (e R k q) (e R k r) =
      (ccCoeff k p q r - 3 * basisAssocCoeff k p q r) • e R k (p ^^^ q ^^^ r) := by
  unfold innerDer
  rw [commutator_commutator_e_e_e, associator_e_e_e, smul_smul, sub_smul]

/-- At every level `k ≥ 4`, over a ring with `2 ≠ 0`, the cyclic sum of the associator is not
three times the associator. -/
theorem exists_associator_cyclic_sum_ne (h2 : (2 : R) ≠ 0) (k : ℕ) (hk : 4 ≤ k) :
    ∃ x y z : Tower R k, associator x y z + associator y z x + associator z x y ≠
      associator x y z + associator x y z + associator x y z := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le hk
  refine ⟨lift 4 m (e R 4 1#4), lift 4 m (e R 4 2#4), lift 4 m (e R 4 12#4), ?_⟩
  simp only [← lift_associator, ← lift_add]
  intro h
  have h4 := lift_injective 4 m h
  simp only [associator_e_e_e, BitVec.reduceXOr, ← add_smul] at h4
  exact zsmul_e_ne_zsmul_e (d := 2) (by decide) (by simpa using h2) 4 15#4 h4

/-- At every level `k ≥ 4`, over a ring in which `4 ≠ 0`, the cyclic sum of the double
commutators is not six times the associator. -/
theorem exists_commutator_cyclic_sum_ne (h4 : (4 : R) ≠ 0) (k : ℕ) (hk : 4 ≤ k) :
    ∃ x y z : Tower R k, commutator (commutator x y) z + commutator (commutator y z) x +
        commutator (commutator z x) y ≠ (6 : ℤ) • associator x y z := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le hk
  refine ⟨lift 4 m (e R 4 1#4), lift 4 m (e R 4 2#4), lift 4 m (e R 4 12#4), ?_⟩
  rw [commutator_commutator_cyclic_sum]
  simp only [← lift_associator, ← lift_add, ← lift_sub, ← lift_zsmul]
  intro h
  have h5 := lift_injective 4 m h
  simp only [associator_e_e_e, BitVec.reduceXOr, ← add_smul, ← sub_smul, smul_smul] at h5
  exact zsmul_e_ne_zsmul_e (d := 4) (by decide) (by simpa using h4) 4 15#4 h5

/-- At every level `k ≥ 4`, over a ring with `2 ≠ 0`, the inner derivation violates the Leibniz
rule: `D(e 1, e 8)(e 2 * e 4) - D(e 1, e 8)(e 2) * e 4 - e 2 * D(e 1, e 8)(e 4) = 2 e 15`. -/
theorem exists_innerDer_leibniz_ne (h2 : (2 : R) ≠ 0) (k : ℕ) (hk : 4 ≤ k) :
    ∃ a b x y : Tower R k, innerDer a b (x * y) ≠ innerDer a b x * y + x * innerDer a b y := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le hk
  refine ⟨lift 4 m (e R 4 1#4), lift 4 m (e R 4 8#4), lift 4 m (e R 4 2#4),
    lift 4 m (e R 4 4#4), ?_⟩
  simp only [← lift_mul, ← lift_innerDer, ← lift_add]
  intro h
  have h5 := lift_injective 4 m h
  simp only [e_mul_e_sign, innerDer_zsmul_right, innerDer_e_e_e, smul_mul_assoc, mul_smul_comm,
    smul_smul, BitVec.reduceXOr, ← add_smul] at h5
  exact zsmul_e_ne_zsmul_e (d := 2) (by decide) (by simpa using h2) 4 15#4 h5

theorem lift_innerDerSum (j m : ℕ) (a b x : Tower R j) :
    lift j m (innerDerSum a b x) = innerDerSum (lift j m a) (lift j m b) (lift j m x) := by
  simp only [innerDerSum, commutator, lift_sub, lift_mul, lift_add]

theorem innerDerSum_e_e_e (k : ℕ) (p q r : BitVec k) :
    innerDerSum (e R k p) (e R k q) (e R k r) = ccCoeff k p q r • e R k (p ^^^ q ^^^ r) +
      ccCoeff k p r q • e R k (p ^^^ r ^^^ q) + ccCoeff k r q p • e R k (r ^^^ q ^^^ p) := by
  unfold innerDerSum
  rw [commutator_commutator_e_e_e, commutator_commutator_e_e_e, commutator_commutator_e_e_e]

/-- At every level `k ≥ 4`, over a ring in which `4 ≠ 0`, the sum of three double commutators
violates the Leibniz rule: the defect at `(e 1, e 2, e 4, e 8)` is `-4 e 15`. -/
theorem exists_innerDerSum_leibniz_ne (h4 : (4 : R) ≠ 0) (k : ℕ) (hk : 4 ≤ k) :
    ∃ a b x y : Tower R k,
      innerDerSum a b (x * y) ≠ innerDerSum a b x * y + x * innerDerSum a b y := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le hk
  refine ⟨lift 4 m (e R 4 1#4), lift 4 m (e R 4 2#4), lift 4 m (e R 4 4#4),
    lift 4 m (e R 4 8#4), ?_⟩
  simp only [← lift_mul, ← lift_innerDerSum, ← lift_add]
  intro h
  have h5 := lift_injective 4 m h
  simp only [e_mul_e_sign, innerDerSum_zsmul_right, innerDerSum_e_e_e, smul_mul_assoc,
    mul_smul_comm, smul_smul, BitVec.reduceXOr, ← add_smul] at h5
  exact zsmul_e_ne_zsmul_e (d := -4) (by decide) (by simpa using h4) 4 15#4 h5

end Failure

section FailureDot

variable {R : Type u} [CommRing R] [StarRing R] [TrivialStar R]

omit [TrivialStar R] in
/-- The embedding `lift` preserves the trace form. -/
theorem dot_lift (j m : ℕ) (x y : Tower R j) :
    dot (j + m) (lift j m x) (lift j m y) = dot j x y := by
  induction m with
  | zero => rfl
  | succ m ih =>
    change dot (j + m + 1) (mk (lift j m x) 0) (mk (lift j m y) 0) = dot j x y
    rw [dot_mk, ih, dot_zero_left, add_zero]

omit [TrivialStar R] in
theorem dot_zsmul_left (k : ℕ) (n : ℤ) (x y : Tower R k) : dot k (n • x) y = n * dot k x y := by
  rw [← Int.cast_smul_eq_zsmul R n x, dot_smul_left]

/-- At every level `k ≥ 4`, over a ring with `2 ≠ 0`, the left inverse property
`star x * (x * y) = dot x x • y` fails. -/
theorem exists_star_mul_mul_ne (h2 : (2 : R) ≠ 0) (k : ℕ) (hk : 4 ≤ k) :
    ∃ x y : Tower R k, star x * (x * y) ≠ dot k x x • y := by
  obtain ⟨x, y, h⟩ := exists_left_alternative_ne h2 k hk
  refine ⟨x, y, fun h' => h ?_⟩
  have h5 := star_mul_mul_sub_eq x y
  rw [h', sub_self] at h5
  exact sub_eq_zero.1 h5.symm

omit [TrivialStar R] in
/-- At every level `k ≥ 4`, over a ring with `2 ≠ 0`, the map `c ↦ A(a, b, c)` is not
skew-symmetric for the trace form: with `A(e 1, e 10, e 4) = 2 e 15` and
`A(e 1, e 10, e 15) = 0`. -/
theorem exists_dot_associator_skew_ne (h2 : (2 : R) ≠ 0) (k : ℕ) (hk : 4 ≤ k) :
    ∃ a b c d : Tower R k,
      dot k (associator a b c) d + dot k c (associator a b d) ≠ 0 := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le hk
  refine ⟨lift 4 m (e R 4 1#4), lift 4 m (e R 4 10#4), lift 4 m (e R 4 4#4),
    lift 4 m (e R 4 15#4), ?_⟩
  simp only [← lift_associator, dot_lift]
  rw [associator_e_e_e, associator_e_e_e]
  have h1 : basisAssocCoeff 4 1#4 10#4 4#4 = 2 := by decide
  have h3 : basisAssocCoeff 4 1#4 10#4 15#4 = 0 := by decide
  simp only [h1, h3, BitVec.reduceXOr, dot_zsmul_left, dot_e_e, zero_smul, dot_zero_right]
  simpa using h2

end FailureDot

end Tower

end CayleyDickson
