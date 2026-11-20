# gororoba-math

Machine-checked mathematics of the gororoba workspace: the statements that
[gororoba-quantum](https://github.com/Oichkatzelesfrettschen/gororoba-quantum)
and [gororoba-open](https://github.com/Oichkatzelesfrettschen/gororoba-open)
rest on, each compiled by a proof assistant and audited for the axioms it
uses.

## Lean library

`lean/` is a Lake package, `GororobaMath`, over Mathlib.

| Module | Result | Reads on |
|---|---|---|
| `GororobaMath.CayleyDickson.Basic` | the Cayley-Dickson double of a nonassociative ring with a star is again one (`instNonAssocRing`, `instStarRing`); `x * star x` lies in the first half (`mul_star_self`); the reflection `(a, b) -> (a, -b)` and the embedding `a -> (a, 0)` preserve products | the doubling `(a, b)(c, d) = (ac - conj(d) b, da + b conj(c))` of `gororoba_quantum/cd_core.py` |
| `GororobaMath.CayleyDickson.Tower` | at every level `k` and over every such ring, `e_p * e_q = sign(p, q) e_(p xor q)` (`Tower.e_mul_e`, `Tower.e_mul_e_sign`), conjugation negates every basis element but `1` (`Tower.star_e`), each of those squares to `-1` (`Tower.e_mul_self`) and two distinct ones anticommute (`Tower.e_mul_e_anticomm`); the sign of `e_p * e_(p xor q)` is that of `e_p * e_q`, reversed for `p != 0` (`Tower.negSign_xor_right`); `Pathion R` is level 5, the 32-dimensional algebra `A_5` | `cd_core.cd_sign`, by the comparison below |
| `GororobaMath.CayleyDickson.TwoTerm` | an aligned pair `{x, x xor i xor j}` gives the zero product `(e_i + e_j)(e_x +- e_x') = 0` at every level over every ring (`Tower.two_term_mul_add_eq_zero`, `Tower.two_term_mul_sub_eq_zero`); `partner` is an involution without a fixed point for `i != j` and alignment is a property of the pair; the aligned-pair counts of the measured operands, evaluated in the kernel: 12 for `e_1 + e_18` and `e_1 + e_24`, 4 for `e_1 + e_26` and `e_2 + e_27`, 0 for `e_1 + e_17` in `A_5`, 4 for `e_1 + e_10` in the sedenions | the nullity reading of gororoba-quantum's `docs/evidence/pathion-kernel-map/README.md`; `TwoTermNullity` proves that the count is the nullity |
| `GororobaMath.CayleyDickson.TowerModule` | every level of the tower over a commutative star ring `R` is an `R`-module with the basis `e_p`, of rank `2^k` (`Tower.basis`, `Tower.finrank_eq`); over a ring with the identity as star, left multiplication is `R`-linear (`Tower.mulLeft`) and acts on coordinates as a signed permutation (`Tower.repr_e_mul`) | the coordinates in which gororoba-quantum's `pathion_kernel_map.py` writes the operator |
| `GororobaMath.CayleyDickson.TwoTermNullity` | over a nontrivial commutative ring with the identity as star in which `2` is a non-zero-divisor, the kernel of left multiplication by `e_i + e_j` is a free module of rank `alignedPairCount k i j` (`Tower.free_ker_mulLeft_e_add_e`, `Tower.finrank_ker_mulLeft_e_add_e`), and the same for `e_i - e_j` with `i != j`; 12 for `e_1 + e_18` in `A_5` over the rationals and over the integers | the nullity that the hardware estimator of `KernelMap.Estimator` targets; `KernelMap.TwoTermBins` links `KernelMap.nullity` to this count |
| `GororobaMath.CayleyDickson.TwoTermRecursion` | the recursion of `alignedPairCount` on the top index bit, with low parts `a`, `b` of `i`, `j`: twice the level-`k` count of `a`, `b` for `i` and `j` in the same half (`Tower.alignedPairCount_succ_of_msb_eq`), `0` for different halves with `a = 0`, `b = 0` or `a = b` (`Tower.alignedPairCount_succ_eq_zero`), and `N(k+1, i, j) + 2 N(k, a, b) + 4 = 2^k` for different halves otherwise (`Tower.alignedPairCount_succ_add`); hence no aligned pair at levels `k <= 3` or for an operand with the term `e_0` or the unit the last doubling adjoins (index `2^(k-1)` at level `k`), every count a multiple of 4, and a nonzero count at level `k` at most `2^(k-1) - 4` | the counts of the measured operands in `TwoTerm`; over the reals, the same-half case is Theorem 10.1 of Biss, Dugger and Isaksen (arXiv:math/0511691) on sums of two basis vectors; the mixed case matches their Proposition 11.1 and Lemmas 8.7 and 8.8 under the associator-dimension identity that `AssociatorSpace` proves |
| `GororobaMath.CayleyDickson.AlignedPairSpectrum` | for `k >= 3` every count satisfies `N + 4 <= 2^(k-1)` (`Tower.alignedPairCount_add_four_le_of_three_le`), every multiple `4v` with `4v + 4 <= 2^(k-1)` is the count of a pair of nonzero distinct indices (`Tower.exists_alignedPairCount_eq`), and the counts are exactly those multiples (`Tower.range_alignedPairCount`); flipping the top bit of `j` sends a nonzero count `n` to `2^(k-1) - 4 - n` (`Tower.alignedPairCount_add_flip`), so as many ordered pairs have count `n` as have count `2^(k-1) - 4 - n` (`Tower.multiplicity_mirror`) | the spectrum and multiplicities of the two-term nullities |
| `GororobaMath.CayleyDickson.AlignedPairClosedForm` | `N(k, i, j) = 4 * sum over t in [3, k) of 2^(k-1-t) * parity(m' >> t)`, with `m'` the exclusive or of the indices with every bit at or below the highest degenerate split cleared (`Tower.alignedPairCount_eq_closedForm`) | the closed form computed for issue 15 |
| `GororobaMath.CayleyDickson.AssociatorSpace` | the associator space `{x : (a x) b = a (x b)}` as a kernel (`Tower.assocSpace`); for nonzero distinct basis indices it is free (`Tower.free_assocSpace_e`) of rank `2 N(k, a, b) + 4` over every nontrivial commutative ring with the identity as star in which `2` is a non-zero-divisor (`Tower.finrank_assocSpace_e`) | Lemmas 8.7 and 8.8 of Biss, Dugger and Isaksen read on basis vectors |
| `GororobaMath.CayleyDickson.AnnihilatorSymmetry` | over a commutative ring with the identity as star, no zero divisors, a partial order compatible with addition and nonnegative squares (every ordered field, `ℤ`), at every level `k`: `a z = 0` exactly when `z a = 0` (`Tower.mul_eq_zero_iff_rev`), the nonzero factors of a product that vanishes have zero real part (`Tower.re_eq_zero_of_mul_eq_zero`), and `a b = 1` forces `b a = 1` (`Tower.mul_eq_one_rev`) | Corollary 9.3 and Lemma 9.4 of Biss, Dugger and Isaksen (arXiv:math/0511691); the Rocq form over an abstract ordered domain is `kernel_equality`, `purity_left` and `direct_finiteness` of `rocq/quantum/CdTowerDomain.v` |
| `GororobaMath.CayleyDickson.NonAssociative` | the embedding `x -> (x, 0)` of level `k` into level `k + 1` preserves products (`Tower.mk_zero_mul_mk_zero`); over every ring with a star in which `2 != 0`, no basis element equals its negative (`Tower.e_ne_neg_e`), `(e_1 e_2) e_4 = e_7` and `e_1 (e_2 e_4) = -e_7` in the octonions (`Tower.octonion_e1_e2_e4_mul_assoc_ne`), and every level `k >= 3` has a triple with `(a b) c != a (b c)` (`Tower.exists_mul_assoc_ne`), dimension 128 included (`Tower.exists_mul_assoc_ne_level_seven`) | the claim of a nonempty associator violation set at every dimension from 8 on, which `rocq/open/verified/C956_RoutonAVT.v` states and `ci/census/header-verdicts.tsv` marks as overclaimed; one violating triple per level, no count; the Rocq bridge over a commutative coefficient ring is the functor `NonAssociative` of `rocq/quantum/CdTowerNonAssociative.v` |
| `GororobaMath.KernelMap.Estimator` | the bias identity of the hardware nullity estimator, `N_hat - N = \|B+\|\|B-\|/\|B\| (Vbar+ - Vbar-)/V_hat` for every observed contrast with `V_hat` nonzero (`nHat_sub_nullity`), and the forced reading `N_hat = \|B\|/2` of a block with no bin of ideal contrast `-1` (`nHat_eq_card_div_two_of_negBins_eq_empty`) | `docs/evidence/pathion-kernel-map/nhat-bias/README.md` in gororoba-quantum, claims 1 and 3 |
| `GororobaMath.KernelMap.TwoTermBins` | a labelling of the `2^k` bins in which every index of an aligned pair is a `+1` bin and every misaligned pair holds one bin of each sign has `KernelMap.nullity = alignedPairCount k i j` (`KernelMap.nullity_eq_alignedPairCount`), and the same from the Boolean contract `KernelMap.binContract` (`KernelMap.nullity_eq_alignedPairCount_of_binContract`) | the ideal output contrast of `pathion_kernel_map.kernel_map_circuit`, by the comparison below |
| `GororobaMath.CayleyDickson.RingLaws` | over a nonassociative ring with a star, at every level k: `a * z = 0` exactly when `star z * star a = 0` (`Tower.mul_eq_zero_iff_star_mul_star`); for a pure a (`star a = -a`), `a * z = 0` exactly when `star z * a = 0` (`Tower.mul_eq_zero_iff_star_mul_of_star_eq_neg`) and `v * a = 0` exactly when `a * star v = 0` (`Tower.mul_eq_zero_iff_mul_star_of_star_eq_neg`), and `(a, 0)(c, d) = 0` exactly when `a * c = 0` and `a * star d = 0` (`Tower.mk_mul_mk_eq_zero_iff_of_star_eq_neg`); the reflection `(a, b) -> (a, -b)` carries the annihilator of an element onto that of its image (`Tower.mul_eq_zero_iff_reflect_mul_reflect`) | `RingTower` of `rocq/quantum/CdTowerRing.v` and `rocq/open/theories/CDPureDoublingKernel.v` |
| `GororobaMath.CayleyDickson.TraceForm` | over a commutative ring with the identity as star, at every level k, with the trace form: `re (x * y) = re (y * x)` and `re ((x * y) * z) = re (x * (y * z))` (`Tower.re_mul_comm`, `Tower.re_mul_assoc`); `x * (star x * y) = star x * (x * y)` and its mirror (`Tower.mul_star_mul_left`, `Tower.mul_mul_star_right`); the flexible law `(x * y) * x = x * (y * x)` when `2` is left regular (`Tower.mul_mul_self_eq`); in characteristic 2 every level is commutative (`Tower.mul_comm_of_two_eq_zero`); left and right multiplication by a pure element is skew for the trace form (`Tower.dot_mul_left_of_star_eq_neg`, `Tower.dot_mul_right_of_star_eq_neg`); over an ordered ring with nonnegative squares and no zero divisors, `x * y = 0`, `star x * y = 0` and `x * star y = 0` are equivalent (`Tower.mul_eq_zero_iff_star_mul_eq_zero`), nonzero factors of a vanishing product have zero real part (`Tower.re_eq_zero_of_mul_eq_zero_rev`), and a zero divisor and the annihilator of a nonzero element are orthogonal to `1` and to the adjoined unit (`Tower.dot_one_eq_zero_and_dot_mk_zero_one_of_mul_eq_zero`, `Tower.dot_one_eq_zero_and_dot_mk_zero_one_of_mul_eq_zero_right`); from `a * b = 1`, `a * ((dot a a) * b - star a) = 0` (`Tower.mul_dot_smul_sub_star_eq_zero`), and over an ordered field b is `(dot a a)⁻¹ • star a` plus an element of the left kernel of a (`Tower.exists_eq_inv_dot_smul_star_add`) | `CdTower` of `rocq/quantum/CdTowerDomain.v`, `RingTower` of `rocq/quantum/CdTowerRing.v` and `rocq/open/theories/C1539_MorSkewSymm.v`; Lemmas 2.6, 2.8, 9.2 and 9.5 of Biss, Dugger and Isaksen |
| `GororobaMath.CayleyDickson.Map` | a non-unital ring homomorphism between two star rings that commutes with the star extends to the doubles, `CayleyDickson.map` applying it to both halves, and the extension preserves products (`CayleyDickson.map_mul`); the iterated embedding `Tower.lift` of level j into level `j + k` preserves products (`Tower.lift_mul`) and is injective (`Tower.lift_injective`) | `RingTower` of `rocq/quantum/CdTowerRing.v` (`diag_mul`, `lift_mul`, `lift_injective`) |
| `GororobaMath.CayleyDickson.RingTowerI` | over a commutative ring with the identity as star and a square root i of `-1`, at every level `k + 2`, every product that vanishes has a vanishing reverse product exactly when `2 = 0` (`Tower.kernel_swap_iff_two_eq_zero`), and the same holds for pure left factors only if `2 = 0` (`Tower.pure_kernel_swap_two_eq_zero`) | `RingTowerI` of `rocq/quantum/CdTowerRing.v` |
| `GororobaMath.CayleyDickson.BasisExt` | over a commutative ring with the identity as star, a linear map of `Tower R k` that is multiplicative on the basis elements is multiplicative (`Tower.map_mul_of_map_e_mul_e`), and one that satisfies the Leibniz rule on them satisfies it on every pair (`Tower.leibniz_of_leibniz_e`) | `RingTowerBasis` of `rocq/quantum/CdTowerRingBasis.v` |
| `GororobaMath.CayleyDickson.BaseChange` | a linear map of a tower over a commutative ring extends along a ring homomorphism to the tower over the target by its values on the basis; the scaled multiplicative property on the basis, `F (e_i) * F (e_j) = c • F (e_i * e_j)`, transfers to every pair of the target (`Tower.baseChange_mul`), and the Leibniz rule transfers (`Tower.baseChange_leibniz`) | `BaseChange` of `rocq/quantum/CdTowerRingBaseChange.v` |
| `GororobaMath.CayleyDickson.OrderThree` | over a commutative ring with an element of square `3`, the map `Tower.orderThree` (twice the order-three map of Gresnigt) of level `4` satisfies `orderThree x * orderThree y = 2 • orderThree (x * y)` (`Tower.orderThree_mul`), and it commutes with the star at every level (`Tower.orderThree_star`) | `OrderThreeMap` of `rocq/quantum/CdTowerOrderThreeMap.v` and `ci/compare_order_three.sh` |
| `GororobaMath.CayleyDickson.ImaginarySum` | over a commutative ring with the identity as star, at every level k, the sum `Tower.isum` of the imaginary basis elements satisfies `isum * (isum * x) = -(2 ^ k - 1) • x`, `x * isum * isum = -(2 ^ k - 1) • x` and `isum * (x * isum) = isum * x * isum` (`Tower.isum_laws`); left and right multiplication by it is skew for the trace form (`Tower.dot_isum_mul`); right multiplication scales the trace form by `2 ^ k - 1` (`Tower.dot_mul_isum_mul_isum`), the map `x + x * isum` by `2 ^ k` (`Tower.dot_add_mul_isum`), and `α • x + β • (x * isum)` by `α * α + (2 ^ k - 1) * (β * β)` (`Tower.dot_smul_add_smul_mul_isum`); the coordinate of `e_a * isum` at `a xor b` is the sign of `e_a * e_b` (`Tower.repr_e_mul_isum`) | `rocq/quantum/CdImaginarySumConference.v`, `rocq/quantum/CdTowerBasisSign.v` and `ci/compare_isum.sh` |
| `GororobaMath.CayleyDickson.HalfFold` | over an ordered commutative ring with nonnegative squares and no zero divisors, `(a, 0)(c, d) = 0` exactly when `a * c = 0` and `a * d = 0` (`Tower.mk_left_mul_eq_zero_iff`), and `(0, b)(c, d) = 0` exactly when `b * c = 0` and `b * d = 0` (`Tower.mk_right_mul_eq_zero_iff`); over an ordered field the left kernels of `(a, 0)` and `(0, b)` have twice the dimension of those of a and b (`Tower.finrank_ker_mulLeft_mk_left`, `Tower.finrank_ker_mulLeft_mk_right`); for a pure a over every field with the identity as star the same doubling holds (`Tower.finrank_ker_mulLeft_mk_left_of_star_eq_neg`) and right multiplication has the rank of left multiplication (`Tower.finrank_range_mulRight_of_star_eq_neg`) | `HalfFold` of `rocq/quantum/CdHalfFold.v` and `rocq/open/theories/CDPureDoublingKernel.v` |
| `GororobaMath.CayleyDickson.Fold` | over a field in which `2` is nonzero and the star is the identity, the fold `(a, b) -> ((a + b) / 2, (a - b) / 2)` of level `k + 1` scales the trace form of an element with itself by `1 / 2` (`Tower.dot_fold_self`) | `rocq/open/theories/CDTowerFoldTransport.v` |
| `GororobaMath.CayleyDickson.ZeroDivisors` | over a nontrivial ordered commutative ring with nonnegative squares and no zero divisors, at every level `k >= 4` some pair of elements violates the multiplicativity of the trace form, `dot (x * y) (x * y) != dot x x * dot y y` (`Tower.exists_dot_mul_self_ne`) | `rocq/open/verified/C957_VoudonZD.v` |
| `GororobaMath.CayleyDickson.SignLaws` | at every level k, for `b != 0`, the signs of `e_a * e_b` and `e_(a xor b) * e_b` multiply to `-1` (`Tower.negSign_xor_left_right`), and the exponent of Albuquerque and Majid, defined by the recursion on the top bits, is the sign exponent of the swapped pair (`Tower.amExponent_eq`) | `rocq/quantum/CdTowerBasisSign.v` and `ci/compare_am_exponent.sh` |
| `GororobaMath.CayleyDickson.BooleanAnf` | for a Boolean function on k bits, the coefficient transform inverts the evaluation transform of the algebraic normal form (`Tower.anfEval_anfCoeff`) and the coefficients are unique (`Tower.anfCoeff_unique`); the indicator of two distinct points has degree `k - 1` (`Tower.anfDegree_two_point`); the sign row of a nonzero index at level `k >= 2` has degree `k - 1` (`Tower.anfDegree_negSign_left`), and the sign column of m has degree `1` for a power of two and `max 1 (Nat.log2 m.toNat - 1)` otherwise (`Tower.anfDegree_negSign_right`) | `rocq/quantum/CdSignRowAnf.v`, `rocq/open/theories/BooleanANFDegree.v`, `rocq/open/theories/CDPhaseDegree.v` and `ci/compare_anf.sh` |
| `GororobaMath.CayleyDickson.AssociatorPhase` | for basis elements over every nonassociative ring with a star, `e_p * (e_q * e_x)` is `-((e_p * e_q) * e_x)` exactly when the associator phase is set (`Tower.e_mul_e_mul_e`); the phase vanishes for dependent triples (`Tower.assocPhase_eq_false_of_dependent`), for a zero or repeated pair (`Tower.assocPhase_eq_false_of_degenerate`) and at level 2 (`Tower.assocPhase_two`); it doubles in the top bits of its arguments (`Tower.assocPhase_cons`), and the pair coefficient of two independent nonzero indices is true (`Tower.pairCoeff_eq_true`); for `k >= 3` and distinct nonzero p, q its degree is `max 1 (Nat.log2 (max p.toNat q.toNat) - 1)` (`Tower.anfDegree_assocPhase`), and it has a closed form on the point-indicator pairs (`Tower.assocPhase_point_pair`) | `rocq/quantum/CdAssociatorAnf.v`, `rocq/open/theories/CDAssociatorDoubling.v`, `rocq/open/theories/CDPhaseDegree.v` and `ci/compare_assoc_phase.sh` |
| `GororobaMath.CayleyDickson.AssociatorCensus` | for `k >= 3`, the ordered pairs `0 < p < q` of indices whose associator phase has degree d number `3 * 2 ^ d * (2 ^ (d + 1) - 1)` for `2 <= d <= k - 2` (`Tower.card_anfDegree_assocPhase_eq`) and `21` for `d = 1` (`Tower.card_anfDegree_assocPhase_eq_one`), and twice the sum of the counts over all degrees is `(2 ^ k - 1) * (2 ^ k - 2)` (`Tower.sum_card_anfDegree_assocPhase`); twice the number of triples with the phase set at level `k + 1` is `(2 ^ (k + 1) - 2) * (2 ^ (k + 1) - 4) * (2 ^ (k + 1) + 6)` (`Tower.card_assocPhase_true`) | `rocq/quantum/CdAssociatorCensus.v` and `rocq/open/theories/CDAssociatorCensus.v` |
| `GororobaMath.CayleyDickson.SignCode` | the span over `ZMod 2` of the Schreier sign cocycles at level `k + 3` is the set of functions `g (setWidth x) + c * msb x` with g of zero sum (`Tower.mem_signSpan_iff`); its elements that vanish at index `0` number `2 ^ (2 ^ (k + 2) - 1)` (`Tower.card_normalizedSignSpan`); the sign cocycle differs from its value at `0` by an ordinary coboundary of the tower sign (`Tower.schreier_xor_schreier_zero`) | `rocq/open/theories/SchreierSignCode.v`, `rocq/open/theories/SignCodeCardinality.v`, `rocq/open/theories/BooleanCochainFiltration.v` and `ci/compare_schreier.sh` |
| `GororobaMath.CayleyDickson.SparseSupport` | over a commutative ring with the identity as star, at every level, if the coordinates of one factor lie in a coset of a subset of indices closed under the exclusive or and those of the other lie in a second coset, then those of the product lie in the coset of the sum (`Tower.repr_mul_ne_zero_mem`), and the kernel of left multiplication by the first factor splits over the sectors (`Tower.mul_eq_zero_iff_forall_sector`) | `rocq/open/theories/CDSparseBlockTransport.v` and `rocq/open/theories/CDSparseMatrixTransport.v` |
| `GororobaMath.CayleyDickson.KernelCertificate` | over a commutative ring with the identity as star, vectors in the kernel of left multiplication by an element, with dual functionals and a unit d such that `d • z = back (y * z) + ∑ g_j z • v_j` for every z, form a basis of that kernel (`Tower.ker_mulLeft_basis_of_certificate`) | `KernelCertificate` of `rocq/quantum/CdTowerKernelCertificate.v` |

`lean/Challenge/` holds the challenge modules of the headline theorems of
`CayleyDickson.Basic`, `Tower`, `TwoTerm`, `TowerModule`, `TwoTermNullity`, `TwoTermRecursion`, `AlignedPairSpectrum`, `AlignedPairClosedForm`, `AnnihilatorSymmetry`, `AssociatorSpace`, `NonAssociative`, `KernelMap.Estimator`, `KernelMap.TwoTermBins`, `RingLaws`, `TraceForm`, `Map`, `RingTowerI`, `BasisExt`, `BaseChange`, `OrderThree`, `ImaginarySum`, `HalfFold`, `Fold`, `ZeroDivisors`, `SignLaws`, `BooleanAnf`, `AssociatorPhase`, `AssociatorCensus`, `SignCode`, `SparseSupport` and `KernelCertificate`, one per solution module. `Challenge.NAME` restates
the theorems the table names with `sorry` as each proof, together with the
definitions the solution module introduces and those statements use, and
imports the library modules the solution imports. `NAME.json` beside it names
the challenge module, the solution module, the theorems and the permitted
axioms (`propext`, `Quot.sound`, `Classical.choice`). From `lean/`, with
`bubblewrap` installed, `lake comparator --config Challenge/NAME.json`
checks that each named theorem of the solution has that statement and those
axioms. No library module imports `Challenge` and the admission gate does
not build it. The challenge modules of `Basic`, `Tower`, `TowerModule`, `TwoTerm` and
`Estimator` declare constants that the library modules above them in the import chain also declare, so
`lake build Challenge` builds the modules one at a time (the `Challenge.*` glob) and no single file
imports them all. A challenge module whose solution imports a library module that another challenge module restates (`AnnihilatorSymmetry`, `AssociatorSpace`, `Map`) stays out of `lean/Challenge.lean` for the same reason.
`ci/headline-results.tsv` lists the theorems this table names as the
headline results, each with its Rocq partner (every row has one since
[issue 46](https://github.com/Oichkatzelesfrettschen/gororoba-math/issues/46));
a new row lands with its partner.

The tower theorems hold for every level and every coefficient ring, so they
cover the 64- and 128-dimensional runs as well as `A_5`. The estimator
theorems hold over every field of characteristic zero.

## Rocq trees

`rocq/delegation` holds four sources under the logical root
`GororobaDelegation`; `rocq/delegation/README.md` describes them. `Model.v`
defines three semantics of delegation of rights between named subjects
(`reachable_delegation`, the closure under a `Grant` step;
`restricted_delegation`, where a step conveys only actions that satisfy a
predicate; `single_delegation`, where a step conveys only held rights) and,
for the chain of `n` threads with an arena every `p` threads, proves the
reachable set under each for every `n` and `p` (`chain_reachable_iff`,
`chain_restricted_iff`, `chain_single_iff`). `Inventory512.v`,
`Inventory1024.v` and `Inventory2048.v` are rendered by
`ci/delegation-sources/render_inventory.py` from the statement inventories
`confine_theorems_N.v` that gororoba-open keeps under
`curated/01_theory_frameworks/` (2,590, 5,182 and 10,366 statements, there
without proofs and over two undefined parameters): each holds every
statement of its inventory with its proof, pairs each right with the
theorem about it, and proves that
the rights the statements name are the table of the chain of that size with
period 16 (`inventory_is_chain_table`). The tree declares no axiom and its
ledger is empty.

`rocq/open` is the proof tree of gororoba-open (364 sources under
`theories/` and `verified/`, with checkpoints, extraction targets and the
frozen quantum-observable evidence its bindings cite). `rocq/quantum` holds
41 sources: the 29 proof files of gororoba-quantum (the Cayley-Dickson
tower over ordered domains and commutative rings with its basis, base change,
order-three map and the kernel certificates of the canonical `A_5`
points, basis-sign and associator normal
forms, the Python-semantics certificate of `cd_sign`, the Stiefel witness
and the terminal-channel separation) and twelve that began here. The two
imported trees arrived with their history; `rocq/open/README.md` describes
that tree in the words of its origin, where it sat at `proofs/`. Nine of
the sources that began here are
`GaussianIntegerHom.v` (the homomorphism `(a, b) -> a + b i` from the
Gaussian integers to a commutative ring with a square root of -1),
`MatrixLeftInverseCertificate.v` (a matrix `L` with `L M = d I` makes the
columns of `M` independent over every ring where the image of `d` is a
nonzero divisor), `MatrixSplittingCertificate.v` (matrices with
`P M + V C = d I` make every solution of `M x = 0`, after multiplication by
the image of `d`, a combination of the columns of `V`),
`CdTowerLeibnizSystem.v` (the Leibniz rule of a linear map on the basis
units of a level of the ring tower as linear forms in its coordinates),
`CdTowerE1E18Kernel.v` (the kernel certificate of `e_1 + e_18` in `A_5`, which no
point of `CdTowerCanonicalKernels.v` is: twelve vectors, twelve functionals
and a table of 32 images with `d = 2`, free of rank 12 where 2 is invertible),
`CdTowerRealKernels.v` (the certificates of the twelve canonical points and of
`e_1 + e_18`, base-changed to the reals and carried through `TowerBridge.v`:
the kernel of left multiplication in `OpenGororoba.cd_tower 5` is free of rank
8, 12 or 16, `left_kernel_free`), and
three files generated in gororoba-quantum for the `A_5` program:
`CdTowerG2Derivations.v` (14 derivations of the sedenions
as Gaussian-integer tables, linearly independent over every ring that
receives the Gaussian integers), `CdTowerG2DerivationSpan.v` (over every
such ring, six times a linear map of the sedenions that satisfies the
Leibniz rule on the basis units is a combination of those 14, and the map
itself is one where the image of 6 is a nonzero divisor) and
`A5W8ArcMatrixRanks.v` (independent
columns of eight 24 x 6 matrices over every such ring where the scalar of
the certificate maps to a nonzero divisor).

Three sources join the two trees, which each define the Cayley-Dickson
tower recursively; `rocq/quantum/_RocqProject` reads `rocq/open/theories`
as `OpenGororoba` for them. `TowerBridge.v` maps the real tower of
`OpenGororoba.RecursiveCDTower` onto the real instance of the tower of
`CdTowerDomain`, with a two-sided inverse, and the map preserves
multiplication (`to_quantum_mul`). `SignBridge.v` proves that the sign
functions of the two trees agree at every level `k`, each under the
bound its spelling needs: the fuel-indexed function of
`rocq/open/theories` for fuel at least `k` (`open_fuel_sign_sigma`), that
of `rocq/open/verified` for fuel above `k` (`verified_fuel_sign_sigma`),
the Boolean sign law for indices below `2^k` (`open_cube_sign_sigma`),
and the Python semantics of `cd_sign` for such indices and fuel at least
`k + 7` (`python_cd_sign_returns_open_sign`). `QuantumChannelFromOpen.v`
derives `observed_means_exclude_common_binary_channel` of `rocq/quantum`,
in its rational and its real form, from the general theorem
`separated_centers_exclude_common_binary_channel` of `rocq/open`; the
other statements of the two terminal-channel files are not rederived.
A fourth source, `CdTowerRealKernels.v`, reads `TowerBridge.v` the same way: `to_quantum` is a
bijection that preserves zero, sums, scalar multiples and products, so the
kernel statements of the certificates (free of rank 8, 12 or 16 over every
commutative ring where the image of `d` is invertible) become statements
about `OpenGororoba.RecursiveCDTower.tower_mul` over the real numbers
(`NAME_open_kernel_free`, for the twelve points of
`CdTowerCanonicalKernels.v` and for `e_1 + e_18`).

## Toolchain

- Lean: the release `lean/lean-toolchain` names, installed through
  [elan](https://github.com/leanprover/elan) (`elan` reads the file and
  fetches the release on first use).
- Mathlib: the tag `lean/lakefile.toml` names, resolved to the commits of
  `lean/lake-manifest.json`.
- `shellcheck`, `ruff` and `actionlint` for the gate's lint of shell scripts,
  Python files and workflows.
- Rocq: opam with the switch `sh ci/install_rocq.sh` builds (OCaml 5.5.1,
  rocq-core 9.3.0, rocq-stdlib 9.2.0, Flocq, MathComp, Hierarchy Builder,
  Elpi, Equations, ExtLib), `make`, and `rustc` for the admission scanner.

```sh
cd lean
lake exe cache get   # prebuilt Mathlib, about 7 GB with the sources
lake build
```

With the prebuilt Mathlib present and no library object built, `lake build
GororobaMath` took 29 s and its largest process peaked at 3.0 GB of resident
memory (`/usr/bin/time -f '%es %MkB'` at commit d47b053 on a 12-thread
x86-64 workstation, Lean 4.35.0, Mathlib v4.35.0). The first `lake build`
after `lake exe cache get` took 161 s. A file that imports Mathlib outside
the module system peaks at 6.8 GB, against 3.8 GB as `module` with `public
import Mathlib`.

## Building

```sh
make lean
make rocq
```

build the files as they stand in the checkout, edits included, with GNU
make. `make lean` runs `lake build --wfail` in `lean/`, whose build tree is
`lean/.lake`. `make rocq` copies `rocq/` into `build/rocq` and compiles
`rocq/open` (`make all`), then `rocq/quantum`, and `rocq/delegation` there,
so the source directories hold no build product. `make rocq-open` builds
the first tree alone, `make rocq-quantum` the first two, since
`rocq/quantum` reads the objects of `rocq/open`, and `make rocq-delegation`
the third alone. `BUILD_DIR` names another build
directory, which lies outside the checkout (any path inside it other than
`build` is refused), `ROCQ_JOBS` the number of parallel compilations and
`ROCQ_SWITCH` the opam switch. `build`, `lean/.lake` and the compiler's
products are ignored by git. The warning options are the option lines of
each tree's `_RocqProject`. `make clean` removes a build tree that
`make rocq` created and no other directory. `make help` lists the targets.

## Checks

```sh
sh ci/check.sh
```

runs the admission gate: the shell lint, the library build with warnings as
errors, and the axiom audit. `#audit_axioms GororobaMath`
(defined in `lean/AxiomAudit.lean`) fails when any declaration of the library depends
on an axiom other than `propext`, `Classical.choice` and `Quot.sound`, which
excludes `sorry`, `native_decide` and declared axioms. The gate builds and
audits every tracked module under `lean/GororobaMath/`, taken from git's
file list, and separately requires `lean/GororobaMath.lean` to import each
one; it also requires the audit to reject `lean/AuditFixture.lean`, which
holds one of each. Last it replays every tracked module
through `leanchecker`, which type-checks the compiled theorems and
definitions again in a second process (unsafe and partial declarations
are skipped; the kernel rejects a theorem that uses one), and requires that replay to reject
`lean/ReplayFixture.lean`: a declaration of type `False` added with the
kernel switched off, which the build and the axiom audit both accept.

```sh
sh ci/check_rocq.sh
```

runs the Rocq half on an export of `HEAD` outside the checkout: every
tracked source of `rocq/open/theories`, `rocq/open/verified`,
`rocq/quantum` and `rocq/delegation` is listed in its `_RocqProject` and
compiles (364, 41 and 4 sources), `rocq/open` passes `make all check-schur-geometry check-admissions
check-plugins extract-check`, the build log of `rocq/quantum` holds no
warning, and none of the four directories holds `Admitted` or `admit`. Of
the eleven sources elsewhere under `rocq/open`, those make targets compile
seven and the script compiles `NullityTwelveCoefficientCertificate.v`;
`ExtractFP24Admit.v`, `ExtractR2VBDP4.v` and `RustExtractSpike.v` stay
uncompiled, and the script names all eleven and fails on a twelfth. Before any
build it runs the calibration of the kernel replay evidence producer (below).

The script then re-checks every project-listed module with Rocq's kernel
checker and compares the axioms it reports with a ledger in each tree.
`rocq/delegation/kernel-assumptions.txt` is empty.
`rocq/quantum/kernel-assumptions.txt` holds four axioms of the standard
library: functional extensionality, excluded middle and the two axioms of
the classical real numbers. `rocq/open/kernel-assumptions.txt` holds 135:
37 that five modules of the tree declare (`SStructuralGaps`,
`CarlsonIntegrals`, `TightBindingTopology`, `CDFidelity`,
`C958_ZDGraphTopology`), five of the standard library, and 93 primitive
operations and their specifications from Rocq's core library (floats,
63-bit integers, strings). The summary's fourth section stays
unconstrained: it lists the inductive types checked under Rocq's default
rule that an index does not raise the universe of its type (the rule the
`-indices-matter` option turns off), and `Corelib.Init.Logic.eq` is on it
in every development.

```sh
GOROROBA_QUANTUM=../gororoba-quantum ROCQ_BUILD_TREE=build/rocq sh ci/compare_signs.sh
```

compares `Tower.sign` with `cd_core.cd_sign` and with the two Rocq sign
functions of `SignBridge.v` (`CdTowerBasisSign.sigma` and `open_cube_sign`)
on every index pair of levels 3 to 6; `ROCQ_BUILD_TREE` names the `rocq`
directory of a tree that `make rocq` compiled, and `ci/audit/SignTable.v`
prints the two Rocq tables, and

```sh
GOROROBA_QUANTUM=../gororoba-quantum sh ci/compare_estimator.sh
```

compares `KernelMap.vHat`, `KernelMap.nHat` and `KernelMap.nullity`, evaluated
over the rationals, with `pathion_kernel_map._pair_summary` on twelve fixed
blocks whose bins are all decided, and

```sh
GOROROBA_QUANTUM=../gororoba-quantum sh ci/compare_kernel_map_bins.sh [LEVEL [SCOPE]]
```

evaluates `KernelMap.binContract` on the ideal kernel map of
`pathion_kernel_map` at level `LEVEL` (5, 6 or 7; default 5). It runs
`kernel_map_circuit` at dimension `2^LEVEL` for every two-term operand
`e_i + t e_j` (`i != j`, `t = +1` or `-1`): 1,984 operands at level 5, with
the module's six operands and two twins among them, 8,064 at level 6 and
32,512 at level 7. At levels 6 and 7 it also runs each operand of
`pathion_wide_coset.WIDE_OPERANDS` through the coset-block circuits that the
64- and 128-dimensional runs execute; `SCOPE wide` takes only those. The
`+1` bins of the ideal output contrast are `pos`, with bin `y` read as index
`y`, and the script requires `Tower.alignedPairCount`, `KernelMap.nullity`
and half the contrast sum to agree. At every level the contract must reject
`e_1 + e_18` with one SELECT sign negated and a contrast with one bin
negated; at levels 6 and 7 it must also reject the cocycle-free wide
operand. The script refuses a gororoba-quantum checkout whose
`gororoba_quantum` directory is modified or changes during the run, and it
prints that directory's git tree. Level 5 takes about a minute and level 6
about four minutes on the build host; level 7 with `SCOPE all` needs about
35 minutes and more than 4 GiB (issue 36). Each prints the gororoba-quantum commit it
read and runs on demand, since it reads another repository; the second and
third also need that repository's Python packages and the built Lean
library.

```sh
GOROROBA_OPEN=../gororoba-open sh ci/check_delegation_sources.sh
```

renders the three inventory sources of `rocq/delegation` again from the
statement inventories of that checkout, whose sha256 it records, requires
each rendering to equal the tracked source and the statements of each
tracked source to be the bytes of its inventory with a final newline
added, and requires the generator
to refuse a statement whose conclusion names another right than its
hypothesis.

```sh
GOROROBA_QUANTUM=../gororoba-quantum sh ci/check_quantum_sources.sh
```

renders the eight sources of `rocq/quantum` that `ci/quantum-sources/` generates
(the sign semantics and source certificates, the N = 21 target-flip witnesses,
the canonical kernel certificates, the Gaussian-integer certificates of the
G_2 derivation tables, the W8 arc matrices and the derivation span, and the
Stiefel witness) from the records and `cd_core.py` of that checkout, requires
each rendering to equal the tracked file, and requires each generator to reject
a copy of its source with one digit changed (eight copies, one per rendered
source), and runs four more calibrations: a copy of the gororoba-quantum
package whose `cd_core.py` has one changed shift must be rejected by the
generators that read it, the Stiefel package cross-check
(`stiefel_witness_certificate.py --package-cross-check`, python-hypercomplex) must
equal the retained `package_cross_check.json` (reported as skipped when
`hypercomplex` is not installed), six refused writes (an override, `--output`, an
unknown flag, a linked source, a linked `rocq/quantum`, an override naming no
directory) must leave the checkout unchanged, and `make_mutants.py` and
`make_span_mutants.py` must build their mutants from the tracked sources. It
needs python-flint under `PYTHON`; a missing module or tool exits
with status 2, a rendering difference with status 1. A write of a generator
(`--write`, `--generate`) goes only to `rocq/quantum` of this checkout and to the
JSON record beside it; a destination override is honored only with `--check`.

```sh
GOROROBA_QUANTUM=../gororoba-quantum opam exec --switch=rocq-9.3 -- \
  sh ci/replay_quantum_bundles.sh [--ledgers-only] [BUNDLE...]
```

compares, for each retained bundle of `docs/evidence/` in gororoba-quantum, the
`proofs/NAME.v` rows of its ledgers with the files of `rocq/quantum` (the
`proofs/theories/` and `proofs/verified/` rows belong to gororoba-open and are
compared with `GOROROBA_ROOT` when it is set), then runs the bundle's replay and
the `TargetFlipN21` compile and kernel check. `--ledgers-only` stops after the
comparison and needs no Rocq. A `BUNDLE` is one plain path component naming a
bundle; any other word exits with status 2. It runs on demand, since it reads
another repository and compiles for minutes; a bundle that reads a gororoba-open
checkout is skipped unless `GOROROBA_ROOT` names one.

The Rocq half of the span and Gaussian mutation controls has no caller. Nothing in
`ci/check.sh`, `ci/check_rocq.sh` or `ci/check_quantum_sources.sh` runs
`ci/quantum-sources/run_span_checks.sh`, which compiles the three span sources
and `SpanQueries.v`, kernel-checks them, builds the six mutants of
`make_span_mutants.py` and requires each to be rejected in the lemma named for it;
the six mutants of `make_mutants.py` (the Gaussian-integer sources) have no
compile driver. The span checks run by hand, with a build directory outside the
checkout:

```sh
B=$(mktemp -d)
cp rocq/quantum/*.v ci/quantum-sources/SpanQueries.v ci/quantum-sources/make_span_mutants.py "$B"
(cd "$B" && opam exec --switch=rocq-9.3 -- rocq makefile --no-rocq-package-warning -Q . "" -o Makefile.span \
  CdTowerDomain.v CdTowerDomainR.v CdTowerReal.v CdTwistedProduct.v CdTowerRing.v CdTowerRingBasis.v \
  CdTowerRingBaseChange.v GaussianIntegerHom.v MatrixLeftInverseCertificate.v CdTowerG2Derivations.v && \
  opam exec --switch=rocq-9.3 -- make -f Makefile.span)
opam exec --switch=rocq-9.3 -- sh ci/quantum-sources/run_span_checks.sh "$B"
```

`run_span_checks.sh` compiles the span sources itself, takes `$HOME/.opam/rocq-9.3/bin/rocq`,
writes `span-checks-record.txt` in `$B`, ends with one verdict line and exits 0
when every expectation held.
The `make` above runs one job at a time: measured with `-j4`, it stopped on a
missing dependency of `CdTowerDomain` (hypothesis: the generated makefile
lacks an edge for the empty logical root; untraced).

## Kernel replay evidence

gororoba-open records a theorem as kernel checked from a replay of its
proof source. `ci/kernel_replay_evidence.py` is the producer of that replay:
for one source of `rocq/open` and the names of its declarations it
compiles the dependency closure in a scratch directory, re-checks the proof
object with `rocq check -silent -o`, runs `Print Assumptions` on each
declaration, and writes the evidence JSON that
`gororoba-db theorem identity record-kernel-evidence` ingests, together with
the proof object and the compile, kernel and assumption logs a witness binds.
gororoba-open reads that file and never runs Rocq.

```sh
opam exec --switch=rocq-9.3 -- python3 -I ci/kernel_replay_evidence.py \
    --proof theories/X.v --declaration NAME --warning-policy fatal_default \
    --out ../kernel-capture/X
```

The tree is `rocq/open` of the checkout `GOROROBA_MATH` names, or the
directory `--tree` names. The producer accepts only Rocq 9.3.0 on OCaml 5.5.1,
refuses a warning line, an error line and a local absolute path in any
output, writes the evidence file last (and removes it when the summary cannot
be printed), and refuses an output directory inside the git repository that
tracks the tree. It creates the output directory before the replay, refuses a
symbolic link, and checks the directory again before the first write. A git
failure other than "no repository" or "path not tracked" refuses the run. It
removes its scratch directory on SIGTERM (status 143). Its header comment gives
the fixed argument vectors and the environment variables it reads
(`FLOCQ_ROOT`, `OPAM_SWITCH_PREFIX`; `COQPATH` and `ROCQPATH` are removed).

```sh
sh ci/check_kernel_replay_evidence.sh
```

calibrates it on a synthetic three-file tree under the switch `rocq-9.3`: a
closed theorem over a chain of two imported sources whose dependency order
differs from their lexical order, a theorem over a declared axiom and a source
that imports Flocq must each produce evidence that a verifier compares with
literal expectations: the complete compiler, checker and assumption argument
vectors, the compilation order, the digests of the written files and the
sources, the assumption lists (empty, `postulate` and empty) and, for Flocq,
an object list equal to the sorted `.vo` files of the switch's library with
`-R external/Flocq Flocq` before every target, and a `flocq_producer` that
names the entry of a scratch manifest (`ci/flocq_manifest.py --record` of the
running switch) which lists those objects. The verifier is itself
calibrated: 20 mutated copies of that evidence (swapped `-R` pairs, a lexical
or reversed compilation order, a truncated Flocq list, altered digests, a
missing or renamed Flocq producer, among others) must each be rejected, and a
manifest with no entry, two entries, the wrong schema or no file for the
switch's objects must be refused. A warning printed on a zero exit status, a
source that fails to compile, a missing declaration, another Rocq version, a
Flocq directory without `Core/Core.vo`, an output directory inside the
tracking repository, a failing git, an output directory that is a symbolic
link or becomes one during the replay, and a summary that cannot be printed
must each be refused with no evidence file. The verifier checks use no `assert`,
so `python3 -O` runs them unchanged. The script removes its temporary directory
on exit, INT (status 130) and TERM (status 143). It compiles a few sources of a
few lines each, and `sh ci/check_rocq.sh` runs it from its export of `HEAD`
before the tree build and passes its status 2 (a tool or the switch is
missing) through as 2.

## License

Apache-2.0, in [LICENSE](LICENSE), for the library and the proof trees. The
package descriptions, the patch and the switch export under `rocq/open/opam`
describe third-party Rocq libraries and carry the license each `opam` entry
names.
