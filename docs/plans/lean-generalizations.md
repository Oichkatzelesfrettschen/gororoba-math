# Lean generalizations of the Rocq every-level and ring-class results

This plan orders the Lean work of issue 55. `lean-generalizations.tsv`
beside it holds one row per headline theorem of each Rocq source whose results
quantify over every level of the Cayley-Dickson tower or over a class of
coefficient rings, with the Lean statement a proof worker writes, the
declarations it reuses, the rows it depends on and an effort estimate. No
statement in either file has been compiled; each is a proposal checked by
reading the library source at origin/main 6d00d47 and the Rocq source it
translates.

## Columns

- `order`: dependency order; every number in `depends` is smaller.
- `rocq`: `PATH:NAME`, with the enclosing Rocq modules in `NAME` as in
  `ci/headline-results.tsv`; a name inside a `Section` carries no prefix.
- `lean_statement`: one line. A statement that begins `(ctx X)` takes the
  variables of context `X` below; "with new def" names a definition the row
  introduces.
- `narrowing`: `-` when the Lean statement is at least as general as the
  Rocq one; otherwise the narrower Lean statement and its reason. A cell that
  begins `unsure:` marks a statement whose hypotheses or transcription the
  worker re-reads before the proof starts. A cell that begins `no Lean
  reading:` marks a row with `-` in `lean_module`, `lean_statement` and
  `effort`.
- `headline`: `yes` when the theorem name occurs in `README.md` of
  gororoba-math, in `registry/claims.toml` or a receipt under
  `data/output/audit/` of gororoba-open, or in `formalization.yaml` or
  `docs/evidence/` of gororoba-quantum (a word-bounded name search, so a
  common name such as `flexible` or `first_half` can match a record of
  another file; a row whose `headline` decides a headline-results entry is
  confirmed against the record first).
- `effort`: S (a few lemmas over existing ones), M (a new induction or a
  linear-algebra equivalence), L (a new theory or a large computation).

## Contexts

- ctx A: `{R : Type u} [NonAssocRing R] [StarRing R]` (for
  `CayleyDickson A` statements, the same classes on `A`).
- ctx C: `{R : Type u} [CommRing R] [StarRing R] [TrivialStar R]`, the
  context of `TowerModule.lean` and of the trace form `Tower.dot`,
  `Tower.re` of `AnnihilatorSymmetry.lean`.
- ctx O: ctx C with `[PartialOrder R] [IsOrderedAddMonoid R]
  [NoZeroDivisors R]` and the explicit hypothesis
  `hsq : ∀ x : R, 0 ≤ x * x`, the ordered section of
  `AnnihilatorSymmetry.lean`; over a field it reads with `K` and `[Field K]`.
- ctx F: `{K : Type u} [Field K] [StarRing K] [TrivialStar K]`.

## Conventions between the Rocq trees and the Lean tower

- Coefficients. The functor `RingTower` of `CdTowerRing.v` takes a
  `CommutativeRing` whose conjugation on level 0 is the identity; Lean takes
  `Tower R k` over `NonAssocRing` with `StarRing`, and a Rocq statement
  reads in ctx C (`TrivialStar R`) unless its proof uses less. The functor
  `CdTower` of `CdTowerDomain.v` takes an `OrderedDomain`; its fields map
  to ctx O as `AnnihilatorSymmetry.lean` states: `sq_nonneg` to `hsq`,
  the nonnegative sums to `IsOrderedAddMonoid`, `mul_integral` to
  `NoZeroDivisors`. Rocq `one_neq_zero` has no Lean counterpart; a row that
  needs it adds `[Nontrivial R]`. The open tree `RecursiveCDTower.v` and the
  verified tree fix the Stdlib reals, which ctx O covers with `R := ℝ`.
- Product, conjugate, pure. All three trees and Lean double with
  `(a, b)(c, d) = (ac - conj(d) b, da + b conj(c))` and `conj(a, b) =
  (conj a, -b)` (`Tower.mk_mul_mk`, `Tower.star_mk`). Rocq `pure k a`
  (`conjugate k a = scale k neg_one a`) reads `star a = -a`; Rocq
  `re k` and `dot k` are `Tower.re k` and `Tower.dot k`; the adjoined
  unit `i_unit k = (zero k, one k)` is `mk 0 1`.
- Index. A Rocq index `a < 2^k` (`nat`) is `p : BitVec k` with
  `p.toNat = a`; `Nat.lxor` is `^^^` through `BitVec.toNat_xor`. The
  quantum tree puts index bit `j` in the second half of the
  `(j + 1)`-st double, as Lean's msb does. The open tree's `cube order` is a
  nested pair whose last component is the highest bit; `cube_encode` is
  `BitVec.toNat` and `BitVec.cons` adds the top bit
  (`CDSignNumericCorrespondence.v`).
- Signs. `sigma k a b` (quantum, integer-valued) is `Tower.sign k p q` (compared by
  `ci/compare_signs.sh`); `sign_exponent order l r` (open, Bool) is
  `Tower.negSign k l r` (`CDTowerSignCorrespondence.v`, `SignBridge.v`);
  `am_exponent k a b` swaps its arguments, `am_exponent k a b = negSign k b a`
  (`am_sign`), so the left sign row `sign_row k m x = am_exponent k x m` is
  `negSign k m x`.
- Associator phases. Lean `Tower.associates a b c` brackets
  `(e a * e c) * e b` against `e a * (e c * e b)`, middle argument last.
  Quantum `assoc k p q x` (`e_p (e_q e_x)` against `(e_p e_q) e_x`) and
  open `associator_phase order l m r` (`schreier l m r XOR sign_exponent l m`)
  are both `!associates p x q`, read off the four sign terms of each
  definition; the rows name it `Tower.assocPhase p q x`.
- Levels. Rocq `lift j k` lands in `cd (k + j)`; Lean's `Tower.lift j k`
  lands in `Tower R (j + k)` so that `j + (k + 1)` unfolds to
  `(j + k) + 1` by `rfl`, and a statement at level `k + 2` lifts by
  induction on `k` with `mk · 0`.
- Base rings with `i`. Rocq's Gaussian integers carry the identity as
  conjugation; Mathlib's `GaussianInt` carries complex conjugation as
  `star`, which builds a different tower, so a Gaussian instance in Lean uses
  a local trivial star or stays in Rocq (row 38).
- Comparisons. A row that defines a Lean function mirroring a Rocq one of
  another sign or index convention names a new `ci/` comparison in the
  manner of `ci/compare_signs.sh`: integer instance, levels 1 to 5 or 6, a
  mutated reference rejected.

## Dependency layers

Layer `n` holds the rows whose longest dependency chain has `n` rows
(rows with no Lean reading omitted).

1. Layer 1 (39 rows): 1, 5, 6, 7, 8, 10, 11, 12, 13, 17, 18, 19, 20, 23, 26, 29, 30, 34, 35, 36, 39, 43, 46, 47, 48, 49, 55, 61, 62, 64, 65, 68, 72, 73, 74, 80, 85, 93, 96.
2. Layer 2 (34 rows): 2, 3, 9, 14, 15, 16, 21, 22, 27, 31, 32, 37, 40, 41, 50, 54, 57, 63, 66, 67, 69, 70, 75, 81, 83, 84, 94, 95, 97, 106, 107, 108, 109, 110.
3. Layer 3 (22 rows): 4, 24, 28, 33, 38, 42, 44, 51, 56, 60, 71, 76, 79, 82, 88, 92, 98, 99, 101, 102, 103, 104.
4. Layer 4 (10 rows): 25, 45, 52, 53, 58, 59, 77, 86, 100, 105.
5. Layer 5 (5 rows): 78, 87, 89, 90, 91.

By family: ring and star laws, maps, the derivation extension and the
scalar actions of a double (rows 1 to 16) and the trace form with the
characteristic-2 and square-root-of-minus-one rows (17 to 38) open the work;
basis extension, base change, certificates, the order-three map and the ideal
lemma (39 to 48), the imaginary sum (49 to 54), and the kernel dimensions,
fold, zero divisors, Hurwitz bound, level-2 rows and quaternion modules (55
to 71) build on them; the sign, ANF, associator-phase, census, sign-code and
sparse-support rows (72 to 98) form a combinatorial strand over `BitVec`
that needs no coefficient ring beyond row 80; the derivation rows (99, 100)
close the list. Rows 101 to 110 are instance rows that point at a canonical
row, and rows 111 to 122 have no Lean reading.

## First tranche

Rows 19, 20, 22, 29, 39, 7, 74, 75, 80, 84: `conj_mul_left`, `conj_mul_right`,
`lemma_9_2`, `l_x_skew_symm`, `multiplicative_by_basis`, `diag_mul`,
`anf_inversion`, `canonical_anf_unique`, `assoc_basis` and
`associator_doubling`. They have the most later rows depending on them
(the two conjugation identities 14 and 13 each, `assoc_basis` 11,
`anf_inversion` 10, `canonical_anf_unique` 9, `lemma_9_2`,
`multiplicative_by_basis` and `associator_doubling` 7 each,
`l_x_skew_symm` 6, `diag_mul` 5), they introduce the new definitions the
later rows share (`Tower.anfCoeff`, `Tower.anfEval`, `Tower.assocPhase`,
`Tower.commPhase`, `CayleyDickson.map`), and all but two are effort S.

## Rows with no Lean reading

- Row 111, `rocq/open/theories/FloatRealBridge.v:float_quat_rotate_agrees`: the statement compares two Rocq definitions of the rotation (the FLOAT_OPS extraction route and Quaternion.v); the Lean side needs only the level-2 rows.
- Row 112, `rocq/quantum/CdSignPythonSemantics.v:cd_sign_returns_sigma`: a semantics of Python source is evidence about running code (AGENTS.md, Evidence axis); the Lean side meets the same function through ci/compare_signs.sh, which compares Tower.sign with cd_core.cd_sign.
- Row 113, `rocq/quantum/CdSignAstTranslation.v:function_semantic_preservation`: translation validation of a Python syntax tree, evidence about code with no algebraic content.
- Row 114, `rocq/quantum/SignBridge.v:open_cube_sign_sigma`: it identifies two Rocq spellings of one sign function; Lean holds one spelling, Tower.negSign, compared with them by ci/compare_signs.sh.
- Row 115, `rocq/quantum/TowerBridge.v:to_quantum_mul`: it relates two Rocq carriers of the same tower; Lean has a single carrier, Tower R k.
- Row 116, `rocq/open/theories/CDSignNumericCorrespondence.v:numeric_cube_sign`: it relates a fuel-indexed numeric function of the open tree to the cube sign; Lean indexes by BitVec k with BitVec.toNat_xor, so no fuel or encoding enters.
- Row 117, `rocq/quantum/CdTowerLeibnizSystem.v:LeibnizSystem.system_solved`: the flat index j = 2^k m + q and the equation list are the input format of a Rocq certificate (MatrixSplittingCertificate.v); the Lean reading of the Leibniz rule is row derivation_by_basis.
- Row 118, `rocq/quantum/CdTowerCanonicalKernels.v:CanonicalKernels.W8_kernel_free_basis`: a generated certificate at fixed level 5 (Evidence axis); its general lemma is row kernel_free_basis, and the twelve point tables stay Rocq artifacts.
- Row 119, `rocq/quantum/CdTowerG2Derivations.v:G2Derivations.derivation_1`: a generated table checked by vm_compute (Evidence axis); the Lean reading of the 14 tables together is the dimension row of CdTowerG2DerivationSpan.v.
- Row 120, `rocq/quantum/A5W8ArcMatrixRanks.v:W8ArcMatrixRanks.w8_nm_linear_point1_columns_independent`: a fixed-matrix certificate (Evidence axis); its general lemma is row columns_independent.
- Row 121, `rocq/quantum/CdTwistedProduct.v:Twisted.W8_ideal_exchange`: a fixed 32-coordinate polynomial identity read by the Singular ideal of the A_5 W8 record; its general lemma is row ideal_exchange.
- Row 122, `rocq/open/theories/CDSparseBlockTransport.v:sparse_photonic_configuration_coverage`: membership in a retained configuration list is a record check (Evidence axis).

Further rows carry a narrower Lean reading and say so in `narrowing`: row
35 (norm multiplicativity, levels 0 to 3 only), row 108
(an abstract interface read on the tower), row 69 (an inductive
predicate on nat read as a module statement), row 70 (the
abstract lane of Moreno's Theorem 1.16), row 95 (a group-cochain
identity read for the tower cochain), row 98 (a MathComp block
rank read as the kernel decomposition), and rows 38 and
44 (fixed levels over a class of rings).

## Census

The census read the headers and theorem statements of every source of
`rocq/open/theories`, `rocq/open/verified` and `rocq/quantum` that the
inventory of 2026-11-15 classed every-level or ring-class, every source added
since, and every source that names a ring functor (`CommutativeRing`,
`OrderedDomain`, `RingHom`) or binds a level next to a tower operation.

Sources with rows (61):
`rocq/open/theories/BooleanANFDegree.v`, `rocq/open/theories/BooleanCochainFiltration.v`, `rocq/open/theories/Brown1972ChapterIII.v`, `rocq/open/theories/C1539_MorSkewSymm.v`, `rocq/open/theories/C1542_MorVlambdaOrbit.v`, `rocq/open/theories/C1543_MorMod4Bound.v`, `rocq/open/theories/CDAssociatorCensus.v`, `rocq/open/theories/CDAssociatorDoubling.v`, `rocq/open/theories/CDDoubleFunctor.v`, `rocq/open/theories/CDPhaseDegree.v`, `rocq/open/theories/CDPureDoublingKernel.v`, `rocq/open/theories/CDScalarExtension.v`, `rocq/open/theories/CDSignNumericCorrespondence.v`, `rocq/open/theories/CDSparseBlockTransport.v`, `rocq/open/theories/CDSparseMatrixTransport.v`, `rocq/open/theories/CDTowerFoldTransport.v`, `rocq/open/theories/CDTowerZeroDivisors.v`, `rocq/open/theories/CDTraceZero.v`, `rocq/open/theories/Dickson1921.v`, `rocq/open/theories/DicksonCDProcess.v`, `rocq/open/theories/FinDimHModule.v`, `rocq/open/theories/FloatQuaternion.v`, `rocq/open/theories/FloatRealBridge.v`, `rocq/open/theories/HModuleDim.v`, `rocq/open/theories/HurwitzTheorem.v`, `rocq/open/theories/Moreno1997.v`, `rocq/open/theories/MorenoTowerInstance.v`, `rocq/open/theories/Schafer1954.v`, `rocq/open/theories/SchreierSignCode.v`, `rocq/open/theories/SignCodeCardinality.v`, `rocq/open/verified/C957_VoudonZD.v`, `rocq/quantum/A5W8ArcMatrixRanks.v`, `rocq/quantum/CdAnnihilatorSymmetry.v`, `rocq/quantum/CdAnnihilatorSymmetryReal.v`, `rocq/quantum/CdAssociatorAnf.v`, `rocq/quantum/CdAssociatorCensus.v`, `rocq/quantum/CdAssociatorPointIndicators.v`, `rocq/quantum/CdHalfFold.v`, `rocq/quantum/CdImaginarySumConference.v`, `rocq/quantum/CdSignAstTranslation.v`, `rocq/quantum/CdSignPythonSemantics.v`, `rocq/quantum/CdSignRowAnf.v`, `rocq/quantum/CdTowerBasisSign.v`, `rocq/quantum/CdTowerCanonicalKernels.v`, `rocq/quantum/CdTowerDomain.v`, `rocq/quantum/CdTowerDomainR.v`, `rocq/quantum/CdTowerDomainZ.v`, `rocq/quantum/CdTowerG2DerivationSpan.v`, `rocq/quantum/CdTowerG2Derivations.v`, `rocq/quantum/CdTowerKernelCertificate.v`, `rocq/quantum/CdTowerLeibnizSystem.v`, `rocq/quantum/CdTowerOrderThreeMap.v`, `rocq/quantum/CdTowerRing.v`, `rocq/quantum/CdTowerRingBaseChange.v`, `rocq/quantum/CdTowerRingBasis.v`, `rocq/quantum/CdTowerRingDomain.v`, `rocq/quantum/CdTwistedProduct.v`, `rocq/quantum/MatrixLeftInverseCertificate.v`, `rocq/quantum/MatrixSplittingCertificate.v`, `rocq/quantum/SignBridge.v`, `rocq/quantum/TowerBridge.v`.

Sources whose headline results the Lean library already states, so issue 55
owes no row:
- `rocq/quantum/CdTowerReal.v`: `dot_self_nonneg`, `dot_self_zero` are
  `Tower.dot_self_nonneg`, `Tower.eq_zero_of_dot_self_eq_zero` at `ℝ`.
- `rocq/open/theories/CDTowerKernelSwap.v`: `tower_kernel_equality` is
  `Tower.mul_eq_zero_iff_rev`, `tower_inner_adjoint` is
  `Tower.dot_mul_adjoint`.
- `rocq/open/theories/C1538_MorZDSymmetry.v`: `zd_symmetry` is an instance of
  `Tower.mul_eq_zero_iff_rev`; the sedenion pair is a fixed-level instance.
- `rocq/open/theories/RecursiveCDTower.v`: its additive, negation and
  conjugation laws are the `NonAssocRing` and `StarRing` instances of every
  level.
- `rocq/open/theories/CDTowerSignCorrespondence.v`: `tower_basis_multiplication`
  and `tower_basis_conjugation` are `Tower.e_mul_e` and `Tower.star_e`.
- `rocq/open/theories/CDTowerMatrixAdapter.v`: the column encoding is
  `Tower.basis` with Mathlib's `LinearMap.toMatrix`; `tower_dimension_power`
  is `Tower.finrank_eq`.
- `rocq/open/verified/C956_RoutonAVT.v`: the persistence of non-associativity
  is `Tower.exists_mul_assoc_ne`.
- `rocq/quantum/CdTowerE1E18Kernel.v`: `Tower.free_ker_mulLeft_e_add_e` and
  `Tower.finrank_ker_pathion_1_18` state the kernel over every ring with
  `2` left-regular.
- `rocq/quantum/GaussianIntegerHom.v`: Mathlib's `Zsqrtd.lift` and the
  domain instance of `GaussianInt`.
- Within files that have rows: `norm_mul`, `adjoint`, `kernel_equality`,
  `purity_left`, `direct_finiteness` (CdTowerDomain.v, CdAnnihilatorSymmetry.v
  and their instances) are `Tower.mul_star_eq_dot`, `Tower.dot_mul_adjoint`
  and the three partnered theorems of `AnnihilatorSymmetry.lean`;
  `reflect_mul`, `embed_mul`, `level_one_commutative`, `re_zero_pure`
  (CdTowerRing.v) are `CayleyDickson.reflect_mul`,
  `Tower.mk_zero_mul_mk_zero`, `CayleyDickson.mul_comm_of_trivialStar`,
  `Tower.star_eq_neg_of_re_eq_zero`; `basis_mul`, `sigma_diagonal`,
  `sigma_anticommute`, `sigma_left_involution`, `right_mul_entry`,
  `am_altercommutative` (CdTowerBasisSign.v) are `Tower.e_mul_e`,
  `Tower.e_mul_self`, `Tower.e_mul_e_anticomm`, `Tower.negSign_xor_right`,
  `Tower.repr_e_mul`, `Tower.negSign_swap`; `sign_row_involution`
  (CDPhaseDegree.v) is `Tower.negSign_xor_right`; `sign_doubling`
  (CDAssociatorDoubling.v) is `Tower.negSign_cons`; `decompose`,
  `linear_ext`, `bilinear_ext` (CdTowerRingBasis.v) are `Basis.sum_repr`
  and `Basis.ext`; the remaining linearity laws of CDDoubleFunctor.v and
  CDScalarExtension.v are the module axioms of `CayleyDickson.instModule`.

Sources outside issue 55:
- Partners of existing Lean headline rows (their Lean theorem is the
  original): `rocq/quantum/CdTowerBasisBridge.v`, `rocq/quantum/CdTowerTwoTermBridge.v`, `rocq/quantum/CdTowerModuleBridge.v`, `rocq/quantum/CdTowerTwoTermNullity.v`, `rocq/quantum/CdTowerTwoTermRecursion.v`, `rocq/quantum/CdTowerAlignedPairSpectrum.v`, `rocq/quantum/CdTowerAlignedPairClosedForm.v`, `rocq/quantum/CdTowerAssociatorSpace.v`, `rocq/quantum/CdTowerTwoTermBins.v`, `rocq/quantum/CdTowerMulStarSelf.v`, `rocq/quantum/KernelMapEstimator.v`, `rocq/quantum/CdTowerDomain.v`, `rocq/quantum/CdTowerNonAssociative.v`.
- Fixed level or fixed algebra: `rocq/open/theories/SedenionFoldTransport.v`,
  `rocq/open/theories/CDConcreteTowerAdapter.v`,
  `rocq/open/theories/MinimalUncurvedObstruction.v`,
  `rocq/open/verified/C1133_BraidParityPreservation.v`,
  `rocq/open/verified/C029_SedenionOctonionSubalgebras.v`,
  `rocq/open/verified/C1636_ScheduleProductCount.v`,
  `rocq/quantum/StiefelWitnessInvertible.v`, `rocq/quantum/CdTowerRealKernels.v`,
  `rocq/quantum/TargetFlipN21.v`, and the quaternion, octonion and sedenion
  instances inside Dickson1921.v, DicksonCDProcess.v, Brown1972ChapterIII.v,
  Schafer1954.v and HurwitzTheorem.v.
- No Cayley-Dickson product: `rocq/open/theories/SignCodeProjection.v` (any
  binary code with the constant word), `BooleanPermutation.v`,
  `CubeAffineCosets.v`, `WalshProbability.v`, `BaezNormedDivAlgebra.v`,
  and `rocq/open/verified/C1141_ZDGraphCountingIdentities.v`,
  `C1142_XORScatterGatherSums.v`, `C1463_MatrixColumnIdeal.v`,
  `C882_OctahedronGraphSpectrum.v`, `C010_ComponentBridgeBound.v`. Each has
  a Mathlib reading (Finset sums, `Submodule (ZMod 2)`, matrices, graphs)
  that no tower statement needs.

## Checks

No Lean or Rocq command ran for this plan. The table was checked by script:
11 cells per row, no tab or newline inside a cell, `order` contiguous,
every `depends` entry smaller than its row, every `rocq` cell resolving to
exactly one theorem of its file, every `statement` at most 30 words.
