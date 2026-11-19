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
  a local trivial star or stays in Rocq (row 39).
- Comparisons. A row that defines a Lean function mirroring a Rocq one of
  another sign or index convention names a new `ci/` comparison in the
  manner of `ci/compare_signs.sh`: integer instance, levels 1 to 5 or 6, a
  mutated reference rejected.

## Dependency layers

Layer `n` holds the rows whose longest dependency chain has `n` rows
(rows with no Lean reading omitted).

1. Layer 1 (40 rows): 1, 5, 6, 7, 8, 10, 11, 12, 13, 17, 18, 19, 20, 23, 26, 29, 30, 34, 35, 36, 40, 44, 47, 48, 49, 50, 56, 62, 63, 65, 66, 69, 73, 74, 75, 81, 86, 94, 97, 101.
2. Layer 2 (34 rows): 2, 3, 9, 14, 15, 16, 21, 22, 27, 31, 32, 37, 41, 42, 51, 55, 58, 64, 67, 68, 70, 71, 76, 82, 84, 85, 95, 96, 98, 100, 107, 108, 109, 110.
3. Layer 3 (20 rows): 4, 24, 28, 33, 38, 43, 45, 52, 57, 61, 72, 77, 83, 89, 93, 99, 102, 103, 104, 105.
4. Layer 4 (11 rows): 25, 39, 46, 53, 54, 59, 60, 78, 80, 87, 106.
5. Layer 5 (5 rows): 79, 88, 90, 91, 92.

By family: ring and star laws, maps, the derivation extension and the
scalar actions of a double (rows 1 to 16) and the trace form with the
characteristic-2 and square-root-of-minus-one rows (17 to 39) open the work;
basis extension, base change, certificates, the order-three map and the ideal
lemma (40 to 49), the imaginary sum (50 to 55), and the kernel dimensions,
fold, zero divisors, Hurwitz bound, level-2 rows and quaternion modules (56
to 72) build on them; the sign, ANF, associator-phase, census, sign-code and
sparse-support rows (73 to 99) form a combinatorial strand over `BitVec`
that needs no coefficient ring beyond row 81; the derivation rows (100, 101)
close the list. Rows 102 to 110 are instance rows that point at a canonical
row, and rows 111 to 122 have no Lean reading.

## First tranche

Rows 7, 19, 20, 22, 29, 40, 75, 76, 81, 85:
`diag_mul`, `conj_mul_left`, `conj_mul_right`, `lemma_9_2`, `l_x_skew_symm`,
`multiplicative_by_basis`, `anf_inversion`, `canonical_anf_unique`,
`assoc_basis`, `associator_doubling`.
They have the most later rows depending on them (counted transitively:
row 7 has 5, row 19 has 14, row 20 has 13, row 22 has 7, row 29 has 6, row 40 has 7, row 75 has 10, row 76 has 9, row 81 has 11, row 85 has 7), they introduce the new definitions the
later rows share (`Tower.anfCoeff`, `Tower.anfEval`, `Tower.assocPhase`,
`Tower.commPhase`, `CayleyDickson.map`), and 7 of the ten are effort S.
`Tower.weight` and `Tower.anfDegree` enter with row 77, the first row whose
statement uses them.

## Proved rows

The library proves the ten rows of the first tranche and the rows of the second and third tranches
(issue 55), each in the module its row names; rows 14 to 16 are the theorems of rows 11 to 13, rows
66 and 67 share one theorem, rows 69, 70, 71 and 110 share one theorem, and rows 103 and 105 share one
theorem. Rows 50 and 74 define `Tower.isum` and `Tower.amExponent`; the comparisons that their
`comparison` cells name (`ci/compare_isum.sh`, `ci/compare_am_exponent.sh`) are owed:

| Row | Module | Theorem |
|---|---|---|
| 1 | `RingLaws` | `Tower.mul_eq_zero_iff_star_mul_star` |
| 2 | `RingLaws` | `Tower.mul_eq_zero_iff_star_mul_of_star_eq_neg` |
| 3 | `RingLaws` | `Tower.mul_eq_zero_iff_mul_star_of_star_eq_neg` |
| 4 | `RingLaws` | `Tower.mk_mul_mk_eq_zero_iff_of_star_eq_neg` |
| 5 | `RingLaws` | `Tower.mul_eq_zero_iff_reflect_mul_reflect` |
| 6 | `RingLaws` | `Tower.mul_eq_one_iff_mul_sub_eq_zero` |
| 7 | `Map` | `CayleyDickson.map_mul` |
| 8 | `Map` | `Tower.lift_mul` |
| 9 | `Map` | `Tower.lift_injective` |
| 10 | `Derivation` | `CayleyDickson.mapAdd_leibniz` |
| 11 | `ScalarAction` | `CayleyDickson.smul_mul_assoc` |
| 12 | `ScalarAction` | `CayleyDickson.mul_smul_comm` |
| 13 | `ScalarAction` | `CayleyDickson.instStarModule` |
| 14 | `ScalarAction` | `CayleyDickson.smul_mul_assoc` |
| 15 | `ScalarAction` | `CayleyDickson.mul_smul_comm` |
| 16 | `ScalarAction` | `CayleyDickson.instStarModule` |
| 17 | `TraceForm` | `Tower.re_mul_comm` |
| 18 | `TraceForm` | `Tower.re_mul_assoc` |
| 19 | `TraceForm` | `Tower.mul_star_mul_left` |
| 20 | `TraceForm` | `Tower.mul_mul_star_right` |
| 21 | `TraceForm`, `FlexibleLaw` | `Tower.mul_mul_self_eq`, `Tower.mul_mul_self_eq'` |
| 22 | `TraceForm` | `Tower.mul_eq_zero_iff_star_mul_eq_zero` |
| 23 | `TraceForm` | `Tower.re_eq_zero_of_mul_eq_zero_rev` |
| 24 | `TraceForm` | `Tower.dot_one_eq_zero_and_dot_mk_zero_one_of_mul_eq_zero` |
| 25 | `TraceForm` | `Tower.dot_one_eq_zero_and_dot_mk_zero_one_of_mul_eq_zero_right` |
| 26 | `TraceForm` | `Tower.mul_dot_smul_sub_star_eq_zero` |
| 27 | `TraceForm` | `Tower.exists_eq_inv_dot_smul_star_add` |
| 28 | `TraceForm` | `Tower.dot_eq_zero_of_mul_eq_zero` |
| 29 | `TraceForm` | `Tower.dot_mul_left_of_star_eq_neg` |
| 30 | `TraceForm` | `Tower.dot_mul_right_of_star_eq_neg` |
| 31 | `TraceForm` | `Tower.mul_eq_zero_iff_forall_dot_mul_eq_zero` |
| 32 | `TraceForm` | `Tower.dot_star_mul_self` |
| 33 | `TraceForm` | `Tower.dot_mul_self_comm` |
| 34 | `TraceForm` | `Tower.dot_add_self_add_dot_sub_self` |
| 35 | `NormMultiplicative` | `Tower.dot_mul_self_of_le_three` |
| 36 | `TraceForm` | `Tower.mul_comm_of_two_eq_zero` |
| 37 | `RingTowerI` | `Tower.kernel_swap_iff_two_eq_zero` |
| 38 | `RingTowerI` | `Tower.pure_kernel_swap_two_eq_zero` |
| 39 | `RingTowerI` | `Tower.zmod5_not_pure_kernel_swap` |
| 40 | `BasisExt` | `Tower.map_mul_of_map_e_mul_e` |
| 41 | `BasisExt` | `Tower.leibniz_of_leibniz_e` |
| 42 | `BaseChange` | `Tower.baseChange_mul` |
| 43 | `BaseChange` | `Tower.baseChange_leibniz` |
| 44 | `KernelCertificate` | `Tower.ker_mulLeft_basis_of_certificate` |
| 45 | `OrderThree` | `Tower.orderThree_mul` |
| 46 | `OrderThree` | `Tower.orderThree_star` |
| 47 | `Ideals` | `Ideal.add_mul_mem_and_sub_mul_mem_iff` |
| 48 | `Certificates` | `Matrix.linearIndependent_cols_of_mul_eq_smul_one` |
| 49 | `Certificates` | `Matrix.smul_eq_mulVec_of_splitting` |
| 50 | `ImaginarySum` | `Tower.isum_laws` |
| 51 | `ImaginarySum` | `Tower.dot_isum_mul` |
| 52 | `ImaginarySum` | `Tower.dot_mul_isum_mul_isum` |
| 53 | `ImaginarySum` | `Tower.dot_add_mul_isum` |
| 54 | `ImaginarySum` | `Tower.dot_smul_add_smul_mul_isum` |
| 55 | `ImaginarySum` | `Tower.repr_e_mul_isum` |
| 56 | `HalfFold` | `Tower.mk_left_mul_eq_zero_iff` |
| 57 | `HalfFold` | `Tower.mk_right_mul_eq_zero_iff` |
| 58 | `HalfFold` | `Tower.finrank_ker_mulLeft_mk_left` |
| 59 | `HalfFold` | `Tower.finrank_ker_mulLeft_mk_right` |
| 60 | `HalfFold` | `Tower.finrank_ker_mulLeft_mk_left_of_star_eq_neg` |
| 61 | `HalfFold` | `Tower.finrank_range_mulRight_of_star_eq_neg` |
| 62 | `Fold` | `Tower.dot_fold_self` |
| 63 | `ZeroDivisors` | `Tower.exists_zero_divisor` |
| 64 | `ZeroDivisors` | `Tower.exists_dot_mul_self_ne` |
| 65 | `Hurwitz` | `Tower.hurwitzRadon_lt` |
| 66 | `Quaternion` | `Tower.mul_assoc_two` |
| 67 | `Quaternion` | `Tower.mul_assoc_two` |
| 68 | `NormMultiplicative` | `Tower.dot_mul_self_of_le_three` |
| 69 | `QuaternionModule` | `Module.four_dvd_finrank_of_quaternion` |
| 70 | `QuaternionModule` | `Module.four_dvd_finrank_of_quaternion` |
| 71 | `QuaternionModule` | `Module.four_dvd_finrank_of_quaternion` |
| 73 | `SignLaws` | `Tower.negSign_xor_left_right` |
| 74 | `SignLaws` | `Tower.amExponent_eq` |
| 75 | `BooleanAnf` | `Tower.anfEval_anfCoeff` |
| 76 | `BooleanAnf` | `Tower.anfCoeff_unique` |
| 77 | `BooleanAnf` | `Tower.anfDegree_two_point` |
| 78 | `BooleanAnf` | `Tower.anfDegree_negSign_left` |
| 79 | `BooleanAnf` | `Tower.anfDegree_negSign_left` |
| 80 | `BooleanAnf` | `Tower.anfDegree_negSign_right` |
| 81 | `AssociatorPhase` | `Tower.e_mul_e_mul_e` |
| 82 | `AssociatorPhase` | `Tower.assocPhase_eq_false_of_dependent` |
| 83 | `AssociatorPhase` | `Tower.assocPhase_eq_false_of_degenerate` |
| 84 | `AssociatorPhase` | `Tower.assocPhase_two` |
| 85 | `AssociatorPhase` | `Tower.assocPhase_cons` |
| 86 | `AssociatorPhase` | `Tower.pairCoeff_eq_true` |
| 87 | `AssociatorPhase` | `Tower.anfDegree_assocPhase` |
| 88 | `AssociatorPhase` | `Tower.anfDegree_assocPhase` |
| 89 | `AssociatorPhase` | `Tower.assocPhase_point_pair` |
| 90 | `AssociatorCensus` | `Tower.card_anfDegree_assocPhase_eq` |
| 91 | `AssociatorCensus` | `Tower.card_anfDegree_assocPhase_eq_one` |
| 92 | `AssociatorCensus` | `Tower.sum_card_anfDegree_assocPhase` |
| 93 | `AssociatorCensus` | `Tower.card_assocPhase_true` |
| 96 | `SignCode` | `Tower.schreier_xor_schreier_zero` |
| 97 | `SparseSupport` | `Tower.repr_mul_ne_zero_mem` |
| 98 | `SparseSupport` | `Tower.mul_eq_zero_iff_forall_sector` |
| 99 | `SparseSupport` | `Tower.mul_eq_zero_iff_forall_sector` |
| 100 | `Derivation` | `Tower.leibniz_four_iff_of_restricts` |
| 101 | `Derivation` | `Tower.finrank_leibniz_of_certificate` |
| 102 | `TraceForm` | `Tower.int_mul_mul_self_eq` |
| 103 | `TraceForm` | `Tower.real_mul_mul_self_eq` |
| 104 | `TraceForm` | `Tower.real_exists_eq_inv_dot_smul_star_add` |
| 105 | `TraceForm` | `Tower.real_mul_mul_self_eq` |
| 106 | `TraceForm` | `Tower.real_dot_one_eq_zero_and_dot_mk_zero_one_of_mul_eq_zero` |
| 107 | `TraceForm` | `Tower.int_mul_dot_smul_sub_star_eq_zero` |
| 108 | `RingLaws` | `Tower.int_mul_eq_zero_iff_reflect_mul_reflect` |
| 109 | `TraceForm` | `Tower.real_pathion_dot_mul_left_of_star_eq_neg` |
| 110 | `QuaternionModule` | `Module.four_dvd_finrank_of_quaternion` |

`ci/compare_anf.sh` and `ci/compare_assoc_phase.sh` compare the definitions
of rows 75 and 81 with their Rocq partners of `rocq/quantum` and with the
Python of gororoba-quantum. The open-tree spellings (`canonical_anf` of
`BooleanANFDegree.v`, `associator_phase` of `CDAssociatorDoubling.v`) are
outside both scripts: their cube carrier needs the compiled open tree, and
the `comparison` cells of rows 75 and 81 mark that part owed. A row leaves
the plan's open work when its theorem is in the library; the table grows
with each tranche.

## Rows with no Lean reading

- Row 111, `rocq/open/theories/FloatRealBridge.v:float_quat_rotate_agrees`: the statement compares two Rocq definitions of the rotation (the FLOAT_OPS extraction route and Quaternion.v); the Lean side needs only the level-2 rows.
- Row 112, `rocq/quantum/CdSignPythonSemantics.v:cd_sign_returns_sigma`: a semantics of Python source is evidence about running code (AGENTS.md, Evidence axis); the Lean side meets the same function through ci/compare_signs.sh, which compares Tower.sign with cd_core.cd_sign.
- Row 113, `rocq/quantum/CdSignAstTranslation.v:function_semantic_preservation`: translation validation of a Python syntax tree, evidence about code with no algebraic content.
- Row 114, `rocq/quantum/SignBridge.v:open_cube_sign_sigma`: it identifies two Rocq spellings of one sign function; Lean holds one spelling, Tower.negSign, compared with them by ci/compare_signs.sh.
- Row 115, `rocq/quantum/TowerBridge.v:to_quantum_mul`: it relates two Rocq carriers of the same tower, and Lean has a single carrier, Tower R k; the reading the file can carry is its quantum_basis_product, which is Tower.e_mul_e through the sign dictionary (sign_exponent on cube_decode is negSign), so no row is owed.
- Row 116, `rocq/open/theories/CDSignNumericCorrespondence.v:numeric_cube_sign`: it relates a fuel-indexed numeric function of the open tree to the cube sign; Lean indexes by BitVec k with BitVec.toNat_xor, so no fuel or encoding enters.
- Row 117, `rocq/quantum/CdTowerLeibnizSystem.v:LeibnizSystem.system_solved`: the flat index j = 2^k m + q and the equation list are the input format of a Rocq certificate (MatrixSplittingCertificate.v); the Lean reading of the Leibniz rule is row derivation_by_basis.
- Row 118, `rocq/quantum/CdTowerCanonicalKernels.v:CanonicalKernels.W8_kernel_free_basis`: a generated certificate at fixed level 5 (Evidence axis); its general lemma is row kernel_free_basis, and the twelve point tables stay Rocq artifacts.
- Row 119, `rocq/quantum/CdTowerG2Derivations.v:G2Derivations.derivation_1`: a generated table checked by vm_compute (Evidence axis); the Lean reading of the 14 tables together is the dimension row of CdTowerG2DerivationSpan.v.
- Row 120, `rocq/quantum/A5W8ArcMatrixRanks.v:W8ArcMatrixRanks.w8_nm_linear_point1_columns_independent`: a fixed-matrix certificate (Evidence axis); its general lemma is row columns_independent.
- Row 121, `rocq/quantum/CdTwistedProduct.v:Twisted.W8_ideal_exchange`: a fixed 32-coordinate polynomial identity read by the Singular ideal of the A_5 W8 record; its general lemma is row ideal_exchange.
- Row 122, `rocq/open/theories/CDSparseBlockTransport.v:sparse_photonic_configuration_coverage`: membership in a retained configuration list is a record check (Evidence axis).

Rows 118 to 121 are certificates at a fixed level or matrix whose general
lemma is a Lean row (44, 43, 48 and 47), so each claim lands on both axes
and owes an instance bridge (`AGENTS.md`, "Statements and proofs"): a Rocq
theorem in a new file whose comment names the Lean theorem by path and name
and the values substituted for its parameters, and whose statement is the
substituted proposition. No such theorem exists at origin/main; the
`narrowing` cell of each row names the Lean partner and the substitution,
and the bridge lands with the partner row. The bridge of row 119 also
states the dimension 14 of the sedenion derivations as the instance
`k := 4`, `n := 14` of row 101.

Rows 100 and 101 state what their Rocq originals prove. Row 100 keeps the
premise `Hbackward` of the Rocq theorem as a hypothesis; Schafer's
unconditional Theorem 4 has no row. Row 101 is the linear-algebra step
from independent derivations and a spanning relation to the dimension, and
the value 14 stays with the Rocq tables.

These rows hold `-` in `lean_module`, `lean_statement` and `effort`, a
departure from the S, M or L of the brief that keeps a no-reading row from
looking like owed work.

Further rows carry a narrower Lean reading and say so in `narrowing`: row
35 (norm multiplicativity, levels 0 to 3 only),
row 70 (an inductive
predicate on nat read as a module statement), row 71 (the
abstract lane of Moreno's Theorem 1.16), row 96 (a group-cochain
identity read for the tower cochain), row 99 (a MathComp block
rank read as the kernel decomposition), and rows 39 and
45 (fixed levels over a class of rings).

## Census

The census read the headers and theorem statements of the sources that one
of three sweeps selected: the inventory of 2026-11-15 classing a source
every-level or ring-class; a keyword search (tower, Cayley, Dickson, sedenion,
octonion, pathion, CommutativeRing, Module Type, sigma_k, cube) over the
sources added since that inventory; and a search for a ring functor
(`CommutativeRing`, `OrderedDomain`, `RingHom`) or a level binder (`k`,
`order`, `n`, `dim`, `level` as a `nat` argument) next to a tower
operation. A source no sweep selected was not opened.
`rocq/open/verified/C956_TowerAssociatorPersistence.v`, added and then
deleted after the inventory commit, is absent from the tree.

Sources with rows (60):
`rocq/open/theories/BooleanANFDegree.v`, `rocq/open/theories/BooleanCochainFiltration.v`, `rocq/open/theories/Brown1972ChapterIII.v`, `rocq/open/theories/C1539_MorSkewSymm.v`, `rocq/open/theories/C1542_MorVlambdaOrbit.v`, `rocq/open/theories/C1543_MorMod4Bound.v`, `rocq/open/theories/CDAssociatorCensus.v`, `rocq/open/theories/CDAssociatorDoubling.v`, `rocq/open/theories/CDDoubleFunctor.v`, `rocq/open/theories/CDPhaseDegree.v`, `rocq/open/theories/CDPureDoublingKernel.v`, `rocq/open/theories/CDScalarExtension.v`, `rocq/open/theories/CDSignNumericCorrespondence.v`, `rocq/open/theories/CDSparseBlockTransport.v`, `rocq/open/theories/CDSparseMatrixTransport.v`, `rocq/open/theories/CDTowerFoldTransport.v`, `rocq/open/theories/CDTowerZeroDivisors.v`, `rocq/open/theories/Dickson1921.v`, `rocq/open/theories/DicksonCDProcess.v`, `rocq/open/theories/FinDimHModule.v`, `rocq/open/theories/FloatQuaternion.v`, `rocq/open/theories/FloatRealBridge.v`, `rocq/open/theories/HModuleDim.v`, `rocq/open/theories/HurwitzTheorem.v`, `rocq/open/theories/Moreno1997.v`, `rocq/open/theories/MorenoTowerInstance.v`, `rocq/open/theories/Schafer1954.v`, `rocq/open/theories/SchreierSignCode.v`, `rocq/open/theories/SignCodeCardinality.v`, `rocq/open/verified/C957_VoudonZD.v`, `rocq/quantum/A5W8ArcMatrixRanks.v`, `rocq/quantum/CdAnnihilatorSymmetry.v`, `rocq/quantum/CdAnnihilatorSymmetryReal.v`, `rocq/quantum/CdAssociatorAnf.v`, `rocq/quantum/CdAssociatorCensus.v`, `rocq/quantum/CdAssociatorPointIndicators.v`, `rocq/quantum/CdHalfFold.v`, `rocq/quantum/CdImaginarySumConference.v`, `rocq/quantum/CdSignAstTranslation.v`, `rocq/quantum/CdSignPythonSemantics.v`, `rocq/quantum/CdSignRowAnf.v`, `rocq/quantum/CdTowerBasisSign.v`, `rocq/quantum/CdTowerCanonicalKernels.v`, `rocq/quantum/CdTowerDomain.v`, `rocq/quantum/CdTowerDomainR.v`, `rocq/quantum/CdTowerDomainZ.v`, `rocq/quantum/CdTowerG2DerivationSpan.v`, `rocq/quantum/CdTowerG2Derivations.v`, `rocq/quantum/CdTowerKernelCertificate.v`, `rocq/quantum/CdTowerLeibnizSystem.v`, `rocq/quantum/CdTowerOrderThreeMap.v`, `rocq/quantum/CdTowerRing.v`, `rocq/quantum/CdTowerRingBaseChange.v`, `rocq/quantum/CdTowerRingBasis.v`, `rocq/quantum/CdTowerRingDomain.v`, `rocq/quantum/CdTwistedProduct.v`, `rocq/quantum/MatrixLeftInverseCertificate.v`, `rocq/quantum/MatrixSplittingCertificate.v`, `rocq/quantum/SignBridge.v`, `rocq/quantum/TowerBridge.v`.

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
- `rocq/open/theories/CDTraceZero.v`: `trace_zero_of_zd` (x pure and nonzero,
  x y = 0, so re(y) = 0) is `Tower.re_eq_zero_of_mul_eq_zero` with the case
  y = 0 trivial; the interface `CDAlgInnerTrace` has no Mathlib class.
- `rocq/open/theories/WedderburnPrimitive.v`: its `is_h_module_dim` lemmas are
  the arithmetic predicate of `FinDimHModule.v`, whose Lean reading is row
  69.
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
  `CDFidelity.v` (real inequalities about an associator norm it never
  computes), `RationalRealSpecialization.v`, `GF2Algebra.v`,
  `FP24Representable.v`, `BekensteinEntropy.v`, `Foliation.v`,
  `FanoPlane.v`, `ParityClique.v`, `SedenionXorGroup.v`, and
  `rocq/open/verified/C1141_ZDGraphCountingIdentities.v`,
  `C1141_ZDGraphGeneralStructure.v`, `C1142_XORScatterGatherSums.v`,
  `C1463_MatrixColumnIdeal.v`, `C882_OctahedronGraphSpectrum.v`,
  `C010_ComponentBridgeBound.v`, `C016_FanoOrientedTriples.v`,
  `C022_OrdinalAnalogy.v`, `C036_CliqueClusteringCounts.v`,
  `C1313_Thesis42Arithmetic.v`. Each has a Mathlib reading (Finset sums,
  `Submodule (ZMod 2)`, matrices, graphs, real inequalities) that no tower
  statement needs.
- Fixed level or fixed algebra, selected by the binder sweep:
  `rocq/open/theories/CDSignSection.v`, `ZDGraph.v`,
  `G2StabilizerDimension.v`, `BrownGeneralizedCD.v`, `Brown1972ChapterV.v`,
  `Brown1972ChapterVII.v`, `SStructuralGaps.v`, and
  `rocq/open/verified/C1137_MissingEdgeQuantizedGap.v`,
  `C1140_PathionQuantizedGap.v`, `C1466_SubalgebraClosure.v`,
  `C031_HurwitzComplete.v`.

## Checks

No Lean or Rocq command ran for this plan. A script checked the table: 11
cells per row, no tab or newline inside a cell, `order` contiguous, every
`depends` entry smaller than its row, every `statement` at most 30 words,
every `rocq` cell resolving to exactly one theorem of its file (the Moreno
1997 corollary by a direct search, since it sits in a section the extractor
skipped), and every `Tower.`, `CayleyDickson.` or `KernelMap.` name in
`lean_statement` and `reuses` either declared in `lean/GororobaMath/` or
introduced by a row in the transitive `depends` of its row.
