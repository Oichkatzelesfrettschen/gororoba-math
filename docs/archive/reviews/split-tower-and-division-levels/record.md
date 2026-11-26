# Review record: gororoba-math PR 132 (split tower and division levels)

## Scope

The pull request `rocq/split-doubling-tower` carries the split Cayley-Dickson tower with signature gamma (`rocq/quantum/SplitDoublingTower.v`, `rocq/open/verified/C1760_ParallelHalvesBridge.v`), the Lean module `DivisionLevels.lean` (associativity, alternativity and division at levels 0 to 3) and the claims-ledger rows they move. Two local review rounds ran on the owner's choice of reviewers, codex on gpt-daybreak-blue and agy on Gemini 4 Neon as red team, and the Advisor runs last.

| Round | Subject | Head reviewed |
|---|---|---|
| 1 | PR 132, split tower | ada1a9e8c |
| 2 | PR 133, `DivisionLevels.lean`, later folded into PR 132 | 03d71981f |

Fixes after the rounds: 82660baf2 (Rocq: invariant blade censuses, non-division, bridge file), 2743f9751 (merge of the Lean branch), 09d28a825 (Lean: unique solutions of a x = b and y a = b through level 3), 09b4a020e (claims rows). Every verdict below was read at 09b4a020e against the statement of the cited declaration (hypotheses, ring class, signatures covered, quantifiers), and each commit was found by `git log -S` on the declaration or ledger text.

Verdict codes: F is Fixed in the named commit, Rf is Refuted with the reason from the source, B is Boundary with the ledger row that records what stays open, U is Unaddressed (no fix, no refutation and no ledger note). Reports with no finding on a claim (C-808, C-812, C-632, C-549, C-807, C-811, C-910, C-921 (apart from R35) and the lions commentary row, the box-kite frustration row, C-582) and the failed attempted breaks on `mul_assoc_of_le_two`, `exists_mul_assoc_ne_iff`, `mul_eq_zero_of_le_three` and the ledger schema are not itemized.

## Items

| # | Reviewer item | Finding | Answer at 09b4a020e | Verdict |
|---|---|---|---|---|
| R1 | codex 132, claim 3 and defect 2 | C-1760 reads proved while no declaration joins sed_add (sed_e 1) (sed_e 9) with parallel_imaginary_halves | koebisu_e1_e9_is_parallel_halves and koebisu_e1_e9_trivial_kernel (C1760_ParallelHalvesBridge.v) stand in the proof column; the claim text asserts equal norms and a trivial left annihilator of e_1 + e_9 | F 82660baf2 (theorems), 09b4a020e (row) |
| R2 | codex 132, claim 2 and defect 3 | C-547 note does not say what the 128 counts | note: ordered pairs (x, y) of the 56 blades, x = y included, 128 = 52 + 52 + 24, all gamma = +1 over the integers; theorems split_octonion_ordered_zero_pairs (128), _forward_ (52), _reverse_ (52), _diagonal_ (24) | F 09b4a020e (note), 82660baf2 (theorems) |
| R3 | codex 132, claim 4 | "adds zero axioms" is false: CommRingNZ declares ring_th and one_neq_zero with Axiom | docstring: the Axiom fields are parameters of a module type that ZRing, ZEps and ZGauss prove; no Admitted or admit in the file | F 82660baf2 |
| R4 | codex 132, claim 4 (hypotheses) | empty kernel-assumption ledger and the three warning pairs are plausible but uncompiled | hosted rocq run green on 09b4a020e, which compares both lists | Rf: hypothesis confirmed by the gate; no defect |
| R5 | codex 132, defect 1 | C-631 note says 24 pair two such blades; proof column omits split_octonion_null_null_pairs | the declaration is in the C-631 proof column | F 09b4a020e |
| R6 | codex 132, conjecture 1 | 128 = 2 * 52 + 24 | split_octonion_ordered_zero_pairs, _forward_, _reverse_, _diagonal_ (each a vm_compute count) | F 82660baf2 |
| R7 | codex 132, conjecture 2 | sed_add (sed_e 1) (sed_e 9) = parallel_imaginary_halves | koebisu_e1_e9_is_parallel_halves | F 82660baf2 |
| R8 | codex 132, conjecture 3 | negative_entries is the psi = 1 count when each product is one basis vector with coefficient +-1 | split_octonion_products_signed_units, split_octonion_table_size, split_octonion_negative_fraction (8 * 24 = 3 * 64) | F 82660baf2 |
| R9 | agy 132, break 1 | the 52 pairs of C-631 test one product direction on i < j of the generation order, so the count depends on the list order | split_octonion_ordered_zero_pairs (128), _forward_ and _reverse_ (52 each), _unordered_zero_pairs (76), _unordered_null_null_ (24), _unordered_mixed_ (48), _unordered_proper_ (4); the file docstring states that 52 is not reorder-invariant | F 82660baf2 |
| R10 | agy 132, break 1 (residue) | whether the claim 48 null-involving and 4 proper equals an order-independent count | 48 null-involving is the forward count (24 with both blades null, 24 with one); the unordered census has 72 null-involving (24 + 48) and 4 proper; the C-631 note says the equality is open and the row is partial | B: ledger row C-631 (partial) |
| R11 | agy 132, break 2 gap 1 | non-division of the split quaternions and octonions is prose only | level2_not_division and level3_not_division state non-injectivity of left and of right multiplication by every nonzero a; rows C-808 and C-812 list them | F 82660baf2 (theorems), 09b4a020e (rows) |
| R12 | agy 132, break 2 gap 2 | zero-divisor hypotheses g 1 = 1 and g 2 = 1 miss signatures | level2_split_zero_divisor over g 0 = 1 or g 1 = 1 (three signatures), level3_split_zero_divisor over g 0, g 1 or g 2 = 1 (seven signatures), each with a b = 0 and b a = 0, over every CommRingNZ | F 82660baf2 |
| R13 | agy 132, break 3 | C-632 does not state single signed entries, the fraction, or more than one signature | split_octonion_products_signed_units, _table_size, _negative_fraction; the row and the claim are the all-plus tower | F 82660baf2 |
| R14 | agy 132, break 4 | C-547 note misdiagnoses 128 as unreproduced; the ordered count of the 56 blades is 128 | split_octonion_ordered_zero_pairs = 128; the row reads proved with the convention of R2 | F 82660baf2 (theorem), 09b4a020e (row) |
| R15 | agy 132, break 4 (secondary) | square_coeff reads coordinate 0 only | split_octonion_products_signed_units covers the 8 diagonal products: each has one nonzero coordinate, and coordinate 0 is +-1 in split_octonion_basis_squares, so coordinates 1 to 7 vanish | Rf: single-unit theorem plus the squares theorem state the whole square |
| R16 | agy 132, C-809 | note omits the H tensor C identification, the real embedding and non-division | C-809 is partial; the note names the associativity theorem, the Gaussian-integer zero divisor and the missing complex-over-real instance; no non-division theorem exists for the biquaternion tower | B: ledger row C-809 (partial) |
| R17 | agy 132, C-810 | one witness only; no general inheritance statement | C-810 is partial; the note names the single dual_quaternion_zero_divisor over the integer dual numbers and the missing real instance; the general inheritance over any coefficient ring with a zero divisor is unstated | B: ledger row C-810 (partial) |
| R18 | agy 132, break 5 (a) | five declarations across two files, no single one states C-1760 | the bridge file of R1 joins the two vector names; the row lists seven declarations that together state the claim | F 82660baf2, 09b4a020e |
| R19 | agy 132, break 5 (b) | left-kernel injectivity only; parallel_halves_left_square not cited; no right annihilator | the claim says trivial left annihilator; parallel_halves_trivial_kernel proves it through parallel_halves_left_square, which its proof applies | Rf: the claim names the left annihilator only |
| R20 | agy 132, break 5 (c) | ledger text of C-1760 is truncated; the full claim may add statements | the registry statement ends "e_1+e_9 has parallel imaginary halves and trivial left annihilator"; it asserts equal norms of the four vectors and nothing about zero divisors of the other three | Rf: full statement read |
| R21 | agy 132, claim 4 | SplitDoublingTower.v is out of alphabetical order in _RocqProject | the gate requires a listing, and no sort order | Rf |
| R22 | agy 132, claim 4 | docstring omits the blade-census convention | docstring states the 56 blades e_i +- e_j (i < j), the ordered and unordered counts and the status of 52 | F 82660baf2 |
| R23 | agy 132, claim 4 | the product mirrors cd_multiply_split of gororoba-open (named in the docstring) with no comparison under ci/ and no bridge to the CdTowerDomain tower at gamma = -1 | ci/compare_split_tower.sh with ci/compare_split_tower.py runs cd_multiply_split of cd_kernel and ZT.mul on 12 signatures (576 basis products, 4,352 coordinates), agrees, and rejects an evaluation with every gamma negated; SplitTowerStandardBridge.v proves ZT.mul at gamma = -1 equal to ZTower.mul on all elements of levels 2 and 3 (closed under the global context, rocq check passes in both modes) | F e6e3fb937 |
| R24 | agy 132, defect 1 | dead definition gq | definition removed | F 82660baf2 |
| R25 | agy 132, defect 2 | basis n p silently saturates for p >= 2^n | basis n p returns the zero vector for p >= 2^n and basis_out_of_range proves it | F 90a7e6fa0 |
| R26 | agy 132, defect 3 | commit text of a41e0b0fa counts rows | agy confirms the eight rows match; C-1760 moved in its own commit ada1a9e8c | Rf |
| R27 | codex 133, claim 1 | C-1794 reads proved with no declaration for the H_n and T_n formulas | row is partial; its note says no declaration evaluates the attributed formulas at n = 3 and 4 | F 09b4a020e |
| R28 | codex 133, claim 2 | C-578 note leaves only the nucleus open; the loop packaging is also unstated | note lists the unit, the inverses, the closure of the unit-norm subtype, the unique solutions of a x = b and y a = b, and the nucleus | F 09b4a020e |
| R29 | codex 133, defects | docstring of DivisionLevels.lean omits 2 != 0 and a nontrivial ring | docstring "Two nondegeneracy hypotheses"; exists_mul_assoc_ne_iff takes h2 : (2 : R) != 0 | F 09d28a825 |
| R30 | codex 133, claim 4 and agy 133, claim 4 (hypotheses) | warning-free build, axiom audit and replay unverified | hosted lean run green on 09b4a020e | Rf: gate run green; no defect |
| R31 | agy 133, claim 1 (C-910, C-1794) | rows cite no DivisionLevels.lean declaration for C-910, and none for C-1794 | C-910 cites left_alternative_three of Alternative.lean, the declaration of its statement; C-1794 is a Rocq row | Rf: a row cites the declarations that state its claim |
| R32 | agy 133, C-1794 break 1 | note recording the missing formulas was deleted | note restored, status partial | F 09b4a020e |
| R33 | agy 133, C-1794 break 2 | sorted_triple_classes decides associativity on the integer tower tz_mul 4; no listed theorem carries it to the real tower (the C-1792 row lists associates_at_tower) | the C-1794 proof column lists associates_at_tower and the note names the step from the integer tower tz_mul 4 to the real tower and the absence of a bridge to sed_mul | F b7152d2a7 |
| R34 | agy 133, C-807 gap and C-811 | two-sided inverses hold at every level and do not state division | existsUnique_mul_eq_of_le_three (ordered field K, k <= 3, a != 0: exactly one x with a x = b and exactly one y with y a = b) with the inverse laws normInv_mul_mul_of_le_three and mul_mul_normInv_of_le_three; rows C-807 and C-811 list them, and the C-811 note states the definition used | F 09d28a825 (theorem), 09b4a020e (rows) |
| R35 | agy 133, C-921 framing caveat | the parenthetical "property tower: second loss" (commutativity is the first loss, at dimension 4) is not stated by the listed theorems | the C-921 note and proof column carry mul_comm_of_le_one (levels 0 and 1) and exists_mul_comm_ne (level 2, 2 != 0) | F 3ed02c01d (theorems), b7152d2a7 (row) |
| R36 | agy 133, C-578 break 1 | loop axioms of the unit sphere are not stated | see R28 | F 09b4a020e |
| R37 | agy 133, C-578 break 2 | exists_mul_assoc_ne_iff does not restrict the triple to unit norm | the C-578 note says no declaration packages the unit-norm octonions as a loop, which covers the loop reading; the witness e_1, e_2, e_4 of octonion_e1_e2_e4_mul_assoc_ne is unit-norm by inspection and no theorem says so; the C-578 note now names that clause (exists_mul_assoc_ne_iff does not restrict its triple to unit norm) | F b7152d2a7 |
| R38 | agy 133, C-578 break 3 | middle Moufang parenthesization: the claim reads (a x)(y a) = (a(x y)) a, moufang_middle_three proves (x y)(z x) = x((y z) x) | the note states the proved form and the C-578 proof column lists flexible_three, which joins (a(x y)) a to a((x y) a) | F b7152d2a7 |
| R39 | agy 133, claim 3 | C-582 note cites the count theorem for u <= 8, a predicate of C029_octonion_subalgebra_iff | C029_octonion_subalgebra_count states exactly 8 members for the 15 planes; the u <= 8 form is its witness list | Rf |
| R40 | agy 133, defect 1 | public import of ZeroDivisors.lean is unused (named in prose only) | the public import of ZeroDivisors.lean is removed; the docstring names Tower.exists_zero_divisor as prose and the module builds with --wfail | F 3ed02c01d |
| R41 | agy 133, defect 2 | eq_zero_or_eq_zero_of_mul_eq_zero_of_le_three of SedenionCriterion.lean duplicates mul_eq_zero_of_le_three | both lemmas stand: eq_zero_or_eq_zero_of_mul_eq_zero_of_le_three of SedenionCriterion.lean is stated over a Field, mul_eq_zero_of_le_three over a partially ordered commutative ring without zero divisors, and the generality rule keeps the wider statement; SedenionCriterion.lean could call the wider lemma, which edits a second module | B: the lemmas differ in hypothesis class |
| R42 | agy 133, defect 3 | docstring says "ordered domain" for a weaker class | Main results states the exact class (partial order, ordered addition, no zero divisors, nonnegative squares); the intro prose keeps "ordered domain" | Rf: theorem hypotheses and the results list state the class |
| R43 | agy 133, defect 4 | ledger edits of Rocq rows ride in a Lean commit | the pull request title names rocq and lean; the rows moved are C-1794, C-578, C-582 and the box-kite row | Rf: scope of the pull request |
| R44 | agy 133, defect 5 | "nucleus equal to the real scalars" differs for the loop (nucleus {1, -1}) and the algebra | C-578 note: the nucleus clause is not stated; the loop-versus-algebra wording is not recorded | B: ledger row C-578 (partial) |
| R45 | codex 133, conjectures 1; agy 133, conjecture 3 | unit octonions as a Moufang loop; a nucleus theorem for level 3 | open clauses of the C-578 note | B: ledger row C-578 (partial) |
| R46 | codex 133, conjecture 3; agy 133, conjecture 4 | box-kite frustration minimum 3 and the 8 triangles of sign -1 | row octonion_structure_checks.md:15 kite frustration is partial and names both as not stated | B: that ledger row (partial) |
| R47 | agy 133, conjecture 1 | direct unique solvability for k <= 3 | existsUnique_mul_eq_of_le_three | F 09d28a825 |

Totals: 27 Fixed, 11 Refuted, 8 Boundary, 0 Unaddressed.

## Readings of the points checked with care

- C-631 (R9, R10). The row is partial and the note is exact. The forward census (pair i < j, product x y) gives 52 = 48 with a null-squaring blade (24 with both, 24 with one) + 4 without, as split_octonion_zero_product_pairs, _null_involving_pairs, _null_null_pairs and _proper_pairs. The order-independent census gives 76 unordered pairs (4 proper, 48 with exactly one null-squaring blade, 24 with both), 72 null-involving, and 128 ordered pairs. The claim words 48 and 4 therefore equal the forward count and not the unordered one.
- C-808 and C-812 (R11, R12). Level 2 covers the three signatures with g 0 = 1 or g 1 = 1, level 3 the seven with some g j = 1, over every commutative ring with 1 != 0, with a b = 0 and b a = 0. The not-division theorems state non-injectivity of left and right multiplication, which is non-division over a field only. The standard signature has none.
- C-578 (R36, R37, R38). The three Moufang laws hold at level 3 over every commutative ring; the middle law is stated as (x y)(z x) = x((y z) x). The packaging of unit-norm octonions as a loop, and the non-associativity inside the unit sphere, are not theorems; the note records the loop clause and not the sphere clause separately.
- C-807 and C-921 (R34, R35). existsUnique_mul_eq_of_le_three closes the division reading. The C-921 phrase on commutativity as the first loss has no theorem or note.
- existsUnique_mul_eq_of_le_three (R34). It is stated over a field K with StarRing, TrivialStar and a partial order with ordered addition and hsq : forall x, 0 <= x * x, for k <= 3. The real octonions are the instance K = the reals with hsq the square-nonnegativity of the reals; the rationals are another instance. No build here instantiates the real case.
- C-547 (R2, R14). The note states the ordered convention.

## Gates

| Check | Result |
|---|---|
| quick workflow on 09b4a020e (pull request run) | success |
| lean workflow, dispatched on 09b4a020e | success |
| rocq workflow, dispatched on 09b4a020e | success |

The rocq dispatch ran with ROCQ_CHECK_VM=1, the bytecode check, so the new vm_compute certificates of SplitDoublingTower.v are fully gated after a green pure re-check (a nightly run or a dispatch with kernel=pure). The pure re-check has not run on this head.

## Open items

- Boundary rows: C-631, C-809, C-810, C-578, the box-kite frustration row (R10, R16, R17, R37, R44 to R46).
- Pure re-check of SplitDoublingTower.v: owed.
- Conjectures that no ledger row or theorem records:
  - agy 132, conjecture 1: for every non-standard signature the level-n table has 2^(2n-1) - 2^n negative entries (24 at n = 3, 112 at n = 4); falsifier: count negative entries over all signatures at n = 3 and 4.
  - agy 132, conjecture 2: zero divisors of the coefficient ring or at one level lift to every higher level and signature (covers C-810 in general); falsifier: a ring with u v = 0 whose lifted pair has a nonzero product.
  - agy 132, conjecture 3: the ordered count is 128 for all seven non-standard level-3 signatures; falsifier: evaluate ordered_zero_count at the other six signatures.
  - codex 133 conjecture 2 and agy 133 conjecture 2: rings with 2 = 0 are associative at every level (docstring states it; no theorem does); falsifier: a nonzero associator over a ring with 2 = 0 at level 3 or more.
  - codex 133, conjecture 4: the shared line of two octonion planes spans their quaternionic intersection; falsifier: one plane pair whose four-index intersection is not product-closed.
