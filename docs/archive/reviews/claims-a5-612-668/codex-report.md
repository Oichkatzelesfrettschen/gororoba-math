# PR 151 review

Verdict: changes required. Claims 1, 3, and 6 are justified. Claims 2, 4, and 5 are falsified. Claim 7 contains one mixed-axis placement error and two clause errors.

The review read PR head `5d768cc7e224e8ce734e7e470a5e2f62b064c5f5`, `origin/main...HEAD -- ci/claims`, and the findings ledger at `gororoba-quantum@6d2cdac90`. The worktree remained clean.

## 1. Added source locators and statements

Justified.

A direct comparison reconstructed the first 30 whitespace-separated words of each pinned source claim and compared them with the 57 added ledger rows. It found 57 rows and zero locator or statement mismatches.

The source rows occupy two ranges because A5-638 through A5-645 occur earlier in the findings file:

- A5-638..A5-645: pinned source lines 528–534; [ledger.tsv:1091](ci/claims/ledger.tsv:1091).
- A5-612..A5-637 and A5-642..A5-668: pinned source lines 598–647; [ledger.tsv:1168](ci/claims/ledger.tsv:1168).

Every longer statement ends in `...`; every uncut statement contains at most 30 words.

## 2. Quantifier, placement, clause, and status

Falsified.

Most classifications follow the findings rule in [README.md:69](ci/claims/README.md:69). The refuted, superseded, and open rows correctly use `none / no-proof-owed`. The fixed certificates generally use Rocq, and the general tower claims generally use Lean.

Four rows break the semantic rules:

1. **A5-622 reads `owed`, but existing Lean declarations prove part of it.**  
   [ledger.tsv:1180](ci/claims/ledger.tsv:1180) says that no proof is held. `star_mul_mul_sub_eq` states
   \[
   \bar x(xy)-N(x)y=(x^2)y-x(xy),
   \]
   the associator part of the claimed Gram identity, at every level: [AlternativeIdentities.lean:217](lean/GororobaMath/CayleyDickson/AlternativeIdentities.lean:217). `toMatrix_mulLeft_star` identifies \(L_{\bar x}\) with \(L_x^T\): [LeftMulMatrix.lean:43](lean/GororobaMath/CayleyDickson/LeftMulMatrix.lean:43). Together they state the second identity of A5-622. The row must read `partial`.

2. **A5-648 reads `owed`, but both proof trees already state its cochain equality.**  
   [ledger.tsv:1201](ci/claims/ledger.tsv:1201) overlooks `Tower.amExponent_eq`, which defines the Albuquerque–Majid exponent and proves `amExponent k a b = negSign k b a` for every level: [SignLaws.lean:64](lean/GororobaMath/CayleyDickson/SignLaws.lean:64). Rocq states the signed equality explicitly in `am_sign`: [CdTowerBasisSign.v:383](rocq/quantum/CdTowerBasisSign.v:383). The opposite-quasialgebra and quasigroup consequences remain open, so the row must read `partial`.

3. **A5-633 overlooks a fixed-level generation result.**  
   [ledger.tsv:1192](ci/claims/ledger.tsv:1192) reads `owed`. The eight matrices are left multiplication by the \(A_4\) units \(e_1,\ldots,e_8\): [ZeroEight.lean:9](lean/GororobaMath/Clifford/ZeroEight.lean:9). Their 256 monomials are linearly independent, and their generated algebra maps surjectively onto \(M_{16}(\mathbb R)\): [ZeroEight.lean:259](lean/GororobaMath/Clifford/ZeroEight.lean:259), [ZeroEight.lean:287](lean/GororobaMath/Clifford/ZeroEight.lean:287). This is the fixed \(n=4\) part of the generation claim. The rational formulation and all-level result remain open, so `partial` is the calibrated status.

4. **A5-623 belongs on both axes.**  
   [ledger.tsv:1181](ci/claims/ledger.tsv:1181) combines finite \(A_5\) nullity certificates with a bound over every field of characteristic zero or above 32. The former belongs in Rocq; the latter is a field-class Lean theorem. The repository rule requires both artifacts for such a compound claim: [AGENTS.md:257](AGENTS.md:257), [AGENTS.md:290](AGENTS.md:290). Its placement should be `both`, with the `Both axes` clause.

## 3. Five partial rows and their declarations

Justified.

- **A5-627.** `finrank_ker_mulLeft_e_add_e` proves nullity equals aligned-pair count at every level under left-regularity of 2; the characteristic-zero theorem supplies that hypothesis over fields: [TwoTermNullity.lean:414](lean/GororobaMath/CayleyDickson/TwoTermNullity.lean:414), [TwoTermNullity.lean:462](lean/GororobaMath/CayleyDickson/TwoTermNullity.lean:462). Neither declaration evaluates the 225 cross-half \(A_5\) pairs. The note at [ledger.tsv:1186](ci/claims/ledger.tsv:1186) is accurate.

- **A5-629.** The five declarations prove the generic Gram identity, its conjugate-transpose form, the kernel fixed-space equivalence, and their \(e_1,\ldots,e_8\) instances: [AnticommutingPairGram.lean:50](lean/GororobaMath/Clifford/AnticommutingPairGram.lean:50), [AnticommutingPairGram.lean:66](lean/GororobaMath/Clifford/AnticommutingPairGram.lean:66), [AnticommutingPairGram.lean:81](lean/GororobaMath/Clifford/AnticommutingPairGram.lean:81), [AnticommutingPairGram.lean:117](lean/GororobaMath/Clifford/AnticommutingPairGram.lean:117), [AnticommutingPairGram.lean:134](lean/GororobaMath/Clifford/AnticommutingPairGram.lean:134). The module docstring explicitly lists the missing half-dimension, complement, and \(A_5\) conclusions at lines 23–29. The note is accurate.

- **A5-649.** `card_assocPhase_true` counts phase-true triples: [AssociatorCensus.lean:366](lean/GororobaMath/CayleyDickson/AssociatorCensus.lean:366). `e_mul_e_mul_e` states the sign change: [AssociatorPhase.lean:108](lean/GororobaMath/CayleyDickson/AssociatorPhase.lean:108). Rocq gives the divided count: [CDAssociatorCensus.v:313](rocq/open/theories/CDAssociatorCensus.v:313). A declaration equating phase truth with a nonzero associator under the required coefficient hypothesis remains absent. `partial` is correct.

- **A5-658.** The three theorems prove sign change under each transposition of pure arguments, at every level over a commutative ring with trivial star: [MultiplicationForms.lean:91](lean/GororobaMath/CayleyDickson/MultiplicationForms.lean:91). They do not state the doubling-unit Gram identity. The note is accurate.

- **A5-661.** `mul_self_eq_smul_sub` proves the quadratic relation at every level: [Associator.lean:171](lean/GororobaMath/CayleyDickson/Associator.lean:171). It does not state the finite-field characterizations or enumerated counts. The note is accurate.

## 4. Owed rows versus declarations already on main

Falsified.

A5-622 and A5-648 are decisive counterexamples. A5-633 supplies a third fixed-level overlap. Their evidence appears under claim 2.

The focused searches found no declaration stating the reviewed identities of A5-612, A5-613, A5-624, A5-625, or A5-636. In particular:

- `Clifford.ZeroEight.cliffordEquivMatrix` uses the \(A_4\) generators \(e_1,\ldots,e_8\), not the different \(A_5\) generator set of A5-625.
- `Tower.negSign_cons_eq` supplies the recursion from which A5-636 could start, but it does not state the claimed commutation set or the two slice families.

## 5. Relocations and eight changed source rows

Falsified by one stale note.

The structural portion holds:

- 63 existing ledger rows changed field 1 only, their source line locator.
- A5-151, A5-544, and A5-548 changed only their note.
- A5-546 changed its statement and note.
- A5-026, A5-315, A5-560, and A5-598 required no statement or note change.

A5-548 nevertheless overstates its updated source. Its note says “the nine cells agree at 32009, 32029 and 32057”: [ledger.tsv:1090](ci/claims/ledger.tsv:1090). The pinned source at line 527 says the 32057 run covers six cells, while A5-560 at pinned line 546 enumerates those six. The source reaches nine cells over \(\mathbb Q(i)\), after A5-641, rather than at every listed prime. The note should distinguish:

- retained cells at 32009 and 32029;
- six cells at 32057;
- all nine cells over \(\mathbb Q(i)\).

## 6. Expected sources and README counts

Justified.

A semantic comparison by findings label gives:

- 57 added findings sources;
- zero removed sources;
- 61 existing rows with source-line and commit changes only;
- two rows, A5-560 and A5-598, with source-line, commit, and digest changes;
- six rows, A5-026, A5-151, A5-315, A5-544, A5-546, and A5-548, with commit and digest changes;
- 520 remaining findings rows with a commit change only;
- zero changed gororoba-open, topic-note, or scratch-analysis sources.

Thus the digest changes occur at exactly the eight named rows. The new pin appears at [expected_sources.py:66](ci/claims/expected_sources.py:66). The added entries appear at [expected-sources.tsv:1091](ci/claims/expected-sources.tsv:1091) and [expected-sources.tsv:1168](ci/claims/expected-sources.tsv:1168).

The ledger counts equal the README:

- 646 findings rows.
- Lean: 18 owed, 15 partial, 1 proved.
- None: 195 no-proof-owed.
- Rocq: 406 owed, 9 partial, 2 proved.
- 201 rows in the complete ledger use the “source does not assert” clause.

The published counts appear at [README.md:69](ci/claims/README.md:69) and [README.md:99](ci/claims/README.md:99).

## 7. Uncertain placements

| Rows | Judgment | Deciding clause |
|---|---|---|
| A5-630, A5-631 | Keep `fixed-dimension 32 / none / no-proof-owed`. Each row asserts behavior of a circuit builder or exact statevector implementation. The separate algebraic complement law belongs to A5-629. | Outside the clauses: physics, software, data or measurement |
| A5-657 | Keep `fixed-dimension 32 / none / no-proof-owed`. The unnamed “invariant of the strata record” leaves no formal proposition. | Outside the clauses: analogy or interpretation |
| A5-667 | Keep `fixed-dimension 32 / lean / owed`. The claim ranges over every real point of W8; its finite scan is evidence rather than the theorem. | Statement of real or complex analysis: Lean on Mathlib |
| A5-622 | Keep placement `lean`, but use quantifier `other`, status `partial`, and preferably the existing-proof clause. The source states finite levels; main already proves the general Gram/associator identity. | Result already in a proof tree stays where it is |
| A5-658 | Keep placement `lean`, quantifier `other`, and `partial`. Its existing general Lean theorem is stronger than the finite-level alternating-form clause in the source. | Result already in a proof tree stays where it is |
| A5-616, A5-619, A5-626, A5-637, A5-664 | Keep `other / rocq`. These are finite censuses or direct checks across several named levels, rather than quantified every-level claims. | Certificate evaluated by `vm_compute` or extracted code: Rocq |
| A5-663 | Keep `fixed-dimension 8 / rocq`. The fixed coefficient algebra is the octonions; the \(J_3(O)\) system and stabilizers are exact rank certificates derived from that algebra. | Certificate evaluated by `vm_compute` or extracted code: Rocq |
| A5-623 | Change to `ring-class / both / owed`. The fixed-prime nullities require Rocq certificates, while the bound over every field of characteristic zero or above 32 requires Lean. | Both axes: general Lean theorem and Rocq certificate |
| A5-649 | Keep `every-level / lean / partial`. The declarations count phase-true triples and state the sign reversal, but no declaration states the required equivalence with nonzero associators. | Statement over every level or ring class: Lean on Mathlib |

## Further defects

- The A5-648 note says that “no declaration defines the cochain F.” `Tower.amExponent` does exactly that, and `Tower.amExponent_eq` proves its equality with the transposed tower sign. The note contradicts [SignLaws.lean:64](lean/GororobaMath/CayleyDickson/SignLaws.lean:64).
- A5-633 omits the existing \(n=4\) matrix-generation result from its note and proof column.
- The semantic defects survive the mechanical ledger gate because the gate validates declaration existence and column rules; it does not establish that the declarations exhaust or match each claim.

## Conjectures

1. **One operator identity may organize the null-slice cohort.**  
   A5-612, A5-622, A5-623, A5-635, and the transition rows A5-650..A5-668 appear to specialize
   \[
   L_y^T L_y=N(y)I+\operatorname{Assoc}(y,y,-).
   \]
   The slice-specific spectra and nullity transitions may therefore be rank strata of one associator operator rather than separate mechanisms.  
   **Falsifier:** a retained Gram polynomial or transition rank that differs from the specialization of `star_mul_mul_sub_eq` and `toMatrix_mulLeft_star`.  
   **Cheapest test:** specialize those declarations to the A5-612 basis slice and compare the resulting matrix entries with the retained integer matrix record.

2. **The compression commutant may determine the full Lie closure.**  
   A5-654, A5-659, A5-666, and A5-667 suggest the sequence
   \[
   \mathbb R\mapsto\mathfrak{so}(8),\quad
   \mathbb C\mapsto\mathfrak{su}(4),\quad
   \mathbb H\mapsto\mathfrak{sp}(2),
   \]
   with the Lie closure equal to the full skew centralizer of the compression commutant. The quaternionic limiting-kernel sphere may occur exactly on the \(\mathbb H\) locus.  
   **Falsifier:** a point with the same commutant but a smaller Lie closure, a non-division commutant, or a quaternionic point whose limiting planes leave the stated sphere.  
   **Cheapest test:** compute commutant multiplication and Lie-closure ranks on the existing exact four-term W8 census, then run kernel-limit certificates on one representative of each type.

3. **The slice-change scalars may form a descent cocycle.**  
   A5-638..A5-647 supply header, weight, sign, and module maps whose normalized scalars are \(i/2\), \(1/2\), \(-1/2\), \(-1\), and \(1\). Their products may encode a single cocycle for changing presentation, with the sign of A5-647 as its orientation character.  
   **Falsifier:** a closed composition of retained header/weight/sign maps that is not scalar identity, or whose scalar differs between the three split primes.  
   **Cheapest test:** multiply the retained transformation matrices around one closed loop at 32009 and compare the normalized product with the identity; repeat at 32029 as the independent check.