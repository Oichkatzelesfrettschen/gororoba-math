# Review report

The branch is clean at `577abfab8b023858622ef8c8073e5713eaa076cb`. The three new proofs support the intended ledger upgrades. Two review claims fail: the field hypotheses are stronger than the proofs need, and the stated counterexample does not establish that a field is necessary.

The review changed no file and ran no build. The supplied aarch64 build, axiom, and replay results remain separate evidence.

## Claims

### 1. Statements and proof generality — falsified

The theorem statements are correct, but two files use stronger structures than their proofs need.

- `AssociatorPhaseNonzero.lean` has appropriate hypotheses. The condition `(2 : R) ≠ 0` at [AssociatorPhaseNonzero.lean:76](lean/GororobaMath/CayleyDickson/AssociatorPhaseNonzero.lean:76) enters decisively through `two_zsmul_e_ne_zero` at lines 84 and 86. Characteristic two falsifies the equivalence because a phase-true associator becomes twice a basis element.

- `associator_add_associator_swap_of_anticomm` at [AnticommutingAssociator.lean:36](lean/GororobaMath/CayleyDickson/AnticommutingAssociator.lean:36) uses distributivity, an additive commutative group, multiplication, and zero. It never uses `1`. Mathlib’s `NonUnitalNonAssocRing` supplies exactly those operations, while `NonAssocRing` adds a unit in [Defs.lean:129](mathlib:Mathlib/Algebra/Ring/Defs.lean:129). The same proof therefore supports the wider nonunital class.

- All declarations in `SquareZero.lean` inherit `[Field F]` at [SquareZero.lean:43](lean/GororobaMath/CayleyDickson/SquareZero.lean:43). The main arguments need scalar cancellation and `mul_eq_zero`, rather than division. The existing `eq_zero_of_smul_eq_zero` provides scalar cancellation under `NoZeroDivisors` at [AnnihilatorSymmetry.lean:145](lean/GororobaMath/CayleyDickson/AnnihilatorSymmetry.lean:145). The inverse at [SquareZero.lean:63](lean/GororobaMath/CayleyDickson/SquareZero.lean:63) can be replaced by applying `re` to the scalar equation and cancelling the nonzero coefficient.

- `mul_self_eq_self_iff` at [SquareZero.lean:118](lean/GororobaMath/CayleyDickson/SquareZero.lean:118) already omits `(2 : F) ≠ 0`. Its module summary nevertheless places all results over fields with `2 ≠ 0` at lines 11–14.

The intended source claims over odd prime fields remain proved. The defect concerns the repository rule to state each theorem at the generality of its proof.

### 2. Necessity of the field hypothesis — falsified

The counterexample at [SquareZero.lean:20](lean/GororobaMath/CayleyDickson/SquareZero.lean:20) is correct when instantiated with a ring such as
\[
R=\mathbb{Q}[\varepsilon]/(\varepsilon^2).
\]
Here `2` is a unit, `ε ≠ 0`, and `x = ε • 1` satisfies `x² = 0` and `re x = ε ≠ 0`.

That example proves that an arbitrary commutative ring with `2` invertible is insufficient. It does not prove that a field is necessary.

A commutative ring with `NoZeroDivisors` and `(2 : R) ≠ 0` supports the same mechanism:

- scalar cancellation replaces the inverse in `eq_re_smul_one_of_smul_eq`;
- `mul_ne_zero` proves the coefficient `2 * re x` is nonzero;
- `mul_self_eq_zero` and `mul_eq_zero` handle the scalar square equations.

Thus a domain hypothesis suffices with the same proof idea. This generalization still requires compilation before it becomes formal evidence.

### 3. Resolution of `associator` — justified

Every unqualified occurrence resolves to `CayleyDickson.associator`, defined at [Associator.lean:47](lean/GororobaMath/CayleyDickson/Associator.lean:47).

- `AnticommutingAssociator.lean` imports `Associator` directly at [line 4](lean/GororobaMath/CayleyDickson/AnticommutingAssociator.lean:4).
- `SquareZero.lean` imports it directly at [line 4](lean/GororobaMath/CayleyDickson/SquareZero.lean:4).
- `AssociatorPhaseNonzero.lean` imports `Alternative` at [line 4](lean/GororobaMath/CayleyDickson/AssociatorPhaseNonzero.lean:4), and `Alternative` imports `Associator` at [Alternative.lean:4](lean/GororobaMath/CayleyDickson/Alternative.lean:4).

Each use also occurs inside `namespace CayleyDickson`. Mathlib’s root identifier cannot win that namespace lookup.

### 4. A5-649 proved status — justified

The pinned source row A5-649 states the formula for ordered imaginary basis triples at every \(D=2^n\ge4\).

The declarations cover each component:

- `associator_e_e_e_ne_zero_iff` identifies nonzero associators with phase-true triples at [AssociatorPhaseNonzero.lean:76](lean/GororobaMath/CayleyDickson/AssociatorPhaseNonzero.lean:76).
- `ne_zero_of_associator_e_e_e_ne_zero` proves that each counted index is nonzero at [line 90](lean/GororobaMath/CayleyDickson/AssociatorPhaseNonzero.lean:90). This closes the possible gap between all index triples and imaginary triples.
- `card_associator_e_e_e_ne_zero` gives the denominator-cleared count at [line 98](lean/GororobaMath/CayleyDickson/AssociatorPhaseNonzero.lean:98).
- The Rocq theorem gives the divided formula at [CDAssociatorCensus.v:322](rocq/open/theories/CDAssociatorCensus.v:322).

The source row is marked `char0`, so its coefficient rings cannot have `2 = 0`. The Lean result is stronger because it needs only `(2 : R) ≠ 0`. Its extra \(D=2\) instance does not weaken the required \(D\ge4\) claim.

The `proved` row at [ledger.tsv:1202](ci/claims/ledger.tsv:1202) is therefore sound.

### 5. Partial status of A5-622 and A5-661 — justified

A5-622 remains correctly partial at [ledger.tsv:1180](ci/claims/ledger.tsv:1180).

- `associator_e_add_associator_e_swap` proves the first identity without division at [AnticommutingAssociator.lean:61](lean/GororobaMath/CayleyDickson/AnticommutingAssociator.lean:61).
- `star_mul_mul_sub_eq` states the left-associator defect at [AlternativeIdentities.lean:219](lean/GororobaMath/CayleyDickson/AlternativeIdentities.lean:219).
- `toMatrix_mulLeft_star` identifies the transpose with conjugate left multiplication at [LeftMulMatrix.lean:46](lean/GororobaMath/CayleyDickson/LeftMulMatrix.lean:46).

Only the identifications with the coordinates and operators of the A5-612 slice remain open, exactly as the note says.

A5-661 remains correctly partial at [ledger.tsv:1216](ci/claims/ledger.tsv:1216). The three new theorems cover the square-zero characterization, fourth-power implication, and idempotent characterization. The pinned source’s seven enumerated counts remain the only uncovered clauses.

### 6. Ledger counts and proof names — justified

A direct tab-separated count gives:

- 14 `lean, owed`
- 18 `lean, partial`
- 2 `lean, proved`
- 1 `both, owed`
- 195 `none, no-proof-owed`
- 405 `rocq, owed`
- 9 `rocq, partial`
- 2 `rocq, proved`

The total is 646 rows. These values match [ci/claims/README.md:78](ci/claims/README.md:78).

All fourteen proof entries across the three rewritten rows resolve to declarations. The new root imports are present at [GororobaMath.lean:21](lean/GororobaMath.lean:21) and [GororobaMath.lean:79](lean/GororobaMath.lean:79).

### 7. Proof hygiene — justified

- The only nonterminal `simp` calls are the two `simp only` calls at [SquareZero.lean:55](lean/GororobaMath/CayleyDickson/SquareZero.lean:55).
- Plain `simp` calls in the other modules terminate their current branch or nested proof.
- The modules set no file-wide option.
- Each module docstring states its product, basis, associator, or trace convention before presenting results.
- The new files contain no `sorry`, `native_decide`, or `debug.skipKernelTC`.
- `git diff --check origin/main...HEAD` reports clean output.

## Further defects

1. The sentence at [AssociatorPhaseNonzero.lean:19](lean/GororobaMath/CayleyDickson/AssociatorPhaseNonzero.lean:19) says that a triple containing index zero has zero associator, “so every such triple is a triple of imaginary units.” Read literally, the conclusion contradicts its premise. The intended subject is “every nonzero-associator triple.”

2. The field-necessity sentence in `SquareZero.lean` overclaims what its example establishes. It should identify failure of scalar cancellation or zero divisors, rather than necessity of a field.

3. Current-head kernel replay remains a validation gap. The supplied replay of `AnticommutingAssociator.lean` predates its explicit `Associator` import. Static name resolution is sound, but the full gate on `577abfab8` remains the decisive current-head check.

## Conjectures and unrecorded corollaries

Scoped searches of the branch and pinned findings ledger found no declaration or row stating these forms.

1. **Domain-level square-zero and idempotent classification.**  
   Replace `Field F` with `CommRing F`, `NoZeroDivisors F`, `StarRing F`, and `TrivialStar F`; retain `(2 : F) ≠ 0` for the first two main results.

   Falsifier: a domain and tower element violating one of the three conclusions.  
   Cheapest test: restate `eq_re_smul_one_of_smul_eq` with cancellation through `eq_zero_of_smul_eq_zero`, then compile the unchanged main proof structure.

2. **A5-662 over every odd finite field.**  
   For a finite field of odd cardinality \(q\), the expected counts are
   \[
   q^{2^n-2}
   \]
   for square-zero elements and
   \[
   q^{2^n-2}+q^{2^{n-1}-1}
   \]
   for nontrivial idempotents, for \(n\ge2\). This strengthens A5-662 from prime fields to prime-power fields.

   Falsifier: \(A_2\) over \(\mathbb F_9\) has counts other than 81 and 90.  
   Cheapest test: enumerate its \(9^4=6561\) elements, then formalize the odd-dimensional diagonal-quadric point count with the sign at \(c=-1/4\).

3. **Repeated squaring stabilizes at square zero.**  
   Over the SquareZero hypotheses, an iterated square \(x^{2^m}\) vanishes for some \(m\ge1\) exactly when \(x^2=0\), using recursively bracketed squaring.

   Falsifier: an element with a higher iterated square zero and \(x^2\ne0\).  
   Cheapest test: define recursive squaring and induct with `mul_self_eq_zero_of_mul_self_mul_mul_self_eq_zero`.

4. **Nonzero associator support is binary-linearly independent.**  
   A nonzero basis associator should imply that its three indices are nonzero, pairwise distinct, and satisfy \(p\mathbin{\mathrm{xor}}q\ne x\). These are the elementary \(\mathbb F_2\)-independence conditions for three vectors.

   Falsifier: a nonzero associator with a zero index, a repeated index, or \(p\mathbin{\mathrm{xor}}q=x\).  
   Cheapest test: combine `associator_e_e_e_ne_zero_iff` with `assocPhase_eq_false_of_dependent` at [AssociatorPhase.lean:162](lean/GororobaMath/CayleyDickson/AssociatorPhase.lean:162).

## Verdict

The branch correctly advances A5-649 to `proved` and narrows the open portions of A5-622 and A5-661. The mathematical results needed by those rows are sound. The branch still violates the repository’s generality rule in `SquareZero.lean` and the generic anticommuting theorem, and `SquareZero.lean` states an incorrect necessity claim. These points warrant revision before merge; the final full gate must then validate the amended head.