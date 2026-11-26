**Scope**
- `[computed]` Head `3978afe349dfb4aac198157318f4dfb650634a14` has parent `152112929809c2ba9ada4ab72b653b23f1119827`; `git diff --name-status origin/main...3978afe34` reports only `lean/GororobaMath.lean:82` and `lean/GororobaMath/EisenbudGoto/MinimalMultiplicity.lean:1`.
- `[computed]` `git diff --check origin/main...3978afe34` reports no whitespace defects.
- `[computed]` The diff contains none of `sorry`, `native_decide`, `debug.skipKernelTC`, declared axioms, or implementation overrides.
- `[hypothesis]` Proof acceptance remains unverified. The brief prohibited the Lean build, axiom audit, and kernel replay that the repository requires for a proved verdict.

**Claim 1**
**Verdict: falsified as written by its blanket quantifier; the listed statements otherwise appear in the source with the scopes below.**

- `[proved]` `coeff_hilbertSeries` states the coefficient formula over every commutative ring and all natural `c`, `d`, and `n`: the coefficient at degree `n + 1` equals `C(d+n+1,d) + c C(d+n,d)`. See `lean/GororobaMath/EisenbudGoto/MinimalMultiplicity.lean:78`.
- `[proved]` `eval_hilbertPoly` states agreement over every characteristic-zero field and all natural `c`, `d`, and `n`. Its evaluation argument is `n + 2`, which parameterizes every natural degree at least two. See `lean/GororobaMath/EisenbudGoto/MinimalMultiplicity.lean:94`.
- `[proved]` `betti_identity` states
  `j C(c+1,j+1) = c C(c,j) - C(c,j+1)`
  over the integers for every natural `c` and `j`. See `lean/GororobaMath/EisenbudGoto/MinimalMultiplicity.lean:106`.
- `[proved]` `numerator_eq` states the claimed polynomial identity, with the sum packaged by `numerator`. See `lean/GororobaMath/EisenbudGoto/MinimalMultiplicity.lean:156` and `lean/GororobaMath/EisenbudGoto/MinimalMultiplicity.lean:161`.
- `[proved]` `alternating_betti` requires `1 ≤ c`; it does not hold for every `c`. At `c = 0`, the displayed sum is `1`, not `0`. See `lean/GororobaMath/EisenbudGoto/MinimalMultiplicity.lean:188`.
- `[proved]` `eisenbudGoto_numbers_two` also requires `1 ≤ c`. At `c = 0`, its first equality would read `0 = C(1,0) = 1`. See `lean/GororobaMath/EisenbudGoto/MinimalMultiplicity.lean:195`.
- `[computed]` A bounded independent AWK sweep checked the Betti identity’s polynomial consequences, numerator coefficients, and alternating sum for `1 ≤ c ≤ 20`; it printed `checked c=1..20; failures=0`.

**Claim 2**
**Verdict: the \(p=2\) specialization is justified; the claimed match to the printed 1984 pages remains unverified and therefore the compound claim is not fully justified.**

- `[hypothesis]` The authorized tree contains no copy, transcription, or retained page image of Eisenbud–Goto 1984. Repository search found only the module’s own secondary citation at `lean/GororobaMath/EisenbudGoto/MinimalMultiplicity.lean:17`. The wording and formulas on journal pages 100 and 104 therefore remain unchecked against the primary source.
- `[proved]` Assuming the general Betti formula supplied in the brief,
  \[
  \binom{c+p-1}{q+p-1}\binom{q+p-2}{p-1},
  \]
  substitution of \(p=2\) gives
  \[
  \binom{c+1}{q+1}\binom q1
  =q\binom{c+1}{q+1},
  \]
  exactly the definition of `betti` at `lean/GororobaMath/EisenbudGoto/MinimalMultiplicity.lean:70`.
- `[proved]` At \(q=1\), the generator count becomes \(\binom{c+1}{2}\). The Lean statement uses \(\binom{c+1}{c-1}\), and its proof invokes binomial symmetry after writing \(c=(c-1)+1\). See `lean/GororobaMath/EisenbudGoto/MinimalMultiplicity.lean:195` and `lean/GororobaMath/EisenbudGoto/MinimalMultiplicity.lean:198`.
- `[proved]` The multiplicity specialization is
  \(\binom{c+1}{c}=c+1\), exactly the second conjunct at `lean/GororobaMath/EisenbudGoto/MinimalMultiplicity.lean:196`; the source uses `Nat.choose_succ_self_right` at `lean/GororobaMath/EisenbudGoto/MinimalMultiplicity.lean:203`.
- `[computed]` The same AWK sweep compared the supplied \(p=2\) Betti formula with `q * C(c+1,q+1)`, and compared both displayed generator and multiplicity forms, for `1 ≤ c ≤ 20`; it found zero failures.

**Claim 3**
**Verdict: falsified as a claim about derivation; the numerical values are correct.**

- `[proved]` `e8_hilbertFn` is proved by `decide` directly on the decidable equality containing `hilbertFn 6 3`; its proof does not instantiate `coeff_hilbertSeries` or `eval_hilbertPoly`. See `lean/GororobaMath/EisenbudGoto/MinimalMultiplicity.lean:207`.
- `[proved]` `e8_betti` is likewise proved by `decide` directly on values of `betti 6`; its proof does not instantiate `numerator_eq`, `betti_identity`, or `eisenbudGoto_numbers_two`. See `lean/GororobaMath/EisenbudGoto/MinimalMultiplicity.lean:212`.
- `[computed]` An independent AWK evaluation of the definitions produced:
  `hilbertFn: 10 34 80 155 266 420 624 885`
  and
  `betti: 21 70 105 84 35 6`.
- `[proved]` The concrete theorems use the same definitions as the general theorems, so a kernel-accepted disagreement would be impossible. The source nevertheless contains separate computations rather than explicit specialization proofs. A derivational bridge would rewrite each concrete term with the relevant general theorem before closing the remaining numeral equality.

**Claim 4**
**Verdict: not justified in this checkout; it remains a hypothesis rather than a falsified claim.**

- `[computed]` `ls -ld lean/.lake lean/.lake/packages/mathlib` reports that all three paths are absent.
- `[proved]` The module asserts that Mathlib v4.35.0 lacks graded Cohen–Macaulay theory, graded depth and regular sequences, Castelnuovo–Mumford regularity, minimal graded free resolutions, graded Betti tables, Eagon–Northcott, and graded-module multiplicity. See `lean/GororobaMath/EisenbudGoto/MinimalMultiplicity.lean:40`.
- `[hypothesis]` The package tree required to test those assertions is unavailable under the path authorized by the brief. The manifest pins Mathlib v4.35.0, but a lock entry contains no searchable source definitions. Each absence claim therefore remains unverified.

**Defects Beyond The Claims**
- **SLOPPY — `[proved]` Off-by-one documentation.** The `hilbertFn` docstring says the formula `C(d+n,d) + c C(d+n-1,d)` is evaluated “at `n + 1`,” while the definition actually returns `C(d+n+1,d) + c C(d+n,d)`. The main-result summary and theorem use the latter, correct shift. Rewrite the docstring with the implemented expression or describe the generic degree as a separate variable. See `lean/GororobaMath/EisenbudGoto/MinimalMultiplicity.lean:72`.
- **COSMETIC — `[computed]` Opaque instance name.** Repository search finds `e8_hilbertFn` and `e8_betti` only in this module and its summary; the source never defines what `e8` denotes. Names such as `c6_d3_hilbertFn` and `c6_betti`, or one sentence explaining `e8`, would preserve durable meaning. See `lean/GororobaMath/EisenbudGoto/MinimalMultiplicity.lean:207` and `lean/GororobaMath/EisenbudGoto/MinimalMultiplicity.lean:212`.
- **SOUND — `[proved]` Registry coverage.** The new module is imported by the library root at `lean/GororobaMath.lean:82`. It is absent from the headline registry because the README’s Lean-library table does not name it, and the claims ledger governs claims imported from gororoba-open and gororoba-quantum rather than every local theorem.
- **SOUND — `[computed]` Source hygiene.** The diff is clean under `git diff --check`, and the new proof source introduces no textually visible trust-base escape.

**Conjectures**
- `[hypothesis]` **General \(p\)-linear numerator identity.** For \(c,p\ge1\), define
  \[
  h_{c,p}(t)=\sum_{i=0}^{p-1}\binom{c+i-1}{i}t^i.
  \]
  The \(p=2\) theorem at `lean/GororobaMath/EisenbudGoto/MinimalMultiplicity.lean:161` suggests
  \[
  (1-t)^c h_{c,p}(t)
  =
  1+\sum_{q=1}^{c}(-1)^q
  \binom{c+p-1}{q+p-1}
  \binom{q+p-2}{p-1}
  t^{q+p-1}.
  \]
  **Falsifier:** one coefficient mismatch for any explicit \(c,p\), or a symbolic coefficient calculation that leaves a nonzero difference.
- `[hypothesis]` **General ambient-degree decomposition.** The quadratic identity at `lean/GororobaMath/EisenbudGoto/MinimalMultiplicity.lean:119` suggests
  \[
  \sum_{i=0}^{p-1}
  \binom{c+i-1}{i}\binom{d+p-i}{d}
  +\binom{c+p-1}{c-1}
  =
  \binom{c+d+p}{p}.
  \]
  This states that the degree-\(p\) quotient dimension plus the number of degree-\(p\) generators equals the ambient degree-\(p\) dimension. **Falsifier:** a natural triple \(c,d,p\ge1\) for which the two sides differ.
- `[hypothesis]` **Instance-bridge strengthening.** The concrete results can be restated for coefficients of `hilbertSeries` and the polynomial numerator, then proved by instantiating the universal theorems followed by finite arithmetic. **Falsifier:** an index or coefficient-type mismatch that prevents the universal statements from rewriting the concrete goals without an additional mathematical assumption.