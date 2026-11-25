**Executive Verdict**
- Claim 1 is justified.
- Claim 2 is falsified as written only in its description of the standalone flip; the stated equations and ideal equalities are justified.
- Claim 3 is partly justified; the heartbeat scopes and unchanged theorem strength are established, while necessity remains a hypothesis.
- Claims 4 and 5 are justified.
- Two documentation defects and one calibration gap remain.

**Claim 1 — Generator Lists**
- **Justified — computed.** The Singular ring fixes the variable order as `(i,s1,s2,s3,s4,s5,s6,s7,s8,s9)` at `gororoba-quantum/docs/evidence/a5-exceptional-fibers/working/runs/e8-rees-fibers-v3-open-cells/conjugation/conjugation_map.sing:2`.
- The two `ideal J=` literals occur at `conjugation_map.sing:146` and `conjugation_map.sing:290`; each contains 27 generators.
- The Lean definitions contain 27 `jmGen` declarations beginning at `lean/GororobaMath/CayleyDickson/E8ConjugationIdeal.lean:43`, and 27 `jpGen` declarations beginning at `lean/GororobaMath/CayleyDickson/E8ConjugationIdeal.lean:220`. Their vectors begin at `lean/GororobaMath/CayleyDickson/E8ConjugationIdeal.lean:189` and `lean/GororobaMath/CayleyDickson/E8ConjugationIdeal.lean:365`.
- A read-only AWK comparison split each polynomial into signed monomials, sorted the monomials within each indexed generator, and hashed the resulting 54-row streams. Both streams produced `4e3557af7dc45a7532bf35e1f30a8b91b241dab585643bd807a2922eb74b0018`.
- The source file hash computed by `git show ... | sha256sum` is `a1d7278b251e39c907641276ddee0d94919ffefa8613ad9863a2ff4e262d01ed`, matching the pin at `ci/quantum-sources/e8_conjugation_ideal.py:31`.

**Claim 2 — Conjugation, Flip, and Spans**
- **Justified — proved by source.** `phiVars` implements `i ↦ -i`, `s4 ↦ -s5`, `s5 ↦ s4`, and `s7 ↔ s8` at `lean/GororobaMath/CayleyDickson/E8ConjugationIdeal.lean:413`.
- **Justified — proved by source.** `jm_phi` states that exact substitution and multiplies `jp k` by `phiSign k` at `lean/GororobaMath/CayleyDickson/E8ConjugationIdeal.lean:429`.
- **Justified — computed.** The negative entries of `phiSign` are exactly the one-based positions `5, 7, 8, 10, 13, 16, 19, 21, 23, 26`, from `lean/GororobaMath/CayleyDickson/E8ConjugationIdeal.lean:402`.
- **Falsified as written — proved by source.** The standalone flip negates `s3`, `s5`, and `s6`, not `s3`, `s4`, `s5`, and `s6`. Its definition is at `lean/GororobaMath/CayleyDickson/E8ConjugationIdeal.lean:417`.
- The composed transformation in `jm_phi_flip` has arguments `(-s3), (-s5), (-s4), (-s6)` at `lean/GororobaMath/CayleyDickson/E8ConjugationIdeal.lean:438`. Thus both swapped `s4`/`s5` slots carry negatives after composition, but the additional flip itself still acts only on `s3`, `s5`, and `s6`.
- **Justified — proved by source.** `span_phi_jm` and `span_phiFlip_jm` are equalities of `Ideal.span` values in `MvPolynomial (Fin 10) R` at `lean/GororobaMath/CayleyDickson/E8ConjugationIdeal.lean:510` and `lean/GororobaMath/CayleyDickson/E8ConjugationIdeal.lean:525`. The section quantifies over every `R` with `[CommRing R]` at `lean/GororobaMath/CayleyDickson/E8ConjugationIdeal.lean:460`.

**Claim 3 — Heartbeats and Statement Strength**
- **Justified — proved by source.** Exactly four `set_option maxHeartbeats 1600000 in` commands occur at `lean/GororobaMath/CayleyDickson/E8ConjugationIdeal.lean:425`, `:434`, `:442`, and `:450`.
- Each `in` scope applies to the immediately following declaration: `jm_phi`, `jm_phi_flip`, `map_jmAt`, or `map_jpAt`. The option does not leak into the polynomial section.
- **Justified — computed.** A trust-sensitive token search found no `sorry`, `native_decide`, declared axiom, `Admitted`, `admit`, `Parameter`, `Conjecture`, or bypass command in either added proof file.
- **Justified — proved by source.** The theorem statements retain `[CommRing A]` from `lean/GororobaMath/CayleyDickson/E8ConjugationIdeal.lean:41`; the heartbeat option changes elaboration resources rather than the proposition.
- **Hypothesis.** The assertion that all four raises are needed lacks a retained default-heartbeat failure or a permitted current Lean run. The comments at `lean/GororobaMath/CayleyDickson/E8ConjugationIdeal.lean:426`, `:435`, `:443`, and `:451` assert necessity but do not measure it.
- The commit message reports a successful build with the raised limits, but that report does not establish failure under the default limit.

**Claim 4 — Rocq Bridge**
- **Justified — proved by source.** The bridge names the Lean source path at `rocq/quantum/E8ConjugationIdealBridge.v:1` and names `CayleyDickson.E8Conjugation.jm_phi`, `jm_phi_flip`, and `span_phi_jm` at `rocq/quantum/E8ConjugationIdealBridge.v:9`.
- `jm_phi_Z` and `jm_phi_flip_Z` give the integer list equalities at `rocq/quantum/E8ConjugationIdealBridge.v:49` and `rocq/quantum/E8ConjugationIdealBridge.v:53`.
- `conjugation_ideal_bridge` gives the integer-valued `gen_ideal` membership equivalence at `rocq/quantum/E8ConjugationIdealBridge.v:57`.
- The narrowing is explicit at `rocq/quantum/E8ConjugationIdealBridge.v:15`: Lean states equality of formal polynomial ideals, while Rocq quantifies over evaluated integer variable values.
- **Qualification — proved by source.** `conjugation_ideal_bridge` is a narrower value-level analogue, rather than the literal specialization `R := ℤ` of the Lean type. The literal Lean specialization remains an ideal equality in `MvPolynomial (Fin 10) ℤ`; the bridge comment states this distinction accurately.

**Claim 5 — Comparison Mechanism and Pin**
- **Justified — proved by source.** The mechanism described at `AGENTS.md:178` matches `ci/compare_e8_conjugation.sh:3`: both describe regeneration from the pinned `ideal J=` literals, exact comparison with the tracked Lean module, and rejection of a one-digit mutation.
- The normal comparison runs at `ci/compare_e8_conjugation.sh:34`; the coefficient mutation and rejection check occur at `ci/compare_e8_conjugation.sh:42` and `ci/compare_e8_conjugation.sh:49`.
- **Justified — proved by source.** The Lean generator obtains its lists through the pinned base generator at `ci/quantum-sources/e8_conjugation_ideal_lean.py:22` and `ci/quantum-sources/e8_conjugation_ideal_lean.py:330`.
- The base generator computes SHA-256 and raises on any mismatch before parsing at `ci/quantum-sources/e8_conjugation_ideal.py:49`.
- **Justified — computed.** The current `origin/main` bytes of `conjugation_map.sing` match the configured digest.

**Defects Beyond the Claims**
- **Low — computed:** The four heartbeat comments give a false term-count range. They say “12 to 16 terms” at `lean/GororobaMath/CayleyDickson/E8ConjugationIdeal.lean:426`, `:435`, `:443`, and `:451`, with the same generated text at `ci/quantum-sources/e8_conjugation_ideal_lean.py:209`, `:218`, `:226`, and `:234`. A read-only count of the two pinned literals found 3 to 14 terms per generator; generator 1 has 3 terms and generator 12 has 14 on both sides. Correct the generator comment or replace the numerical rationale with retained heartbeat measurements.
- **Low — proved by source:** The module docstring presents the parity-character sentence as part of the Lean main result at `lean/GororobaMath/CayleyDickson/E8ConjugationIdeal.lean:29`, but the parity-homogeneity check lives in Python at `ci/quantum-sources/e8_conjugation_ideal_lean.py:46`. The Lean file proves the conjugation identities, while the explicit degree-parity characterization remains a finite generator check. Label that evidence class or formalize the grading statement in Lean.
- **Low — proved by source:** The shell calibration mutates the generated Lean output but does not exercise the upstream digest-mismatch branch. The tested mutant is at `ci/compare_e8_conjugation.sh:42`; the uncalibrated digest refusal is at `ci/quantum-sources/e8_conjugation_ideal.py:49`. The source logic is fail-closed, but a known-bad pinned-input fixture would independently calibrate that protection.

**Conjectures**
- **Hypothesis:** The 27 case proofs can be replaced by a generic theorem for the `ℤ/2ℤ` grading defined by the parity of `deg s3 + deg s5 + deg s6`. The finite evidence is `ci/quantum-sources/e8_conjugation_ideal_lean.py:46`. **Falsifier:** one generator contains monomials of both parities, or the generic grading lemma fails to derive `jm_phi_flip`.
- **Hypothesis:** `phiMap` descends to an automorphism after quotienting by `i² + 1`, giving the conjugation equality directly in the complex-coordinate quotient used by the Singular calculation. The formal map begins at `lean/GororobaMath/CayleyDickson/E8ConjugationIdeal.lean:470`; the Singular relation appears at `conjugation_map.sing:2`. **Falsifier:** the image of `i² + 1` fails to lie in its generated ideal, or the descended map lacks an inverse.
- **Hypothesis:** Generator-wise helper lemmas or a grading-based proof reduce all four declarations below Lean’s default heartbeat limit. The current scopes begin at `lean/GororobaMath/CayleyDickson/E8ConjugationIdeal.lean:425`. **Falsifier:** a permitted default-limit build still exhausts heartbeats after the case proofs are decomposed.

No build, Python, Lean, or Rocq process ran. `git diff --check origin/main...ec79877eb` passed, `HEAD` remained `ec79877eb9ebe525acd9c2737806d985d900139c`, and the worktree remained clean.