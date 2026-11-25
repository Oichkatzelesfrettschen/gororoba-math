# Red-Team Review: gororoba-math PR 129 (`lean/e8-conjugation`, `ec79877eb`)

Diff inspected: `origin/main...ec79877eb` (`computed`: `git diff --stat origin/main...ec79877eb`, 8 files, +1015 lines across commits `167868aa8`, `82384be83`, `95f32a412`, `ec79877eb`). All source checks are read-only; no build, Python, Lean, or Rocq process ran.

---

## Claims Under Review

### Claim 1 — **Justified**
> The 27 generator lists `jm` and `jp` in [E8ConjugationIdeal.lean](lean/GororobaMath/CayleyDickson/E8ConjugationIdeal.lean) equal the two `ideal J=` lists of `conjugation_map.sing`, up to the variable order `(i, s1..s9)`.

- **Attempted break 1 (term-by-term / sign / exponent mismatch):** Compared all 27 definitions `jmGen00`–`jmGen26` ([E8ConjugationIdeal.lean](lean/GororobaMath/CayleyDickson/E8ConjugationIdeal.lean#L44-L186)) against the first `ideal J=` literal (`conjugation_map.sing` line 146, read via `computed`: `git -C gororoba-quantum show origin/main:docs/evidence/a5-exceptional-fibers/working/runs/e8-rees-fibers-v3-open-cells/conjugation/conjugation_map.sing`), and all 27 definitions `jpGen00`–`jpGen26` ([E8ConjugationIdeal.lean](lean/GororobaMath/CayleyDickson/E8ConjugationIdeal.lean#L220-L362)) against the second `ideal J=` literal (`conjugation_map.sing` line 290).
  - **Outcome (`proved`):** All 54 polynomials match in generator count (27 each), term count, coefficients, signs, and exponents, differing only by monomial ordering (sorted by descending total degree, then reverse exponent tuple) and factor ordering (`i, s1, ..., s9`).
- **Attempted break 2 (index permutation or off-by-one in `jm`/`jp` vectors):** Checked `jm` ([E8ConjugationIdeal.lean](lean/GororobaMath/CayleyDickson/E8ConjugationIdeal.lean#L189-L217)) and `jp` ([E8ConjugationIdeal.lean](lean/GororobaMath/CayleyDickson/E8ConjugationIdeal.lean#L365-L393)).
  - **Outcome (`proved`):** Both list `00` through `26` in order, matching 1-based positions 1 through 27 in `conjugation_map.sing`.

---

### Claim 2 — **Falsified** (on `jm_phi_flip`)
> `jm_phi` states the conjugation `Phi` (`i -> -i, s4 -> -s5, s5 -> s4, s7 <-> s8`) and the signs `-1` exactly at `k+1 = 5, 7, 8, 10, 13, 16, 19, 21, 23, 26`; `jm_phi_flip` states the same after flipping `s3, s4, s5, s6` with no sign; `span_phi_jm` and `span_phiFlip_jm` state ideal equalities in `MvPolynomial` over every `CommRing`.

- **Attempted break 1 (`jm_phi` and `phiSign` positions):** Checked `phiSign` ([E8ConjugationIdeal.lean](lean/GororobaMath/CayleyDickson/E8ConjugationIdeal.lean#L402-L403)) and `jm_phi` ([E8ConjugationIdeal.lean](lean/GororobaMath/CayleyDickson/E8ConjugationIdeal.lean#L429-L431)).
  - **Outcome (`proved`):** `phiSign` has 27 entries with `-1` at 0-based indices `4, 6, 7, 9, 12, 15, 18, 20, 22, 25`, i.e., `k + 1 = 5, 7, 8, 10, 13, 16, 19, 21, 23, 26`, and `+1` elsewhere. `jm_phi` applies `(-i, s1, s2, s3, -s5, s4, s6, s8, s7, s9)` to `jm` and multiplies `jp` by `(phiSign k : A)`. This part holds.
- **Attempted break 2 (`jm_phi_flip` variable flip — BREAK SUCCEEDS):** Checked `flipVars` ([E8ConjugationIdeal.lean](lean/GororobaMath/CayleyDickson/E8ConjugationIdeal.lean#L418-L419)), `jm_phi_flip` ([E8ConjugationIdeal.lean](lean/GororobaMath/CayleyDickson/E8ConjugationIdeal.lean#L438-L439)), `phiFlipMap_jmPoly` ([E8ConjugationIdeal.lean](lean/GororobaMath/CayleyDickson/E8ConjugationIdeal.lean#L495-L506)), and `flip` in [e8_conjugation_ideal_lean.py](ci/quantum-sources/e8_conjugation_ideal_lean.py#L33-L38).
  - **Outcome (`proved`):** Claim 2 states that `jm_phi_flip` flips `s3, s4, s5, s6`. The code flips only **`s3, s5, s6`** (`s4` stays fixed):
    - `flipVars v = ![v 0, v 1, v 2, -v 3, v 4, -v 5, -v 6, v 7, v 8, v 9]` (index 4 is `+v 4`, not `-v 4`).
    - `phiMap ∘ flipMap` sends `s4 ↦ s4 ↦ -s5` and `s5 ↦ -s5 ↦ -s4`, yielding `jm (-i) s1 s2 (-s3) (-s5) (-s4) (-s6) s8 s7 s9 k = jp i s1 s2 s3 s4 s5 s6 s7 s8 s9 k` ([E8ConjugationIdeal.lean](lean/GororobaMath/CayleyDickson/E8ConjugationIdeal.lean#L439)).
    - Flipping `s3, s4, s5, s6` before `Phi` would send `s4 ↦ -s4 ↦ +s5` (producing `(+s5)` in slot 4 instead of `(-s5)`). Because `s4` appears only as `s4^2` in `jmGen00` and nowhere in `jmGen01`–`jmGen26`, the two maps agree on `jm`, but they are distinct endomorphisms of `MvPolynomial (Fin 10) R` and `jm_phi_flip` states `Phi ∘ Flip_{s3,s5,s6}`, not `Phi ∘ Flip_{s3,s4,s5,s6}`.
- **Attempted break 3 (`span_phi_jm` and `span_phiFlip_jm`):** Checked [E8ConjugationIdeal.lean](lean/GororobaMath/CayleyDickson/E8ConjugationIdeal.lean#L460-L531).
  - **Outcome (`proved`):** Both are quantified over `variable (R : Type*) [CommRing R]` and state `Ideal.span (phiMap R '' Set.range (jmPoly R)) = Ideal.span (Set.range (jpPoly R))` and the same for `phiFlipMap R` in `MvPolynomial (Fin 10) R`. Both proofs hold in every `CommRing R` (including characteristic 2 and the zero ring). Note that `Ideal.span (f '' s)` is `Ideal.map f (Ideal.span s)` by `Ideal.map_span`, while the file does not separately prove `phiMap R` is an `AlgEquiv`.

---

### Claim 3 — **Falsified** (on "needed")
> The four `maxHeartbeats 1600000` raises are scoped to single declarations and needed; nothing weakens the statements.

- **Attempted break 1 (scoping and soundness):** Checked lines 425–456 of [E8ConjugationIdeal.lean](lean/GororobaMath/CayleyDickson/E8ConjugationIdeal.lean#L425-L456).
  - **Outcome (`proved`):** All four raises use `set_option maxHeartbeats 1600000 in` immediately before single `theorem` declarations (`jm_phi`, `jm_phi_flip`, `map_jmAt`, `map_jpAt`). `maxHeartbeats` is an elaborator resource limit and weakens no statement or axiom set.
- **Attempted break 2 (necessity of the four raises — BREAK SUCCEEDS):**
  - **Architectural necessity (`proved`):** [e8_conjugation_ideal_lean.py](ci/quantum-sources/e8_conjugation_ideal_lean.py#L93-L109) already generates 27 separate definitions `jmGen00`–`jmGen26` and `jpGen00`–`jpGen26`. Putting all 27 `ring`/`simp` cases inside one `fin_cases k` theorem causes the heartbeat blowup; emitting per-generator lemmas eliminates the 27-way combined budget.
  - **Unused declaration (`proved`):** `map_jpAt` ([E8ConjugationIdeal.lean](lean/GororobaMath/CayleyDickson/E8ConjugationIdeal.lean#L454-L456)) is never referenced anywhere in the repository (`computed`: `git grep -n map_jpAt` returns only its definition and generator template), so its `maxHeartbeats 1600000` raise is unused by the module's results.
  - **Unmeasured threshold (`hypothesis`):** No heartbeat profile is recorded in the repo or commit messages showing that `map_jmAt`/`map_jpAt` (which run `simp` without `ring`) or `jm_phi`/`jm_phi_flip` require 1,600,000 rather than a lower budget; because Lean cannot be run in this review, exact heartbeat counts remain unmeasured.

---

### Claim 4 — **Partially Justified (incomplete coverage of the Lean theorems)**
> [E8ConjugationIdealBridge.v](rocq/quantum/E8ConjugationIdealBridge.v) names the Lean theorems by path and name and states their integer instance; its narrowing (integer values, not the polynomial ring) is stated.

- **Attempted break 1 (naming and integer instances):** Checked [E8ConjugationIdealBridge.v](rocq/quantum/E8ConjugationIdealBridge.v#L1-L64) against [E8ConjugationIdeal.lean](lean/GororobaMath/CayleyDickson/E8ConjugationIdeal.lean#L26-L34) and [E8ConjugationIdeal.v](rocq/quantum/E8ConjugationIdeal.v#L119-L214).
  - **Outcome (`proved`):** Line 1 names `lean/GororobaMath/CayleyDickson/E8ConjugationIdeal.lean`, and lines 10–15 name `CayleyDickson.E8Conjugation.jm_phi`, `CayleyDickson.E8Conjugation.jm_phi_flip`, and `CayleyDickson.E8Conjugation.span_phi_jm`. `jm_phi_Z` (line 49), `jm_phi_flip_Z` (line 53), and `conjugation_ideal_bridge` (line 57) state their integer instances (`phi_signs` in [E8ConjugationIdeal.v](rocq/quantum/E8ConjugationIdeal.v#L119-L120) matches `phiSign` entry-for-entry). Lines 15–18 explicitly state the narrowing of `conjugation_ideal_bridge` from the polynomial ring to integer values in `Z`.
- **Attempted break 2 (missing theorem and double narrowing — PARTIAL BREAK):**
  - **Outcome (`proved`):** `E8ConjugationIdeal.lean` declares four main results (`jm_phi`, `jm_phi_flip`, `span_phi_jm`, and `span_phiFlip_jm`; [E8ConjugationIdeal.lean](lean/GororobaMath/CayleyDickson/E8ConjugationIdeal.lean#L26-L34)). `E8ConjugationIdealBridge.v` omits `span_phiFlip_jm` completely (neither named in the docstring nor bridged in `gen_ideal`).
  - **Outcome (`proved`):** Line 15 of [E8ConjugationIdealBridge.v](rocq/quantum/E8ConjugationIdealBridge.v#L15-L18) describes `span_phi_jm` as having "the ring `Z[i, s1..s9]` replaced by `Z`", understating the Lean theorem's generality (`MvPolynomial (Fin 10) R` for every `CommRing R`, not only `R = Z`).

---

### Claim 5 — **Justified** (with calibration/error-handling caveats)
> [compare_e8_conjugation.sh](ci/compare_e8_conjugation.sh) and the [AGENTS.md](AGENTS.md#L178-L182) sentence describe the same mechanism, and the generator refuses an input with another sha256.

- **Attempted break 1 (AGENTS.md vs script):** Compared [AGENTS.md](AGENTS.md#L178-L182) with [compare_e8_conjugation.sh](ci/compare_e8_conjugation.sh#L1-L56).
  - **Outcome (`proved`):** Both describe the same flow: invoke `ci/quantum-sources/e8_conjugation_ideal_lean.py --check` with `GOROROBA_QUANTUM`, compare the rendering against `lean/GororobaMath/CayleyDickson/E8ConjugationIdeal.lean`, and calibrate by requiring `--check --source` to reject a copy with one changed digit (`8` -> `9` in `jmGen00`, line 43) with exit status 1.
- **Attempted break 2 (sha256 pin enforcement):** Traced `e8_conjugation_ideal_lean.py:main()` ([e8_conjugation_ideal_lean.py](ci/quantum-sources/e8_conjugation_ideal_lean.py#L330)) -> `e8_conjugation_ideal.py:generator_lists()` ([e8_conjugation_ideal.py](ci/quantum-sources/e8_conjugation_ideal.py#L97-L109)) -> `read_pinned()` ([e8_conjugation_ideal.py](ci/quantum-sources/e8_conjugation_ideal.py#L49-L56)).
  - **Outcome (`proved`):** `read_pinned` hashes raw bytes with `hashlib.sha256` and raises `SystemExit(1)` on any digest mismatch against `PINS` ([e8_conjugation_ideal.py](ci/quantum-sources/e8_conjugation_ideal.py#L30-L34)), which pins `conjugation_map.sing` (`a1d7278b...`, matching `SING_SHA256` in [conjugation_map_certificate.py](ci/quantum-sources/conjugation_map_certificate.py#L32)) as well as both v2 Rees scripts (`e8-nm-p.v2-u-full.sing`, `e8-np-p.v2-u-full.sing`).
  - **Caveat (`proved`):** [compare_e8_conjugation.sh](ci/compare_e8_conjugation.sh#L42-L55) calibrates only the output-side mutation (perturbing the Lean copy) and never calibrates a mutated `conjugation_map.sing` input.

---

## Defects Beyond the Claims

1. **False term-count comment in Lean source and generator (`proved`):**
   - [E8ConjugationIdeal.lean](lean/GororobaMath/CayleyDickson/E8ConjugationIdeal.lean#L426) (and lines 435, 443, 451; generated by [e8_conjugation_ideal_lean.py](ci/quantum-sources/e8_conjugation_ideal_lean.py#L209) lines 209, 218, 226, 234) states `"the case split over 27 generators of 12 to 16 terms exceeds the default limit"`. The 27 generators actually have **3 to 14 terms** (1 of 3, 5 of 4, 5 of 6, 12 of 12, and 4 of 14 terms; none has 16 terms).
2. **Misleading calibration output when `--check` fails on input pin mismatch (`proved`):**
   - In [compare_e8_conjugation.sh](ci/compare_e8_conjugation.sh#L34-L55), if step 1 (`--check`) exits `1` because `read_pinned` rejected a bad `conjugation_map.sing` sha256, the script continues to step 2 (`--check --source "$work/mutated.lean"`), which also exits `1` at `read_pinned`, and prints `"compare_e8_conjugation: the copy with one changed coefficient is rejected"` even though the Lean file was never compared. The final exit status remains `1` (fail-closed), but the log reports a false-positive calibration.
3. **Non-POSIX `sed` address in POSIX `sh` script (`proved`):**
   - [compare_e8_conjugation.sh](ci/compare_e8_conjugation.sh#L43) uses `sed '0,/pattern/s//.../'`, which is a GNU `sed` extension rather than POSIX `sed` (`0` is not a valid line address in POSIX/BSD `sed`).
4. **Dead code, unused constant, and inconsistent error prefix/exit code in `e8_conjugation_ideal_lean.py` (`proved`):**
   - `CONTINUATION = "      "` ([e8_conjugation_ideal_lean.py](ci/quantum-sources/e8_conjugation_ideal_lean.py#L28)) is unused (`render_gen` line 97 hardcodes `"  "` and `"    "`).
   - Lines 328–329 (`if arguments.write and arguments.source: parser.error(...)`) are unreachable dead code because importing `e8_conjugation_ideal` -> [quantum_checkout.py](ci/quantum-sources/quantum_checkout.py#L58-L64) already rejects `--source` during `--write` at import time with exit status 2.
   - Unsafe write target refusal ([e8_conjugation_ideal_lean.py](ci/quantum-sources/e8_conjugation_ideal_lean.py#L336-L337)) raises `base.fail(...)` (exit status 1, prefix `e8_conjugation_ideal:`) instead of `quantum_checkout.refuse(...)` (exit status 2), and does not check `TARGET.parent.is_symlink()`.
   - `PREAMBLE` and `POSTAMBLE` hardcode `26` and `Fin 27` ([e8_conjugation_ideal_lean.py](ci/quantum-sources/e8_conjugation_ideal_lean.py#L158) and lines 189–278) while `render_vector` and `phiSign` parameterize `count`.
5. **Commit-body line length rule violation (`computed` via `git log --format=fuller origin/main..ec79877eb`):**
   - Workspace guide ([AGENTS.md](file://AGENTS.md#L119)) requires commit-body lines to wrap at 72 columns. Commits `167868aa8` (433 chars), `82384be83` (279 chars), and `95f32a412` (212 chars) each have unwrapped single-line bodies.
6. **Unused public theorem `map_jpAt` (`proved`):**
   - `map_jpAt` ([E8ConjugationIdeal.lean](lean/GororobaMath/CayleyDickson/E8ConjugationIdeal.lean#L454-L456)) is never used in the module or elsewhere in the repository.

---

## Conjectures Suggested by the Material

1. **`Phi_flip` is an involution swapping `J_N-` and `J_N+`, whereas `Phi` has order 4 and `Phi(J_N+) ≠ J_N-` (`proved` for the order and generator failure; `hypothesis` for ideal non-equality):**
   - `phiFlipMap^2 = id` on `MvPolynomial (Fin 10) R` (`s4 -> -s5 -> s4`, `s5 -> -s4 -> s5`, `s3, s6, i` negated twice, `s7 <-> s8`), so `phiFlipMap` maps `jpPoly k` back to `jmPoly k` with no sign and maps `J_N+` onto `J_N-`.
   - In contrast, `phiMap^2` fixes `i, s1, s2, s3, s6, s7, s8, s9` and negates `s4, s5`. On `jmGen04`, `phiMap^2` flips the sign of `8*i*s1*s5*s7^2` while fixing `-8*i*s2*s3*s7^2`, so `phiMap(jpGen04)` is not a scalar multiple of `jmGen04`. Conjecture: `Phi(J_N+) ≠ J_N-` as ideals in `Z[i, s1..s9]` (and in `Q[i, s1..s9]/(i^2+1)`).
   - **Falsifier:** Compute `reduce(Phi(Jp), std(Jm + mi))` in Singular (or find cofactors in `MvPolynomial (Fin 10) Q` expressing `Phi(jpGen04)` in `J_N-`); a zero reduction falsifies the conjecture.

2. **Per-generator lemma decomposition eliminates all four `maxHeartbeats 1600000` overrides (`hypothesis`):**
   - Having `e8_conjugation_ideal_lean.py` emit 27 per-generator lemmas (`jmGen00_phi`..`jmGen26_phi`, `jmGen00_phi_flip`..`jmGen26_phi_flip`, `map_jmGen00`..`map_jmGen26`) and dispatching `jm_phi`, `jm_phi_flip`, `map_jmAt` via `fin_cases k` to those lemmas compiles under Lean's default `maxHeartbeats` (200,000) with zero `set_option maxHeartbeats` lines.
   - **Falsifier:** Refactor the generator to emit per-generator lemmas without `set_option maxHeartbeats` and run `lake build --wfail`; any heartbeat timeout falsifies the conjecture.

3. **Additional `(Z/2Z)`-grading on `(s1, s3, s6, s9)` acts diagonally on all 27 generators (`hypothesis`):**
   - Spot-checking `jmGen00`–`jmGen04` and `jmGen11`–`jmGen12` shows every monomial in each generator has uniform parity in `deg(s1) + deg(s3) + deg(s6) + deg(s9)` (even for `00..02`, `11..16`, `21..26`; odd for `03..10`, `17..20`). Conjecture: negating `(s1, s3, s6, s9)` maps every `jmGen_k` to `±jmGen_k` (and `jpGen_k` to `±jpGen_k`), giving a diagonal sign-symmetry group of order at least 8 (`<Flip_{s4}, Flip_{s3,s5,s6}, Flip_{s1,s3,s6,s9}>`) fixing `J_N-` generator-by-generator up to sign.
   - **Falsifier:** Check `deg(s1) + deg(s3) + deg(s6) + deg(s9) mod 2` across all monomials of `jmGen00`–`jmGen26`; any generator with both even and odd monomials falsifies the conjecture.
AGY-DONE
