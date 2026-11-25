# Red-Team Review: gororoba-math PR 131 (`rocq/root-exchange`, head `6ab5427d7`)

Diff reviewed: `origin/main...6ab5427d7` (`ci/rocq-warnings/allowed.tsv`, `rocq/quantum/E8RootExchange.v`, `rocq/quantum/_RocqProject`). All checks are read-only from source and git metadata; no build, Python, Lean, or Rocq process ran.

---

## Claim Verdicts

### Claim 1 — Diagonal congruences of `C_N-` and `C_N+` via list equality
**Verdict: Justified** (with one ambient-ring narrowing on the evaluated definitions).

- **Flip sets and product (`proved`)**: Under the index convention `1 = i`, `2..10 = s1..s9` ([E8ConjugationMap.v](rocq/quantum/E8ConjugationMap.v#L6-L7), [E8RootExchange.v](rocq/quantum/E8RootExchange.v#L4-L5)), `T1 = [2; 4; 7; 10]` is `{s1, s3, s6, s9}`, `T2 = [1; 3; 4; 5; 7; 8; 9]` is `{i, s2, s3, s4, s6, s7, s8}`, and `T3 = [1; 2; 3; 5; 8; 9; 10]` is their exact symmetric difference `T1 Δ T2` ([E8RootExchange.v](rocq/quantum/E8RootExchange.v#L42-L44)). For `C_N+`, `T2p = [1; 3; 4; 6; 7; 8; 9]` and `T3p = [1; 2; 3; 6; 8; 9; 10]` exchange `5` (`s4`) and `6` (`s5`), while `T1` contains neither ([E8RootExchange.v](rocq/quantum/E8RootExchange.v#L45-L46)).
- **Explicit nontrivial sign vectors (`proved`)**: `d1L`, `d2L`, and `d3L` each have length 15 with entries in `{-1, +1}`, none is `±(1,...,1)`, and `d3L[a] = d1L[a] * d2L[a]` holds at every index `0 <= a < 15` ([E8RootExchange.v](rocq/quantum/E8RootExchange.v#L48-L51)).
- **Soundness of the list-equality check (`proved`)**: `symCheck T L C` checks `flipSP T (C a b) = scaleSP (dsel L a * dsel L b) (C a b)` for all `0 <= a, b < 15` via `allpairs` and `spoly_eq_dec` ([E8RootExchange.v](rocq/quantum/E8RootExchange.v#L31-L40), [E8RootExchange.v](rocq/quantum/E8RootExchange.v#L53-L71)). `evMono_flip`, `evSP_flip`, and `symm_of_check` lift that list equality to the exact entrywise congruence `CM.evSP (flipx T xv) (C a b) = D.mul (CM.SPf.phiZ (Z.mul (dsel L a) (dsel L b))) (CM.evSP xv (C a b))` for all `a < 15, b < 15` and arbitrary `xv : nat -> D.t`, with no `i^2 = -1` hypothesis ([E8RootExchange.v](rocq/quantum/E8RootExchange.v#L134-L166)). Spot-checks on `Cm 0 1`, `Cm 0 2`, `Cm 0 3`, `Cm 0 8`, `Cp 0 2`, `Cp 0 8` ([E8ConjugationMap.v](rocq/quantum/E8ConjugationMap.v#L34), [E8ConjugationMap.v](rocq/quantum/E8ConjugationMap.v#L52)) confirm the check is non-vacuous.
- **Attempted break 1a — `spoly_eq_dec` vs polynomial equality (`proved`)**: Syntactic list equality is strictly stronger than polynomial equality (it would fail if monomials were reordered or unmerged), so `symCheck = true` is sufficient rather than necessary in general; it is sound without needing `wfb` because `evSP` evaluates `xv v` directly for any `v : nat`. Break failed (soundness holds).
- **Attempted break 1b — ambient ring restriction (`proved`)**: The evaluated congruences `symm_Cm_T1..T3` and `symm_Cp_T1..T3` sit inside `Module RootExchange (D : CommutativeRingWithI)` ([E8RootExchange.v](rocq/quantum/E8RootExchange.v#L127), [E8RootExchange.v](rocq/quantum/E8RootExchange.v#L161-L166)). Although `xv 1` (`i`) is free in their types, the functor requires `D` to contain *some* `D.i` with `D.i^2 = -1` ([CdTowerRing.v](rocq/quantum/CdTowerRing.v#L480-L484)), excluding `Z`, `R`, and `F_p` for `p ≡ 3 (mod 4)` even though `D.i` and `D.i_squared` never appear in `symm_of_check`. The syntactic lemmas `symm_Cm_T1_ok..symm_Cp_T3_ok` ([E8RootExchange.v](rocq/quantum/E8RootExchange.v#L66-L71)) do hold over `Z` directly.

---

### Claim 2 — `jm_flip_*` homogeneity over every commutative ring and sign lists
**Verdict: Justified**, with one wording discrepancy in the claim (there are **five** `jm_flip_*` theorems, not four).

- **Count of flips (`proved`)**: `Section JHomogeneity` proves five theorems ([E8RootExchange.v](rocq/quantum/E8RootExchange.v#L81-L123)): four independent flips (`jm_flip_s4`, `jm_flip_s3s5s6`, `jm_flip_s1s5s9`, `jm_flip_i_s2_s5_s7_s8`) plus their product `jm_flip_T2` (`T2 = {s4} Δ {s3, s5, s6} Δ {i, s2, s5, s7, s8}`).
- **Ring generality (`proved`)**: `Section JHomogeneity` quantifies over an arbitrary `R : Type` satisfying `Ring_theory.ring_theory rO rI radd rmul rsub ropp (@eq R)` — every commutative ring, with `i` free ([E8RootExchange.v](rocq/quantum/E8RootExchange.v#L74-L78)).
- **Attempted break 2a — `signed` tail-truncation trap (`proved`)**: `signed e g` returns `g` unchanged once `e` runs out ([E8ConjugationIdeal.v](rocq/quantum/E8ConjugationIdeal.v#L124-L128)), so a short sign list would silently default trailing generators to `+1`. Counting each list confirms all five lists have exactly 27 booleans, matching the 27 generators of `jm` ([E8ConjugationIdeal.v](rocq/quantum/E8ConjugationIdeal.v#L61-L88), [E8RootExchange.v](rocq/quantum/E8RootExchange.v#L83), [E8RootExchange.v](rocq/quantum/E8RootExchange.v#L92), [E8RootExchange.v](rocq/quantum/E8RootExchange.v#L101), [E8RootExchange.v](rocq/quantum/E8RootExchange.v#L110), [E8RootExchange.v](rocq/quantum/E8RootExchange.v#L119)). Break failed.
- **Attempted break 2b — sign-list correctness and character multiplication (`proved`)**:
  - `jm_flip_s4` is all `true` (`s4` appears in `jm` only as `s4 * s4` in generator 1, [E8ConjugationIdeal.v](rocq/quantum/E8ConjugationIdeal.v#L62-L88)).
  - `jm_flip_s3s5s6` is `false` at 1-based positions `{5, 7, 8, 10, 13, 16, 19, 21, 23, 26}`.
  - `jm_flip_s1s5s9` and `jm_flip_i_s2_s5_s7_s8` share the exact same character, `false` at `{4, 6, 9, 11, 13, 16, 18, 20, 23, 26}`.
  - `jm_flip_T2` is `false` at `{4..11, 18..21}`, which is the exact entrywise sign product of `jm_flip_s4`, `jm_flip_s3s5s6`, and `jm_flip_i_s2_s5_s7_s8` at all 27 positions.
  - Spot-checking monomials of generators 1, 2, 3, 4, 5, 12, 13, 18, 22, 23, 27 matches every list, and each proof discharges all 27 equalities by `repeat (apply (cons_eq R); [ring |]). reflexivity.`. Break failed.

---

### Claim 3 — `root_exchange_C`, `root_exchange_detB`, `root_exchange_ideal` and silence on `F`, `G`
**Verdict: Justified**, with three precision caveats on what the statements actually say.

- **Functor and instance (`proved`)**: `Module RootExchange (D : CommutativeRingWithI)` and `Module GaussianRootExchange := RootExchange GaussianIntegers` ([E8RootExchange.v](rocq/quantum/E8RootExchange.v#L127), [E8RootExchange.v](rocq/quantum/E8RootExchange.v#L207)). `root_exchange_root` and `root_exchange_root_sq` establish `flipx T2 xv 1 = D.opp (xv 1)` and preservation of `x^2 = -1` ([E8RootExchange.v](rocq/quantum/E8RootExchange.v#L169-L174)).
- **Attempted break 3a — `flipx T2` also negates six `s`-coordinates (`proved`)**: `T2 = {i, s2, s3, s4, s6, s7, s8}` does not only negate `i`; negating `i` alone changes `detB = -1024 (s2^2 - 1)^2 (s2 - i)^2` to `-1024 (s2^2 - 1)^2 (s2 + i)^2` (unequal at `s2 = 2, i = √-1`) and fails to preserve `jm` generator 1. The inline comments at [E8RootExchange.v](rocq/quantum/E8RootExchange.v#L176), [E8RootExchange.v](rocq/quantum/E8RootExchange.v#L182), and [E8RootExchange.v](rocq/quantum/E8RootExchange.v#L191) ("at root -r ... at root r") omit that the `s`-point is simultaneously reflected by `flipx T2`. The formal statements themselves are explicit (`flipx T2 xv`).
- **Attempted break 3b — `root_exchange_ideal` is point-evaluated in `D` (`proved`)**: For a concrete ring `D` such as `GaussianIntegers`, `root_exchange_ideal` ([E8RootExchange.v](rocq/quantum/E8RootExchange.v#L192-L198)) states equality of the ideals of `D` generated by the 27 scalar values at `flipx T2 xv` and at `xv` (which over a field reduces to simultaneous vanishing at that point). Obtaining equality of polynomial ideals in `K[s1..s9]` requires instantiating `RootExchange` with `D := K[s1..s9]` (or `jm_flip_T2` with `R := K[s1..s9]`).
- **Attempted break 3c — silence on `F` and `G` (`proved`)**: `G` does not appear anywhere in `E8RootExchange.v` or `E8ConjugationMap.v`. `Fm` appears only inside `CM.detBD Cm Fm` in `root_exchange_detB` ([E8RootExchange.v](rocq/quantum/E8RootExchange.v#L183-L189)), which is proved by rewriting with `CM.detB_Nm` rather than proving any transformation law for `Fm`. Break failed (Claim 3's silence claim holds).

---

### Claim 4 — No axioms, `_RocqProject`, `allowed.tsv`, and docstring conventions
**Verdict: Partially falsified** (the docstring convention block contains inaccurate and unused references; the axiom, `_RocqProject`, and `allowed.tsv` parts are justified).

- **No axiom added (`proved`)**: `E8RootExchange.v` contains no `Axiom`, `Parameter`, `Admitted`, `admit`, or `Conjecture`; `Hypothesis Rth` is discharged at `End JHomogeneity` ([E8RootExchange.v](rocq/quantum/E8RootExchange.v#L77), [E8RootExchange.v](rocq/quantum/E8RootExchange.v#L125)); no classical library is imported; `rocq/quantum/kernel-assumptions.txt` is unchanged.
- **`_RocqProject` (`proved`)**: `E8RootExchange.v` is added in alphabetical order in [rocq/quantum/_RocqProject](rocq/quantum/_RocqProject#L63), complying with [AGENTS.md](AGENTS.md#L305-L307).
- **`allowed.tsv` (`proved` for policy/schema; `hypothesis` for runtime warning emission)**: [ci/rocq-warnings/allowed.tsv](ci/rocq-warnings/allowed.tsv#L810-L812) adds `deprecated-transitive-library-file-since-Stdlib-9.0`, `disj-pattern-notation`, and `using-fallback-loc` in alphabetical order. All three names already exist in [ci/rocq-warnings/causes.tsv](ci/rocq-warnings/causes.tsv#L5-L7), satisfying [AGENTS.md](AGENTS.md#L335-L337). `Add Ring` at lines 78 and 129 triggers `using-fallback-loc`; whether the exact three warnings and no others print under `-w all,+default` is `hypothesis` without running `rocq`.
- **Attempted break 4a — docstring conventions (`proved`, breaks Claim 4 in part)**:
  1. [E8RootExchange.v](rocq/quantum/E8RootExchange.v#L4) states *"the evaluation `evSP` and the reflection `checkEq` are those of `E8ConjugationMap.v`"*, but `checkEq` is never used in `E8RootExchange.v`; reflection uses `symCheck` with `spoly_eq_dec`.
  2. [E8RootExchange.v](rocq/quantum/E8RootExchange.v#L8) states *"The generator lists `jm` and `jp` are those of `E8ConjugationIdeal.v`"*, but `jp` is never used in `E8RootExchange.v`.
  3. [E8RootExchange.v](rocq/quantum/E8RootExchange.v#L8-L9) states `signed e g` multiplies by `±1` according to `e` without specifying the boolean polarity (`true` = `+1`, `false` = `-1`).
  4. [E8RootExchange.v](rocq/quantum/E8RootExchange.v#L12-L15) names `symm_Cm_T1..symm_Cp_T3` without the `RootExchange.` prefix (unlike `RootExchange.root_exchange_C` on line 19) and calls them identities *"of integer polynomials"*, whereas `RootExchange.symm_*` require `CommutativeRingWithI` (not satisfied by `Z`).
  5. Pure ASCII (`AGENTS.md:491-492`) is respected (`proved`).

---

## Defects Beyond the Claims

1. **Unnecessary `CommutativeRingWithI` requirement on `symm_Cm_*`, `symm_Cp_*`, `root_exchange_C`, and `root_exchange_ideal` (`proved`)**: [E8RootExchange.v](rocq/quantum/E8RootExchange.v#L127-L205) places all of these inside `Module RootExchange (D : CommutativeRingWithI)`, even though none of them uses `D.i` or `D.i_squared`. Only `root_exchange_detB` (via `CM.detB_Nm`) uses `i^2 = -1` (and even that hypothesis is explicit on `xv 1`, not `D.i`).
2. **Unused imports (`proved`)**: [E8RootExchange.v](rocq/quantum/E8RootExchange.v#L27-L28) imports `Lia`, `InitialRing`, `StiefelA5Certificate`, and `StiefelA5Pfaffian`, none of which is directly referenced in the file.
3. **Proof-carrying `spoly_eq_dec` inside `vm_compute` boolean check (`proved`; performance impact `hypothesis`)**: `symCheck` ([E8RootExchange.v](rocq/quantum/E8RootExchange.v#L53-L64)) calls `spoly_eq_dec` (`sumbool` built from `list_eq_dec`, `Z.eq_dec`, `Nat.eq_dec`) and discards its proof term to return `bool`. A plain boolean `spoly_eqb` with a soundness lemma avoids reducing proof combinators in `vm_compute` and `rocq check`. (The commit message's 2584 s pure `rocq check` time is `hypothesis`: likely dominated by re-checking `E8ConjugationMap.vo` and `StiefelA5*.vo` in the dependency closure.)
4. **Missing `vm_compute` cost note in the file docstring (`proved`)**: [AGENTS.md](AGENTS.md#L222-L227) requires a large `vm_compute` certificate to state both compile/bytecode and pure kernel re-check costs; commit `6ab5427d7` records `96 s` (bytecode) and `2584 s` (pure) only in the commit message, not in [E8RootExchange.v](rocq/quantum/E8RootExchange.v#L1-L25).
5. **Asymmetry between `N-` and `N+` coverage (`proved`)**: `symm_Cp_T1..T3` are proved for `C_N+` ([E8RootExchange.v](rocq/quantum/E8RootExchange.v#L69-L71), [E8RootExchange.v](rocq/quantum/E8RootExchange.v#L164-L166)), but `J_N+` (`jp`) and `detB_Np` have no homogeneity or root-exchange theorems despite `jp` being announced in line 8.

---

## Conjectures Suggested by the Material

1. **Diagonal congruence of `Fm` and the full 15x15 matrix `T = Fm^t Cm Fm` under `T2` with `i` free** (`proved` by column-by-column inspection of `FmRows` at [E8ConjugationMap.v](rocq/quantum/E8ConjugationMap.v#L69-L85); `hypothesis` until machine-checked):
   - *Statement*: With `E2 = diag(-1, 1, 1, -1, 1, 1, 1, -1, -1, 1, 1, -1, -1, 1, -1)`, `Fm(flipx T2 xv) = D2 * Fm(xv) * E2` entrywise over `Z[i, s1..s9]` with `i` free. Consequently, the entire 15x15 transformed matrix `T_N- = Fm^t Cm Fm` satisfies `T_N-(flipx T2 xv) = E2 * T_N-(xv) * E2` with `i` free, implying `detB_N-(flipx T2 xv) = detB_N-(xv)` without assuming `i^2 = -1` (and congruence of the full Schur complement as well).
   - *Falsifier*: Check `flipSP T2 (Fm r c) = scaleSP (d2L[r] * e2[c]) (Fm r c)` across all `0 <= r, c < 15`; any single entry mismatch falsifies the conjecture.

2. **Within-cell symmetry `T1` and pointwise-trivial symmetry `T3` of `J_N-`** (`hypothesis`, derived from `T1 = {s3, s5, s6} Δ {s1, s5, s9}` and `T3 = T1 Δ T2` in [E8RootExchange.v](rocq/quantum/E8RootExchange.v#L42-L44), [E8RootExchange.v](rocq/quantum/E8RootExchange.v#L90-L123)):
   - *Statement*: `T1 = {s1, s3, s6, s9}` fixes `i` and `s2` (hence fixes `detB_N-` identically), multiplies `J_N-` generators by the same character as `jm_flip_T2`, and conjugates `Cm` by `D1` — so `T1` is a genuine **within-cell** symmetry of `(C_N-, detB_N-, J_N-)` at a fixed root `r`. Meanwhile `T3 = {i, s1, s2, s4, s7, s8, s9}` multiplies all 27 generators of `J_N-` by `+1` (not merely up to sign).
   - *Falsifier*: Evaluate `jm` at `flipx T1 xv` vs `signed (char T2) (jm xv)` and at `flipx T3 xv` vs `jm xv`; any single generator mismatch falsifies the conjecture.

3. **Exact order-16 sign-symmetry group of `J_N-` with order-4 pointwise kernel** (`hypothesis`, from [E8RootExchange.v](rocq/quantum/E8RootExchange.v#L81-L114)):
   - *Statement*: Inside `{±1}^10` acting on `(i, s1..s9)`, the subgroup multiplying every generator of `jm` by `±1` has order exactly `16`, generated by `{s4}`, `{s3, s5, s6}`, `{s1, s5, s9}`, and `{i, s2, s5, s7, s8}`, and its kernel (fixing all 27 generators with sign `+1`) has order `4`, generated by `{s4}` and `{i, s1, s2, s7, s8, s9}` (equivalently `{s4}` and `T3`).
   - *Falsifier*: Enumerate all `2^10 = 1024` sign assignments on the 27 polynomials of `jm`; finding a 17th homogeneous flip or a generator negated by `{i, s1, s2, s7, s8, s9}` falsifies the conjecture.

4. **Conjugate `J_N+` homogeneity and `N+` root exchange under `T2p`** (`hypothesis`, from `Phi` in [E8ConjugationIdeal.v](rocq/quantum/E8ConjugationIdeal.v#L173-L174) and `T2p` in [E8RootExchange.v](rocq/quantum/E8RootExchange.v#L45)):
   - *Statement*: Under `flipx T2p`, `jp` transforms by the exact same 27-element sign list as `jm_flip_T2`, and `detB_Np` is invariant when `i^2 = -1`, giving the full `N+` counterpart of `RootExchange`.
   - *Falsifier*: Substitute `flipx T2p` into `jp` ([E8ConjugationIdeal.v](rocq/quantum/E8ConjugationIdeal.v#L90-L117)) and compare with `signed (char T2) (jp ...)`; any mismatch falsifies the conjecture.
