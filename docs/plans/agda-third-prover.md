# A third prover: Agda next to Lean and Rocq, and Peregrine

This record compares Agda 2.8 (agda-stdlib v2.4 and the cubical library v0.9) with
the two provers of this repository: Lean 4.35 with Mathlib, and Rocq 9.3 with
MathComp 2.6 and the Stdlib. It also tests the candidates where Agda could add
something to the claims of the ledger, and records what Peregrine is and how it
relates to the extraction routes in use. The pilot of the one accepted candidate
is `agda/` (`agda/README.md`), and `ci/check_agda.sh` checks it.

Each cell gives its evidence: a path in a pinned source tree (`file:line`), a
measurement (2026-11-26, a 32-core x86-64 Linux host, single runs), a project's
own documentation, or "not examined". The pinned trees are agda-stdlib v2.4
(commit `2a5a0dec0a3c`), cubical v0.9 (commit `b150186d2544`), Mathlib at the tag
of `lean/lakefile.toml`, and the MathComp 2.6.0 and Stdlib 9.2.0 sources of
the `rocq-9.3` switch of `ci/install_rocq.sh`. Coq-HoTT is read at its GitHub
default branch on 2026-11-26.

## 1. Comparison

### Foundations

| Row | Lean 4 + Mathlib | Rocq 9.3 + MathComp, Stdlib | Agda 2.8 + agda-stdlib, cubical | Reading |
|---|---|---|---|---|
| Axioms the libraries assume | `propext`, `Classical.choice`, `Quot.sound`; the gate admits only these (`AGENTS.md`, "Statements and proofs") | none in the kernel; a tree's axioms are listed per tree (`rocq/*/kernel-assumptions.txt`) | none: every module the pilot imports checks under `--safe` (measured), which refuses postulates (measured, planted copy of `ci/check_agda.sh`) | overlap: all three can work axiom-free; only Lean's library needs choice |
| Impredicativity | impredicative `Prop` (documented) | impredicative `Prop` (documented) | none; `--prop` gives a predicative `Prop` (documented) | Lean and Rocq share it; Agda lacks it |
| Proof irrelevance | definitional for `Prop` (documented) | `SProp` definitional, `Prop` propositional (documented) | irrelevant arguments and `--prop` (documented) | overlap |
| Function extensionality, quotients | quotients primitive, funext a theorem (documented) | funext an axiom of the Stdlib; quotients by setoids or MathComp `quotType` (documented) | funext and set quotients are theorems and HITs under `--cubical` (documented) | cubical Agda proves funext with no axiom: unique, but no claim here needs it |
| Univalence, higher inductive types | inconsistent with definitional irrelevance; absent | consistent only in the Coq-HoTT setting, which MathComp cannot share (documented) | built in under `--cubical`: spheres `S₊ n`, joins, suspensions (`Cubical/HITs/Sn`, `Cubical/HITs/Join`) | unique to cubical Agda among the three set-ups of this repository |

### Computation

| Row | Lean | Rocq | Agda | Reading |
|---|---|---|---|---|
| Evaluation inside a proof | `decide +kernel`; a 210-goal table at 0.54 s and a Pfaffian memo table that exceeded 16 GiB (`AGENTS.md`, "Proof hygiene") | `vm_compute`, 3.4 to 8.5 times faster than `decide +kernel` on the sign tables (`docs/archive/measurements/h1-vm-compute-decide-kernel.md`); the Stiefel Pfaffian certificate in 104 s | the type checker's evaluator; the pilot normalises 24 octonion coordinate identities of degree 4 in 24 variables, with the rest of the module, in 151 s at 0.70 GB (measured) | Rocq's `vm_compute` stays the certificate engine; Agda's evaluator suffices for polynomial identities of this size |
| Code tied to proofs | compiled code, not tied (`AGENTS.md`, evidence axis) | built-in `Extraction`; CertiRocq and verified extraction on Rocq 9.1 (skill `extract-verified-rocq-code`) | GHC and JavaScript back ends, unverified; `agda2lambox` into Peregrine, unverified (Peregrine README, "Frontends") | unique to Rocq |
| Independent checkers | `leanchecker` and three external kernels (`ci/check_external_kernels.sh`) | `rocq check` (`ci/check_rocq.sh`) | none ships with Agda 2.8; the type checker is the whole trusted base. 103 issues labelled `false` in agda/agda, 11 open, 27 opened since 2025-01-01 (GitHub search, 2026-11-26) | Lean and Rocq have independent checkers; Agda has none |

### Proof style and safety switches

| Row | Lean | Rocq | Agda |
|---|---|---|---|
| Tactics against terms | tactic framework with `simp`, `grind`, `ring`, `decide` | Ltac, Ltac2, SSReflect, `lia`, `ring` | terms only; reflection macros (`Tactic.RingSolver`) and proof by reflection, as in the pilot |
| Dependent pattern matching | equation compiler | `Equations` plugin | native, with `with`-abstraction and copattern definitions |
| Switches | axiom report (`#print axioms`, `lean/AxiomAudit.lean`) | `Print Assumptions`, `rocq check` axiom ledgers | `--safe`, `--without-K` / `--cubical-compatible` (agda-stdlib `README.md:72`), `-Werror` |

### Library content for the mathematics of this repository

| Subject | Lean + Mathlib | Rocq + MathComp, Stdlib | Agda | Reading |
|---|---|---|---|---|
| Quasigroups, loops, Bol and Moufang loops | none: "we don't have `Loop`, or `Quasigroup`" (`Mathlib/Algebra/HierarchyDesign.lean:40`), no source match for Moufang; `Mathlib/Algebra/NonAssoc` holds `LieAdmissible` and `PreLie` only | none (no source match in MathComp 2.6.0 or the Stdlib) | agda-stdlib since v2.0 (`CHANGELOG/v2.0.md:1961`, `:2194`): `IsQuasigroup`, `IsLoop`, `IsLeftBolLoop`, `IsRightBolLoop`, `IsMoufangLoop`, `IsMiddleBolLoop` (`src/Algebra/Structures.agda:1018-1093`), the laws `LeftBol`, `RightBol`, `MiddleBol`, `Identical` (`src/Algebra/Definitions.agda:231-241`), and the derived Moufang identities, flexibility and alternativity (`src/Algebra/Properties/MoufangLoop.agda:18-54`) | unique to Agda |
| Alternative, flexible and non-associative rings | `NonUnitalNonAssocRing` and the classes this repository's tower uses; alternativity is a theorem of the tower (`lean/GororobaMath/CayleyDickson/Alternative.lean`) | rings are associative (`AGENTS.md`, "Statements and proofs") | `IsAlternativeMagma`, `IsFlexibleMagma` (`src/Algebra/Structures.agda:75`, `:88`), `IsNonAssociativeRing` (`:844`) | Lean and Agda overlap; Agda names the predicates, Lean holds the theorems |
| Cayley-Dickson algebras, octonions | none in Mathlib beyond Degen's eight-square identity (`Mathlib/Algebra/Ring/Identities.lean`); this repository's `Tower` | none in MathComp; this repository's `rocq/open` and `rocq/quantum` towers | none in agda-stdlib or cubical (no source match); Coq-HoTT has a synthetic construction, below | the repository's own towers are the only ones |
| Quaternions | `Mathlib/Algebra/Quaternion.lean` | the quaternion group only (`mathcomp/solvable/extremal.v:19`), no quaternion algebra | none | Lean |
| Linear algebra, matrices | extensive (`Matrix`, determinants, rank) | `mxalgebra`, rank and kernels, computable | agda-stdlib minimal; cubical has integer matrices with Smith normal form (`Cubical/Algebra/IntegerMatrix/Smith.agda`) | Lean and Rocq |
| Polynomials, ideals | `Polynomial`, `MvPolynomial`, `Ideal` | `poly`, ideals | cubical: `Cubical/Algebra/Polynomials/Multivariate`, commutative-ring ideals; agda-stdlib none | Lean and Rocq |
| Finite fields | `GaloisField`, `ZMod` | `finfield` | cubical: a field structure (`Cubical/Algebra/Field/Base.agda`); no finite-field theory found | Lean and Rocq |
| Spheres, H-spaces, Hopf fibrations, homotopy groups of spheres | topological spheres, `Mathlib/Topology/Homotopy/HSpaces.lean` (H-spaces; its TODO names the H-space spheres S^0, S^1, S^3, S^7 as unproved), `HomotopyGroup.lean`, fiber and vector bundles; no K-theory (the ledger's bundle rows say so) | MathComp none; Coq-HoTT, outside this repository's switch: `theories/Homotopy/HSpace.v`, `Hopf.v`, `PiSpheres.v`, and `CayleyDickson.v` (the Buchholtz-Rijke construction: an H-space on the join of two suspensions, giving the quaternionic Hopf fibration) | cubical: `Cubical/Homotopy/HSpace.agda:20` (`HSpace`), `:128` (`S1-HSpace`), the Hopf construction from any H-space (`Cubical/Homotopy/Hopf.agda:194`, `IsoTotalSpaceJoin`), π3(S2) ≅ ℤ (`Cubical/Homotopy/Group/Pi3S2.agda:166`), π4(S3) ≅ ℤ/2 (`Cubical/Homotopy/Group/Pi4S3/Summary.agda`), the Hopf invariant of the Hopf map (`Cubical/Homotopy/HopfInvariant/HopfMap.agda:561`); no H-space structure on S^3 or S^7 and no Stiefel manifold (no source match) | synthetic homotopy is strong in cubical Agda and in Coq-HoTT; neither holds Stiefel manifolds, G_2 or K-theory |
| Hopf invariant one, division algebras | none | none | the Hopf invariant is defined (`Cubical/Homotopy/HopfInvariant/Base.agda:278`); the Hopf invariant one theorem is not formalized (no source match for Adams or invariant one) | none of the three |

### Build and gate cost

| Item | Lean | Rocq | Agda |
|---|---|---|---|
| Toolchain install | elan and the Mathlib cache, about 7 GB of build tree (`AGENTS.md`, "Toolchain and build tree") | opam switch of `ci/install_rocq.sh` | one static 55 MB binary, unpacked in 1 s (measured) |
| Library | Mathlib cache download | MathComp from opam | agda-stdlib checkout 14 MB; its 162 interface files for the pilot, 33 MB, built in about 37 s (measured, cold run 191.6 s against warm 154.5 s); cubical `Cubical.Homotopy.Hopf` cold in 59.3 s at 0.88 GB, 185 interface files (measured) |
| Gate | `quick` 11 s, `build` 342 s, hosted `lean` 15 to 49 min (`AGENTS.md`, "Landing") | hosted `rocq` 67 min | `ci/check_agda.sh` 312.9 s at 0.70 GB with both planted copies (measured) |

## 2. What Agda would add here

The test of a candidate is whether it states a claim of the ledger that neither
prover states, or adds assurance that the existing checks lack.

- (a) Accepted. The unit octonions as a Moufang loop: row C-578 of the ledger
  is `partial`, and its note names the missing packaging: unit, inverses,
  closure of the unit-norm subtype, and unique solutions of `a x = b` and
  `y a = b`. agda-stdlib holds the structure and its theory, and neither Lean
  nor Rocq here holds either. The pilot proves the packaging over every
  commutative ring, and the claim's three identities and the unique solutions
  follow from the library (`agda/README.md`). It also states
  non-associativity inside the unit set, conditional on `1 + 1 ≠ 0`. The
  nucleus and the real instance stay open.
- (b) Rejected. The Cayley-Dickson doubling on agda-stdlib bundles, with the
  laws that survive each doubling: the Lean tower already states those laws at
  every level over `NonAssocRing` with `StarRing` (`Alternative.lean`,
  `FlexibleLaw.lean`, `DivisionLevels.lean`), so the Agda version would
  restate them. The pilot's `Doubling.agda` serves only as a computing device.
- (c) Rejected. Synthetic S^1, S^3, S^7 and the Hopf fibrations. Cubical holds
  the H-space on S^1, the Hopf construction and π3(S2), π4(S3), but no
  H-space on S^3 or S^7. Coq-HoTT, a Rocq library, holds the Buchholtz-Rijke
  construction that the octonionic case needs. The topology rows of the
  ledger (A5-381, A5-383, A5-385, A5-386, A5-394, A5-396, the kernel-bundle
  classes) are statements about `V_2(R^7)`, `G_2`, vector bundles and their
  K-classes. No library of the three defines those objects, and a synthetic
  type does not state a claim about a manifold without a bridge to the
  manifold. None of the rows can be expressed in cubical Agda as it stands.
- (d) Rejected. A `--safe --without-K` proof as an axiom-free third check of
  a small headline theorem. The Rocq partners already depend on no axiom, and
  Lean's theorems are re-checked by three external kernels. Agda has no
  independent checker, and 103 issues labelled `false` mark inconsistencies
  found in its type checker, so a third proof adds implementation diversity
  and less assurance than `rocq check` or an external Lean kernel.

## 3. Peregrine

- What it is: a middle end for code generation from proof assistants, on the
  untyped `λ□` (LambdaBox) of MetaRocq's verified erasure
  (github.com/peregrine-project/peregrine-tool, README, read 2026-11-26).
  - Front ends: Rocq through verified erasure; Agda through `agda2lambox`,
    unverified, which needs Agda 2.8.x built with `+debug` and GHC 9.10.1;
    Lean through `lean-to-lambdabox`, partially verified.
  - Back ends: C through CertiRocq (verified compiler, unverified printer);
    Wasm (verified compiler and printer); OCaml through verified extraction to
    Malfunction; CakeML; Rust and Elm (verified typed erasure, unverified
    printers); experimental Lean, F# and Koka (unverified).
  - The README states that some pipeline preconditions of the middle end are
    admitted (`theories/erasure/Transforms.v`).
  - Two documents of the project disagree on the OCaml back end. The README
    says its glue assumes the axiom `trust_coq_kernel`, and `doc/dependencies.md`
    says the pinned fork of verified extraction removes that axiom.
- Papers: OpenAlex lists no paper on Peregrine (search of 2026-11-26). The
  verified OCaml route rests on Forster, Sozeau and Tabareau, "Verified
  Extraction from Coq to OCaml", PACMPL 2024 (doi 10.1145/3656379).
- Relation to the routes of the skill `extract-verified-rocq-code`: Peregrine
  composes the same two projects behind one command, CertiRocq for C and Wasm and
  MetaRocq verified extraction for OCaml. It pins its own forks: CertiRocq
  `eee949ef`, verified extraction `f999f40c`, and the unreleased MetaRocq
  snapshot `51b14e4b`.
- Rocq 9.3: no. `rocq-peregrine.opam` requires `rocq-core >= 9.1 & < 9.2~`
  and OCaml 4.14. The `rocq-released` opam repository holds no
  `rocq-peregrine` package (GitHub API 404 on 2026-11-26), so the README's
  `opam install rocq-peregrine` fails and a source build with the pins is the
  only route.
- Lean 4.35: unsettled. `lean-to-lambdabox` `main` names `v4.35.0` in its
  `lean-toolchain`. Peregrine's tests pin commit `42f8f510` at `v4.22.0`
  (`test/lean/lean-toolchain`), so the pair Peregrine tests is 4.22.
- Install: not attempted. The build needs MetaRocq, CertiRocq with CompCert
  3.17, Vellvm, WasmCert, the typed-extraction and CakeML back ends and
  verified extraction, from unreleased pins. MetaRocq alone took 35 min at 3
  jobs (skill `extract-verified-rocq-code`, `references/pipelines.md`), so
  the one-hour bound fails. The steps, in a switch of its own:
  `opam switch create peregrine ocaml-variants.4.14.2+options ocaml-option-flambda`,
  then `opam repo add rocq-released https://rocq-prover.org/opam/released`, a
  clone of peregrine-tool at a recorded commit, `opam install ./rocq-peregrine.opam`
  (which applies its `pin-depends`), and `peregrine ocaml FILE.v --entry run`.
- The owner's experiment, through the routes already installed: the Pfaffian
  memo-table checker of `rocq/quantum/StiefelA5Certificate.v`, with
  `certificate_ok` dropped and `run := check_table table` extracted. The
  extracted code is "extracted from a closed definition". No specification
  theorem relates `run` to the Pfaffian identity outside the kernel. A run is
  a runtime expectation for one input, not a certificate.

| Route | Toolchain | Run | Peak memory | Result | Mutant (`rhs` without its sign) |
|---|---|---|---|---|---|
| `vm_compute` in the proof | Rocq 9.3.0 | 104 s (compile of the file, `AGENTS.md`) | 549 MB | proof | - |
| built-in `Extraction` to OCaml | Rocq 9.3.0, OCaml 5.5.1, `ocamlfind ocamlopt` | 12.7 s | 85 MB | `true` | `false`, 12.8 s |
| verified extraction to Malfunction | Rocq 9.1.1, OCaml 5.3.0, `malfunction cmx` | 19.9 s | 142 MB | `true` | `false`, 19.9 s |

The verified route moves the checker's trusted base to the verified-extraction
pipeline theorem, its declared axioms, Malfunction and the OCaml compiler. It
needs the source to compile on Rocq 9.1, which this Stdlib-only file does.
Lean compiled code has no proof tie (`AGENTS.md`, evidence axis), so a Lean
run of the same table sets a cost expectation of the same class as built-in
extraction (not run).

## Decision for the owner

Keep Agda out of the admission gates. Its one gain here is a community-reviewed
Moufang loop interface for C-578. Two routes deliver it with no third gated
prover:

- Land `agda/` and `ci/check_agda.sh` as an on-demand check, as the other
  comparisons under `ci/` run.
- Port the packaging to Lean through a structure that copies the fields of
  agda-stdlib's `IsMoufangLoop`, keep the Agda pilot as the cross-check
  against the library's definition, and let the claims ledger cite the Lean
  declarations under its present rules.
