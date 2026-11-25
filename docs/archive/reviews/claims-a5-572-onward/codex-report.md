**Verdict**
PR 127 at `0c2e44edf` is sound for the reviewed scope. All five claims are justified; no further repository defect was found.

**Claim 1 — Justified**
- All 40 rows A5-572 through A5-611 use the correct pinned source lines: `57c2c08bf:docs/evidence/a5-exceptional-fibers/ledger.tsv:551` through `:590`. Their ledger entries begin at `ci/claims/ledger.tsv:1117` and end at `ci/claims/ledger.tsv:1160`.
- Every statement equals the source claim’s first 30 whitespace-separated words with `...` appended. Every locator line begins with the stated A5 identifier. This satisfies the statement and locator rules at `ci/claims/README.md:22` and `ci/claims/README.md:23`.
- The statuses follow the findings rules at `ci/claims/README.md:67`: superseded or stalled rows are `none/no-proof-owed`; run, digest, replay, and performance records are data with `none/no-proof-owed`; asserted fixed-A5 equalities, ranks, ideals, and structures are Rocq obligations; A5-591 and A5-592 are partial.
- The quantifiers and placements follow the statement-versus-evidence distinction at `AGENTS.md:191`, `AGENTS.md:196`, and `AGENTS.md:211`.
- Mechanical confirmation: `python3 ci/check_claims_ledger.py` passed all 1,327 ledger rows.

**Claim 2 — Justified**
- A5-591 and A5-592 are `partial` and name actual project-listed Rocq declarations at `ci/claims/ledger.tsv:1138` and `ci/claims/ledger.tsv:1139`. Both source files are listed at `rocq/quantum/_RocqProject:61` and `rocq/quantum/_RocqProject:62`.
- A5-591’s declarations exist:
  - `Phi_order4` at `rocq/quantum/E8ConjugationMap.v:397`.
  - `conj_C` at `rocq/quantum/E8ConjugationMap.v:410`.
  - `conj_F` at `rocq/quantum/E8ConjugationMap.v:418`.
  - `conjugation_ideal` at `rocq/quantum/E8ConjugationIdeal.v:181`.
- Its note correctly leaves the transformations of `T`, `W`, and their Pfaffians open. The proved ideal theorem covers every commutative ring at `rocq/quantum/E8ConjugationIdeal.v:46`; the map certificate’s scope is described at `rocq/quantum/E8ConjugationMap.v:13`.
- A5-592’s declarations exist:
  - `detB_Nm` at `rocq/quantum/E8ConjugationMap.v:524`.
  - `detB_Np` at `rocq/quantum/E8ConjugationMap.v:532`.
  - `detB_conj` at `rocq/quantum/E8ConjugationMap.v:540`.
- Its note correctly leaves the 21 specialized unit-polynomial identities at primes 32009 and 32029 open.

**Claim 3 — Justified**
- At the former `b7c2b373c` pin, source A5-542 was `open`; at `57c2c08bf` it is `survives`. The row therefore correctly changes from `none/no-proof-owed` to `rocq/owed` at `ci/claims/ledger.tsv:1084`.
- At the former pin, A5-571 was `open` and explicitly lacked the membership receipt; at `57c2c08bf` it is `certified`. The row correctly changes to a Rocq certificate obligation at `ci/claims/ledger.tsv:1116`.
- These transitions implement the precedence rule for unasserted statuses at `ci/claims/README.md:97`.

**Claim 4 — Justified**
- The comparison against `origin/main` found:
  - 40 added entries, all A5-572 through A5-611 findings-ledger sources.
  - Zero removed source keys.
  - 549 common entries changed; all belong to the findings ledger.
  - 534 changed only their commit and 15 changed both commit and digest.
  - Zero non-findings entries changed.
- Thus the assertion is correct for pre-existing entries, with the necessary qualification that 40 new source rows were also added.
- `QUANTUM_FINDINGS` is defined as `57c2c08bfd013cc6687f135dc47d889f372f521c` at `ci/claims/expected_sources.py:69`, and only the findings ledger uses it at `ci/claims/expected_sources.py:72`.
- Both topic-note paths remain on `QUANTUM_LATER` at `ci/claims/expected_sources.py:73` and `ci/claims/expected_sources.py:74`; their expected-source entries remain pinned to `b7c2b373c`, beginning at `ci/claims/expected-sources.tsv:1311`.
- `python3 ci/claims/expected_sources.py` passed all 1,327 pinned sources.

**Claim 5 — Justified Placements**
- **A5-577:** `none`; `Outside the clauses: physics, software, data or measurement`. It states producer/run digests and selected data, rather than a mathematical proposition. See `ci/claims/ledger.tsv:1122` and source line `57c2c08bf:.../ledger.tsv:556`.
- **A5-588:** `none`; the same data-or-measurement clause. Second-host log and digest reproducibility is runtime evidence. See `ci/claims/ledger.tsv:1134` and source line `:567`.
- **A5-583:** `rocq`; `Certificate evaluated by vm_compute or extracted code: Rocq`. The explicit invertible 21-generator map is a finite certificate for equality of two fixed modular ideals. See `ci/claims/ledger.tsv:1129` and source line `:562`.
- **A5-596:** `rocq`; `Fixed finite structure decided by evaluation: Rocq`. It proposes a fixed A5 graded-ring presentation and character structure, rather than a theorem over a ring class or every tower level. See `ci/claims/ledger.tsv:1143` and source line `:575`.
- **A5-601:** `rocq`; `Certificate evaluated by vm_compute or extracted code: Rocq`. Its evidence consists of exact sampled matrix ranks, Plücker coordinates, and tangent ranks. See `ci/claims/ledger.tsv:1149` and source line `:580`.
- **A5-603:** `rocq`; `Fixed finite structure decided by evaluation: Rocq`. Although quantified over nonzero complex boost parameters, it concerns four fixed A5 closure schemes, fixed ideals, and one explicit algebraic action; it is not a general theorem of complex analysis. See `ci/claims/ledger.tsv:1151` and source line `:582`.
- **A5-590:** `rocq`; `Fixed finite structure decided by evaluation: Rocq`. It states equality of the fixed relation systems in eight modular cells and the resulting fixed ideal dependence law. See `ci/claims/ledger.tsv:1136` and source line `:569`.
- **A5-611:** `rocq`; `Certificate evaluated by vm_compute or extracted code: Rocq`. The claim is the fixed A5 classification obtained from minimal-prime, singular-locus, resolution, and point-count certificates. The cited Del Pezzo–Bertini theorem is a dependency, not a second general claim requiring placement `both`. See `ci/claims/ledger.tsv:1160` and source line `:590`.
- **A5-542:** `rocq`; `Fixed finite structure decided by evaluation: Rocq`. It concerns the fixed E8-bar Rees system over specified modular function fields and a finite multigraded standard-basis computation, not every level or a coefficient-ring class. See `ci/claims/ledger.tsv:1084` and source line `:521`.

**Further Defects**
- None found.
- `git diff --check origin/main...HEAD` passed, and the worktree remained clean.
- `sh ci/check.sh --quick` was not run to a verdict: its initial `mktemp` failed because this review environment mounts `/tmp` read-only. The two claims-specific validators completed successfully, so this is an environment limitation rather than a repository failure.

**Conjectures Suggested by the Rows**
- **Universal conjugation transport:** Phi may induce a graded Rees-algebra and fiber-cone isomorphism between N- at `-r` and N+ at `r` over every commutative ring carrying a square root of `-1`, extending A5-590 through A5-592. **Falsifier:** a coefficient ring or prime where the transformed `T`, `W`, Pfaffian, saturation, or relation ideal differs.
- **E8-bar boost flatness:** The E8-bar-to-VB fiber cone may remain isomorphic in every degree along the full nonzero boost orbit, extending the degree-two and degree-three agreement around `ci/claims/ledger.tsv:1147` and `ci/claims/ledger.tsv:1158`. **Falsifier:** one boost parameter and degree with a changed Hilbert function, Betti table, or minimal-generator count.
- **Linearly joined scroll family:** The E8-bar exceptional quadric fibers may systematically decompose into linearly joined varieties of minimal degree, with A5-611 one member of a common construction. **Falsifier:** another E8-bar incidence whose minimal prime has non-minimal degree, a non-linear intersection, or a non-2-linear resolution.
- **Stable Gauss-image Hilbert data:** The two kernel-Gauss strata in A5-601 may have characteristic-independent 15-dimensional image closures with stable degree-two Hilbert ranks. **Falsifier:** a function-field or third-prime certificate with a different tangent dimension or quadratic-monomial rank.