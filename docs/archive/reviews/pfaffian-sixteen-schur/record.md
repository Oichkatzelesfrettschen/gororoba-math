# Review record: the 16 x 16 Pfaffian identity by a Schur reduction

Scope: pull request 134 (branch `lean/pfaffian-16`), theorem
`PfaffianSixteenSchur.pfaffian_sixteen`: over every commutative ring,
`Matrix.pfaffian` of the bordered matrix `borderedA z t` on `Fin 16` equals
`rhsv z t`, that is `-(z.t) Q G`. Reviewers, read-only: codex on
gpt-daybreak-blue at head 816595012, agy on Gemini 4 Neon (red team) at head
d01c104d8, then the Advisor.

## Findings

| # | Reviewer | Finding | Verdict |
|---|---|---|---|
| 1 | codex, claim 1; agy, claim 1 | statement, sign convention, index order and right-hand side against `Amat`, `rhs` and `pf_A_eval` of the Rocq trees | justified by both; no change |
| 2 | codex, claim 2; agy, claim 2 | the description "no kernel table" overstates: `sedSign_eq_sign` (210 cases) is decided by `decide +kernel` on the proof path, and `decide` settles the skew symmetry of the table and four index-list equalities | Fixed in 971ad3e81: the module docstring states the evaluated cases; the Pfaffian identity itself is symbolic |
| 3 | codex, claim 2; agy, break 3 | `U != 0` and the left-regularity of 2 are proved in the integer polynomial ring only; the theorem holds in characteristic 2 and 3 and over rings with zero divisors | justified; no change |
| 4 | codex, claim 5 | 106 unrestricted `simp` calls against 47 `simp only` | Fixed in c8c87d887: 145 calls pinned; agy counts 0 bare and 192 pinned at d01c104d8 |
| 5 | agy, defect 4 | the partner citation of `PfaffianSixteen` names `memo` and `check_table` | Fixed in 971ad3e81: the docstring names `Amat`, `rhs` and `pf_A_eval` |
| 6 | agy, hygiene review | seven commits of the branch carry no evidence sentence, two of them after the rule was written | Boundary: pushed commits keep their bytes; the rule now reads "a commit that changes a proof", and the two later commits change documentation only |
| 7 | agy, defect 2 | one commit body line exceeds 72 columns (d01c104d8) | Boundary: a pushed commit keeps its bytes |
| 8 | agy, defect 3 | `pfaffianAux_eight_indices` expands the six-index Pfaffians before `ring` | Boundary: a cost of seconds at compile time, no effect on the statement |
| 9 | agy, hygiene review | the rules on table mutation and on the exact pre-check are not enforced by a gate | Boundary: both ran for this pull request outside the tree; a gate for them is open work |
| 10 | Advisor | `borderedA` and `rhsv` mirror `Amat` and `rhs` of the Rocq trees, and no comparison under `ci/` runs both | Boundary: both reviewers matched the definitions by reading; the comparison lands with the transport to `Tower.czMatrix` (issue 99 step 4), which `ci/compare_cz_matrix.sh` covers |
| 11 | axiom tests | ledger row C-1128 quotes "Constructive proof" while its Lean theorems use `Classical.choice` | Fixed: the row's note states that the Lean proofs are classical and exhibit the witness |

## Axioms

`#print axioms` on the 1,213 constants of the closure lists only `propext`,
`Classical.choice` and `Quot.sound`; a scratch copy of
`ci/check_external_kernels.sh` extended with the theorem (the tracked script
is unchanged) passes its calibration, and con-leche, con-ron and nanoda
accept the export (35 s, 6.8 GB on a compute host). A copy of each sign table
with one entry changed is rejected at `decide`. The Rocq partner over the
integers is closed under the global context.

## Gates

The hosted `lean` and `rocq` workflows are green on 857b45460 (kernel replay
included). Later commits change docstrings, documentation, one ledger note
and merge `main`; the quick workflow (lints, ledgers, the changed-module
build with warnings as errors and the axiom audit) covers the final head.

## Open

Issue 99 steps 4 to 6: the transport to the level-5 product, the theorem over
fields, and the Rocq bridge. Ledger row A5-364 stays partial.
