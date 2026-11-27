# Claims ledger

`ledger.tsv` places each stated mathematical claim of gororoba-open (its claim
registry and its theorem index) and gororoba-quantum (its evidence READMEs,
topic notes and findings ledger) by the clauses of `AGENTS.md` ("Statements
and proofs") and records whether gororoba-math holds a proof of it. The ledger
is the tracker of formal status: a claim that waits on a proof is a row with
status `owed`, and no GitHub issue is opened for it (owner, 2026-11-17).
`ci/check_claims_ledger.py`, run by `ci/check.sh` after
`ci/check_headline_results.py`, checks the file; the headline results of
`ci/headline-results.tsv` are a different registry, whose rows are proved in
both provers.

## Columns

The file is tab-separated with the header line
`source statement quantifier placement clause status proof note`, one row per
claim, sorted by `source` in byte order, sources unique.

| Column | Value |
|---|---|
| source | `gororoba-open:C-NNN` (a claim of `registry/claims.toml`), `gororoba-open:doc:PATH.md:LINE` (line `LINE` of `docs/PATH.md`: a row of the theorem index or a sentence of a commentary), or `gororoba-quantum:docs/PATH:LINE#LABEL` (line `LINE` of that file, with the ledger's label of the claim; for the findings ledger the label is the row's identifier) |
| statement | the claim, at most 30 words; a registry statement is the registry's own text, and one longer than 30 words is cut to 30 with `...` appended |
| quantifier | `every-level`, `fixed-dimension N`, `ring-class`, `concrete-table`, `numeric` or `other` |
| placement | `lean`, `rocq`, `both` or `none` |
| clause | the placement clause that decides it (below), at most 12 words |
| status | `proved`, `partial`, `owed` or `no-proof-owed` |
| proof | semicolon-separated `PATH:NAME` of gororoba-math declarations, or `-` |
| note | what the proof leaves open, or `-`; a `partial` row always says what is open |

## Rules

- `proved` and `partial` rows name at least one proof; `owed` and
  `no-proof-owed` rows hold `-`.
- Placement `none` goes with `no-proof-owed` only, and `no-proof-owed` with
  placement `none` only.
- A proof entry names a theorem, lemma or instance of a tracked module under
  `lean/GororobaMath/`, or a theorem-like command of a Rocq source that a
  `_RocqProject` lists and whose proof ends in `Qed` or `Defined`. The check
  reads both through the lexers of `ci/check_headline_results.py`, so a name in
  a comment, a string or a `Module Type` resolves to nothing.
- `proved` means that the listed declarations together state the whole claim
  at its generality. Each row that reads `proved`, and each row an earlier
  pass had linked to a file without reading its theorems, was re-read against
  the statements of its declarations on 2026-11-17 (131 rows: 28 of the 92
  `proved` rows lost the status, 14 of the 39 file-linked rows gained it, and
  78 rows read `proved` afterwards; the hosted review then added C-001, which
  the every-level Lean theorem proves). A sentence of a claim that reports the
  agreement of code with the stated identity is a measurement and stays
  outside the reading. `partial` means that the proofs
  state an instance, a fixed level or a part of the claim, and the note says
  what is open. `owed` means that the placement
  clauses ask for a proof and gororoba-math holds none that the readings found.
- A new Lean proof entry follows "Proof hygiene" of `AGENTS.md`: pinned
  `simp only`, sized tables bound to their definitions, checked axioms.
- A reference of those readings that did not resolve against `origin/main` is
  repaired to the declaration it meant (nine rows; the first reading named
  `derivation_1..derivation_14` of `CdTowerG2Derivations.v`, whose declarations
  are `G2Derivations.leibniz_basis_N`), or, where it names only a definition
  (`tower_mul` in three rows, a `Definition` that packages a surface in one),
  the row keeps its other proofs and a note, and is `owed` when none remains
  (one row).
- A `no-proof-owed` row that a record of either repository cites as proved
  falsifies its row; no check reads those records, so the falsifier stays open
  for each such row until a record search closes it. Where the earlier
  readings gave a `neither` row a Rocq proof of its own (five rows of
  gororoba-open and two of gororoba-quantum), the row reads `partial` with that
  proof and a note, since a proof is on record.
- The 589 rows of the findings ledger
  `docs/evidence/a5-exceptional-fibers/ledger.tsv` are placed row by row
  (owner, 2026-11-17). A row whose findings status is refuted, superseded,
  stalled, rejected or open is not asserted by its source and reads
  `no-proof-owed`; a method or run record reads `no-proof-owed` as software
  or data; an asserted exact statement about `A_5` or its fiber cones (a
  Hilbert-function value, an ideal equality, a rank, a Cohen-Macaulay or
  reducedness property) is a Rocq certificate and reads `owed`, and a
  statement over every level or a class of fields is owed in Lean. The rows
  read: 9 lean, owed; 10 lean, partial; 1 lean, proved; 184 none, no-proof-owed; 374 rocq, owed; 9 rocq, partial; 2 rocq, proved. The note of an
  owed row says what a proof certifies and carries the findings status, whose
  `proved` and `certified` name a computation; `survives` marks a statement
  the source has not proved.

## Placement clauses

| Clause | Placement | Source in `AGENTS.md` |
|---|---|---|
| Statement over every level or ring class: Lean on Mathlib | lean | Statement: a class of rings or every level `k` |
| Fixed algebra instancing a Lean theorem: stays beside it | lean | Statement: one fixed algebra that instances a Lean theorem |
| Statement of real or complex analysis: Lean on Mathlib | lean | Statement: a statement of real or complex analysis; the ledger also files here a manifold or bundle statement, whose nearest definitions Mathlib holds |
| Fixed finite structure decided by evaluation: Rocq | rocq | Statement: one fixed algebra or coefficient type, a decision by evaluation |
| Certificate evaluated by vm_compute or extracted code: Rocq | rocq | Evidence: a certificate, a compiled definition, floating-point behavior |
| Finite group or combinatorial structure: its library prover | lean or rocq | Statement: a finite group or combinatorial structure goes to the prover whose library holds it (MathComp in Rocq, Mathlib in Lean) |
| Both axes: general Lean theorem and Rocq certificate | both | Both axes: the Lean theorem and the Rocq instance bridge |
| Result already in a proof tree stays where it is | the proof's prover | "A result already in either tree stays where it is" and pinned bytes |
| Outside the clauses: physics, software, data or measurement | none | no clause applies; a physics, software, data or measurement claim |
| Outside the clauses: analogy or interpretation, no mathematical statement | none | no clause applies; the claim is an analogy or an interpretation |
| Outside the clauses: the source does not assert the claim | none | no clause applies; the source marks the claim refuted, superseded, rejected, stalled or open |

A claim that its source marks refuted, superseded, closed, rejected, stalled
or open takes the clause `Outside the clauses: the source does not assert
the claim` whenever it reads `no-proof-owed`, before the other two
`Outside the clauses` rows are considered (195 rows).

`Result already in a proof tree stays where it is` also covers the rows whose
statement class puts them in the other prover: an every-level law that
gororoba-math proves in Rocq keeps the Rocq proof as its home, and the note
says that a Lean statement would be a bridge. No row uses the placement `both`
yet; the clause is the one a claim takes when its general theorem and its
certificate both land.

## Proof files that the registry does not link

`unlinked-proof-files.tsv` (columns `source`, `proof_file`) lists the 101
sources of the form `gororoba-open:doc:THEOREMS.md:LINE`. Each is a Rocq proof
file of gororoba-math that the theorem index of gororoba-open lists with no
registry claim: no claim states what the file proves, so the ledger holds no
statement of it. Their ledger rows read `partial` with up to two theorems of the
file (or `owed` where the file holds definitions and no theorem), quantifier
`other` and the clause `Result already in a proof tree stays where it is`; the
placement follows the file.

The link belongs to the repositories that own the claims: gororoba-open adds,
for each listed file, a registry claim that states what the file proves (its
placement is then reassessed here), and gororoba-quantum does the same for any
file its ledgers cite. The check requires each listed source to be a ledger
row and each file to be a project-listed Rocq source, so the list cannot drift
from the ledger.

## Expected claims

`expected-sources.tsv` (columns `source`, `commit`, `sha256`) lists the claims
the ledger must hold: each source, the commit of its repository at which it
was read, and the sha256 of the source text there (the registry statement,
or the named line). `ci/check_claims_ledger.py` requires the sources of the
ledger to equal the listed ones, so a deleted row, a deleted cohort and a row
that the list lacks each fail the admission gate.

`ci/claims/expected_sources.py` compares the list with the two repositories.
It runs on demand, with `GOROROBA_OPEN` and `GOROROBA_QUANTUM` naming their
checkouts, and reads each file with `git show COMMIT:PATH`: every source
resolves at its commit with the listed digest; a line locator names a
nonempty line that is no first-level heading; a findings-ledger label is the
identifier of its line, and every row of the findings ledger at its commit is
listed; a registry statement equals the ledger statement; and a claim the
registry marks Refuted, Superseded or Closed does not read `proved`. It
calibrates on a known-bad copy for each of these first. `--write` writes the
list again from the ledger sources, which is how a new row or a moved commit
enters it.

The registry of gororoba-open holds 1607 claims at the listed commit and the
ledger holds the 505 that concern the Cayley-Dickson algebras, chosen by the
reading of the registry; the list fixes that choice and does not derive it.
For the findings ledger of gororoba-quantum the list is the whole file.

## Provenance and limits

- The rows come from a reading of the gororoba-open registry (gororoba-open
  `3c04c2eb`) and of the evidence documents of gororoba-quantum
  (`78c780bc6`), classified against `AGENTS.md`; the topic notes
  `cd-star-lattice-tower.md` and `c5-zero-divisor-code-falsification.md` of
  the second pass were read at gororoba-quantum `b7c2b373c`, and the findings
  ledger, whose rows A5-572 to A5-611 the earlier commits lack, at
  gororoba-quantum `57c2c08bf`.
  `expected-sources.tsv` holds the full commit of each source.
- The check proves that each proof entry names a declaration. It does not prove
  that the declaration states the claim; that is the reading recorded under
  "Rules", and a row moves to `proved` only after such a reading.
- The gororoba-quantum pass is partial. Read for rows: the findings ledger
  `docs/evidence/a5-exceptional-fibers/ledger.tsv` (every row), the theorem
  table of `docs/evidence/cd-tower-domain/README.md`, and the topic notes
  `cd-star-lattice-tower.md` and `c5-zero-divisor-code-falsification.md`. Not
  read for rows: the `a5-*` evidence directories and topic notes (their
  claims are the findings-ledger rows), `rank_locus_*`,
  `dimension32_skew_schur`, `stiefel-pfaffian-higher`,
  `hypercomplex-operators`, `sedenion-automorphisms` beyond the rows already
  present, `docs/notes/topics/box-kites/`, `finite-field-qlsa-alternatives.md`
  and `cd-annihilator-varieties-prior-art.md` (a literature survey). A row is
  added when one of these sources states a claim; none is added by sampling.
