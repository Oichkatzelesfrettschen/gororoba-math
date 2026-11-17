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
| source | `gororoba-open:CLAIM_ID`, `gororoba-open:doc:PATH:LINE` (a proof file that the theorem index of gororoba-open lists), or `gororoba-quantum:PATH:LINE#LABEL` |
| statement | the claim, at most 30 words (a longer statement is cut and ends in `...`) |
| quantifier | `every-level`, `fixed-dimension N`, `ring-class`, `concrete-table`, `numeric` or `other` |
| placement | `lean`, `rocq`, `both` or `none` |
| clause | the placement clause that decides it (below), at most 12 words |
| status | `proved`, `partial`, `owed` or `no-proof-owed` |
| proof | semicolon-separated `PATH:NAME` of gororoba-math declarations, or `-` |
| note | what the proof leaves open, or `-` |

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
- `proved` means that a listed proof covers the whole statement as the
  earlier readings of the two source tables judged it. `partial` means that a
  proof covers an instance, a fixed level, a part of the statement or only a
  file-level link, and the note says which. `owed` means that the placement
  clauses ask for a proof and gororoba-math holds none that the readings found.
- A reference of those readings that did not resolve against `origin/main` is
  repaired to the declaration it meant (nine rows; the first reading named
  `derivation_1..derivation_14` of `CdTowerG2Derivations.v`, whose declarations
  are `G2Derivations.leibniz_basis_N`), or, where it names only a definition
  (`tower_mul` in three rows, a `Definition` that packages a surface in one),
  the row keeps its other proofs and a note, and is `owed` when none remains
  (one row).
- A `no-proof-owed` row that a record of either repository cites as proved
  falsifies its row; no check reads those records, so the falsifier stays open
  for each such row until a record search closes it.

## Placement clauses

| Clause | Placement | Source in `AGENTS.md` |
|---|---|---|
| Statement over every level or ring class: Lean on Mathlib | lean | Statement: a class of rings or every level `k` |
| Fixed algebra instancing a Lean theorem: stays beside it | lean | Statement: one fixed algebra that instances a Lean theorem |
| Fixed finite structure decided by evaluation: Rocq | rocq | Statement: one fixed algebra or coefficient type, a decision by evaluation |
| Certificate evaluated by vm_compute or extracted code: Rocq | rocq | Evidence: a certificate, a compiled definition, floating-point behavior |
| Finite group or combinatorial structure: its library prover | lean or rocq | Statement: a finite group or combinatorial structure goes to the prover whose library holds it (MathComp in Rocq, Mathlib in Lean) |
| Both axes: general Lean theorem and Rocq certificate | both | Both axes: the Lean theorem and the Rocq instance bridge |
| Result already in a proof tree stays where it is | the proof's prover | "A result already in either tree stays where it is" and pinned bytes |
| Outside the clauses: physics, software, data or measurement | none | no clause applies; a physics, software, data or measurement claim |
| Outside the clauses: analogy or interpretation, no mathematical statement | none | no clause applies; the claim is an analogy or an interpretation |

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

## Provenance and limits

- The rows come from a reading of the gororoba-open registry (gororoba-open
  `f81aba2b`) and of the evidence documents of gororoba-quantum
  (`78c780bc6`), classified against `AGENTS.md`; the topic notes
  `cd-star-lattice-tower.md` and `c5-zero-divisor-code-falsification.md` of
  the second pass were read at gororoba-quantum `b7c2b373c`.
- The check proves that each proof entry names a declaration. It does not prove
  that the declaration states the claim: a row whose note reads `theorems named
  by file prefix` links a file, and a reader confirms the statement before the
  row moves to `proved`.
- The gororoba-quantum pass is partial. Not read for rows: the findings ledger
  `docs/evidence/a5-exceptional-fibers/ledger.tsv` beyond the rows that cite
  `rocq/quantum` (about 540 computer-algebra rows over finite fields), the
  `a5-*` topic notes and evidence directories that the earlier pass named as
  skipped, `docs/notes/topics/box-kites/`, `finite-field-qlsa-alternatives.md`
  and `cd-annihilator-varieties-prior-art.md` (a literature survey). A row is
  added when one of these sources states a claim; none is added by sampling.
