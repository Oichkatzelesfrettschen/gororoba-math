# Brief: gororoba-math PR 121, rocq: sedenion box-kite and annihilator census by evaluation (head 50e39050b)

Read first: the workspace `AGENTS.md` in the directory above the gororoba-math checkout, then the sections "Reviews and merges detail" and "Comments, commits and pull-request detail" of the workspace reference, then gororoba-math `AGENTS.md` ("Statements and proofs", "Rocq sources") and gororoba-math ci/claims/README.md (the rule: "partial means that the proofs state an instance, a fixed level or a part of the claim, and the note says what is open").

Work read-only: change no file except your report; never commit, push, stash, submit to a provider or start a cloud resource; spawn no subagents. The review host runs no builds, proof compiles, test suites or Python batch jobs: read sources and use git only (git diff, git show, grep). Keep the whole review under 40 minutes.

Material: the gororoba-math branch rocq-sedenion-table-census, head 50e39050b); read the change with `git diff origin/main...origin/rocq-sedenion-table-census` and `git show origin/rocq-sedenion-table-census:PATH`. Sources cited by the ledger rows: gororoba-open registry text is quoted in ci/claims/ledger.tsv; gororoba-quantum docs/evidence/box_kite_census/README.md and scripts/box_kite_census.py in the gororoba-quantum checkout beside it.

## Claims under review (each is a claim, not a fact; justify or falsify it)

1. C-946: the zero-divisor participation graph of the sedenions has 84 edges and components of sizes 14, 1, 1, and the graph definition in C946_ZDParticipationGraph.v matches the claim's graph (built from zero products of two-blades, edges among the four indices). Status: computed (vm_compute). Support: rocq/open/verified/C946_ZDParticipationGraph.v:C946_sedenion_zd_participation_graph; author Print Assumptions closed. Falsifier: the Rocq graph differs from the one the claim describes, or the theorem's statement does not say 84 edges and [14;1;1].
2. C-946 no longer depends on Axiom zd_graph_three_components (rocq/open/verified/C958_ZDGraphTopology.v). Status: computed. Support: the new file imports neither C958 nor the axiom. Falsifier: an import path that reaches C958.
3. C014_AnnihilatorCensus.v: cert_ok_sound proves that a certificate accepted by cert_ok yields a kernel basis over the reals, and boxkite_annihilator_census, C014_annihilator_dimension_four and C015_four_diagonal_partners state what the C-014, C-015 and box_kite_census README:52 rows need, modulo the notes. Status: computed; rests on ClassicalDedekindReals.sig_forall_dec and functional_extensionality_dep (listed in rocq/open/kernel-assumptions.txt). Falsifier: kernel_basis does not express span plus independence plus containment, or a statement quantifies over a different blade set than claimed.
4. The ledger statuses: C-946, C-1630 and box_kite_census rows 47, 49, 51, 53, 55 read proved; C-014, C-015, C-1467, C-468 and box_kite_census rows 46, 52 read partial with notes naming what is open. Status: author judgment. Falsifier: a proved row whose claim text asserts something no cited theorem states, or a partial row that is in fact fully stated, or a note that misstates what is open.
5. Box-kite census counts (BoxKiteSignCensus.v, BoxKiteTwoBladeCensus.v): edge totals (42, 42, 21, 0), frustration 0 and 4 per kite, twist (28224, 0, 1344), norm histogram (336, 43428, 336, 0), 42 zero-bearing planes and the 7 (l, l xor 8) planes carrying none. Status: computed. Falsifier: a definition (kite, edge type, frustration, twist, plane) that differs from gororoba-quantum scripts/box_kite_census.py.
6. C1630_BasisAssociatorTensor.v: coefficients in {-2,0,2} with counts (2248, 924, 924); the uniform baseline 25/256 and 231/512 range over all 4096 ordered triples, as scripts/box_kite_census.py:647-648 computes (DIM**3), though the ledger claim text says kite triples. Status: computed. Falsifier: the script restricts to kite triples, or omega differs from the script's c.
7. C1467_OctonionFanoTriples.v and C468_EmanationTable.v state the counts their rows cite (7 and 28 triples; 225 cells, 84 marked, diagonal -1). Status: computed. Falsifier: the definition of "associative" or "marked" differs from the claim.
8. The new files use two product conventions: sed_sign of C1467_XORSignCocycle.v (census, Fano, associator, emanation files) and tz_mul of C1468_SlotEmbeddingAllPairs.v (annihilator and graph files). Status: hypothesis that the proved counts do not depend on which convention. Falsifier: a count that changes between the two conventions.
9. New warning rows in ci/rocq-warnings/allowed.tsv use only names already in ci/rocq-warnings/causes.tsv, and the file stays C-sorted. Falsifier: a new name or an ordering break.

## Questions to answer

- Is any proved status unjustified, or any partial status too weak? Name the row and the missing or present statement.
- Is cert_ok_sound's conclusion strong enough for "dimension 4" (independence plus spanning over the reals)?
- Does any theorem name in a ledger proof cell point at a statement weaker than the row's claim?
- Conjecture where nothing is posited: structure in these counts (the 7 kites, 84 edges, 1344 twist zeros, the e_8 singleton) that no record states; each with its falsifier and cheapest test.
- Defects in the sources, the ledger notes and the PR body, with file:line.

Report ranked by consequence, every claim tied to a file:line, a command with its output, or a theorem name, each marked proved, computed, measured or hypothesis. Print it as your answer, under 150 lines.
