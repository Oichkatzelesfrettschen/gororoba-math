# Brief: review of gororoba-math PR 151, claims-ledger rows A5-612 to A5-668 and the findings pin at 6d2cdac90

Read first: AGENTS.md, then gororoba-math AGENTS.md ("Statements and proofs": the placement clauses) and ci/claims/README.md (columns and rules). Work read-only: change no file; never commit, push or stash; spawn no subagents; run only git and read commands, each under 10 minutes. Print the whole report as your final answer.

Material: worktree ., branch claims/findings-a5-612-668 (PR 151, head 5d768cc7e); read `git diff origin/main...HEAD -- ci/claims`. Source of each findings row: gororoba-quantum (checkout gororoba-quantum) at commit 6d2cdac90, file docs/evidence/a5-exceptional-fibers/ledger.tsv; read it with `git -C ../gororoba-quantum show 6d2cdac90:PATH`. The previous pin was 57c2c08bf.

## Claims under review (each a claim, not a fact; the falsifier follows each)
1. The 57 added rows A5-612..A5-668 each name the right source line at 6d2cdac90, and their statement is the first 30 words of the source claim, with `...` when it is longer. Falsifier: a row whose line number or statement differs from the source.
2. Each added row carries the quantifier, placement, clause and status that the README rules give for its source status and claim: refuted, superseded or open rows read none / no-proof-owed under "the source does not assert the claim"; exact A_5 statements read rocq / owed; statements over every level or class of fields read lean / owed. Falsifier: a row whose source status or claim class contradicts its placement.
3. Five rows read partial on existing declarations, and each declaration states what the note says it states:
   - A5-627: TwoTermNullity.finrank_ker_mulLeft_e_add_e and finrank_ker_mulLeft_e_add_e_of_charZero.
   - A5-629: the five theorems of lean/GororobaMath/Clifford/AnticommutingPairGram.lean.
   - A5-649: AssociatorCensus.card_assocPhase_true, AssociatorPhase.e_mul_e_mul_e, and Rocq associator_census_formula.
   - A5-658: MultiplicationForms.tripleForm_swap_left, tripleForm_swap_outer and tripleForm_swap_right.
   - A5-661: Associator.mul_self_eq_smul_sub.
   Falsifier: a declaration whose hypotheses or conclusion differ from the note, or a note that calls something proved which no declaration states.
4. No added row that reads owed is in fact proved, or partly proved, by a declaration already on main. Search lean/GororobaMath and rocq/ for the identities of A5-612, 613, 622, 624, 625, 633, 636 and 648 in particular. Falsifier: such a declaration.
5. The 63 relocated rows changed only their source line number. Of the eight rows whose source text changed (A5-026, 151, 315, 544, 546, 548, 560, 598), the four rewritten notes (A5-151, 544, 546, 548) and the new A5-546 statement follow the source changes, and the other four need no change. Falsifier: a relocated row with another change, or a stale note.
6. expected-sources.tsv changes as follows, and the README counts (646 findings rows; 18, 15, 1, 195, 406, 9, 2 by placement and status; 201 rows under the "does not assert" clause) equal the ledger:
   - 57 sources added and none removed;
   - digest changes only at those eight rows;
   - every other findings row changes its commit alone;
   - no gororoba-open, topic-note or scratch-analysis source changes.
   Falsifier: a count or a diff line that disagrees.
7. These placement judgments are flagged as uncertain. For each, give your placement and the clause that decides it:
   - A5-630 and A5-631 as software (none);
   - A5-657 as interpretation (none);
   - A5-667 as Lean real analysis;
   - A5-622 and A5-658 as Lean every-level rows, although the source states finite levels;
   - A5-616, 619, 626, 637 and 664 as quantifier `other` with Rocq certificates;
   - A5-663 as `fixed-dimension 8`;
   - A5-623 as Rocq, with its clause over every field of characteristic 0 or above 32 left to the note;
   - A5-649 as partial rather than proved.

## Report
For each claim: justified or falsified, with file and line evidence. Then any further defect. Then conjectures: structure across these rows that no record states, each with a falsifier and its cheapest test.
