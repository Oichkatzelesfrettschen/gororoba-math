# Brief: pull request 93 of gororoba-math, Lean proofs for findings rows A5-228, A5-229, A5-371 and A5-472

Read first: the workspace `AGENTS.md`, the sections "Reviews and merges detail" and "Comments, commits and pull-request detail" of `workspace/reference.md` in gororoba-infrastructure, then `AGENTS.md` of this repository ("Statements and proofs", "Rocq sources"). Work read-only: change no file; never commit, push, stash, submit to a provider or start a cloud resource; spawn no subagents. Run no Lean, Lake, Rocq, opam, Python batch or test suite on the review host; the measured build results are listed below as claims with their evidence class. Keep within 25 minutes.

Material: branch `lean/a5-basis-norm-doubling-commutator`, read through `git diff origin/main...HEAD` and the files in place. The findings ledger is `docs/evidence/a5-exceptional-fibers/ledger.tsv` of gororoba-quantum (rows by id).

The red-team seats received the same brief with one added paragraph: assume each claim is wrong, look for the cheapest refutation (a counterexample at a small level or ring, a vacuous hypothesis, a statement weaker than its docstring, a ledger status that overstates), report only refutations tied to a line or a computation by hand, and say plainly when an attack fails.

## Claims under review (each is a claim, not a fact; justify or falsify it)

1. `Tower.dot_mul_e_mul_e`, `Tower.dot_e_mul_e_mul` and `Tower.dot_mul_e_self_eq_sum` of lean/GororobaMath/CayleyDickson/BasisIsometry.lean state what their docstrings say, and the third is the identity ||L_y e_j||^2 = sum_i c_i^2 of findings row A5-371 at every level. Status: proved (measured: `lake build --wfail` exit 0, `#print axioms` = propext, Classical.choice, Quot.sound, `lake env leanchecker` exit 0; Lean 4.35.0, Mathlib v4.35.0, x86_64). Falsifier: a statement that differs from the row's identity (wrong side of multiplication, wrong form), or a hypothesis that cannot hold.
2. `CayleyDickson.mul_sub_mul_of_star_eq_neg`, `mul_comm_iff_of_star_eq_neg`, `mul_sub_mul_im_of_add_self_eq_zero`, `Tower.dot_mul_dot_eq_of_mul_eq_mul` and `Tower.dot_mul_dot_eq_of_mul_eq_mul_polar` of DoublingCommutator.lean match the commutator formula, the commuting criterion and the norm identity of findings row A5-472 under the product convention of CayleyDickson/Basic.lean. Status: proved (same measurements). Falsifier: a sign or order that differs from the row or from the product (a, b)(c, d) = (a c - star d b, d a + b star c); a reading of N1, N2 + N3 in the docstring that the gororoba-quantum README (docs/evidence/a5-kernel-bundles-residuals/README.md, line 613 on) contradicts.
3. KernelMap/EstimatorReadings.lean states the block readings of rows A5-228 and A5-229: the scales (16 - N^2)/8 and (256 - N^2)/32, exactness iff equal class means with both classes inhabited, and the reading -|B|/2 with B+ empty. Status: proved (same measurements). Falsifier: a scale or sign that differs from the rows; a hypothesis set under which the iff is vacuous or the source sentence is misread.
4. The four rows of ci/claims/ledger.tsv (A5-228 proved; A5-229, A5-371, A5-472 partial) follow ci/claims/README.md: `proved` only where the listed declarations state the whole claim, and each `partial` note names what is open. Status: computed (`python3 ci/check_claims_ledger.py`: 1282 rows match). Falsifier: a part of the A5-228 claim that no listed declaration states; an open part a note omits.
5. No new module needs a README table row, a headline row, a Rocq partner or a challenge module under AGENTS.md. Status: hypothesis (the hosted `lean` workflow, which runs ci/check.sh, is green on the head). Falsifier: a rule of AGENTS.md that the placement breaks.
6. Docstrings and comments follow the comment rules (convention first, mechanism, no session narration).

## Questions to answer

- Defects: code, claims and records, with file:line.
- Does each theorem sit at the generality its proof has (could a hypothesis such as TrivialStar or CommRing be dropped)?
- Conjecture: statements these lemmas suggest that the ledger rows A5-177, A5-238, A5-262 or A5-470 still owe, each with its falsifier and cheapest test.

Report ranked by consequence, every finding tied to a file:line, a command with its output, or a theorem name, each marked proved, computed, measured or hypothesis, with a severity P1 to P3. Print the report as your answer, under 150 lines.
