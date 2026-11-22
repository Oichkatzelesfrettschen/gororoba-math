# Brief: rocq/open SedenionNonAlternative.v, successor of SedenionAlternativityFails.v (gororoba-math PR 92)

Read first: the workspace AGENTS.md (gororoba-infrastructure workspace/AGENTS.md), then the sections "Reviews and merges detail" and "Comments, commits and pull-request detail" of gororoba-infrastructure workspace/reference.md, then this repository's AGENTS.md ("Rocq sources", "Statements and proofs"). Work read-only: change no file except your report (named at the end); never commit, push, stash, submit to a provider or start a cloud resource; spawn no subagents. You may run git and read files. Do not compile: this host runs no proof builds. The hosted rocq workflow of the pull request is the build record. Keep each command under 5 minutes.

Material: branch rocq-open-sedenion-non-alternative of this repository. Review `git diff origin/main...HEAD` at head f3f21c99e: rocq/open/theories/SedenionNonAlternative.v (new), rocq/open/_RocqProject (one line), ci/rocq-warnings/allowed.tsv (two rows), README.md (source counts). The predecessor is rocq/open/theories/SedenionAlternativityFails.v; the product, basis and signs are in rocq/open/theories/Sedenion.v, CDSignBridge.v and CDFusedBilinear.v.

## Claims under review (each is a claim, not a fact; justify or falsify it)

1. sed_sign 1 10 = -1 and sed_sign 1 11 = 1, where sed_sign i j = cd_sign_fuel 5 16 i j. Status: proved by vm_compute (theorems sed_sign_1_10, sed_sign_1_11). Falsifier: a different value of cd_sign_fuel at those arguments, or sed_sign defined otherwise in Sedenion.v.
2. SedenionAlternativityFails.v declares both of those signs as +1, and its existential conclusion does not mention sed_mul. Status: claimed in the new file's header. Support: the predecessor's source. Falsifier: the predecessor's constants or statement read otherwise.
3. sed_basis_unit_left_alternative: for every basis unit e_i (i < 16) and every sedenion y, e_i (e_i y) = (e_i e_i) y. Status: proved (the hosted rocq workflow compiled and kernel-checked it). Falsifier: a basis index and y with a nonzero left alternator, or a statement whose quantifiers are narrower than the header says.
4. sed_left_alternator_witness: with a = e_1 + e_10 and b = e_4, (a a) b - a (a b) = 2 e_15. Status: proved. Falsifier: a hand computation from sed_sign and the XOR basis rule giving another value.
5. sedenion_not_left_alternative: some a, b have (a a) b <> a (a b). Status: proved from 4. Falsifier: a proof step that uses a hypothesis the statement hides.
6. The header's convention paragraph matches Sedenion.v (the doubling formula, the basis, e_i e_j = sed_sign i j e_(i xor j) via CDFusedBilinear.sed_mul_fused_basis_xor). Falsifier: a mismatch with those definitions.
7. The two allow-list rows are admissible under the repository rule "a new source adds rows only for warning names that causes.tsv already lists", and the new source's only warnings come from Stdlib Reals at the Require line. Falsifier: another warning, or a cause row that does not cover this source.
8. README: rocq/open lists 373 sources (190 theories, 183 verified). Falsifier: `git ls-files` or _RocqProject counts that differ.

## Questions to answer

- Does any retained record of gororoba-open or gororoba-quantum cite SedenionAlternativityFails.v by sha256 such that the successor needs a pointer (the predecessor keeps its bytes)? `git grep` in gororoba-open and gororoba-quantum.
- Is the statement at the generality its proof has (AGENTS.md "Statements and proofs")? Would a Lean partner be owed under the headline-results rules?
- Comment and docstring voice against the repository and workspace rules.
- Defects in the code, the claims and the records, with file:line.

Report ranked by consequence, every claim tied to a file:line, a command with its output, or a theorem name, each marked proved, computed, measured or hypothesis. Print it as your answer, under 120 lines.
