# Review: Cl(0, 8) is isomorphic to the real 16 x 16 matrices

Branch `lean/clifford-0-8-matrix-iso` of gororoba-math (issue 44, item 3). Reviewers by the owner's ruling of 2026-11-18 for new pull requests: the `codex` command-line agent (gpt-daybreak-blue, high effort, read-only) and the Advisor, last.

## Runs

- **Advisor, first read (373a3ba).** It read the declarations and the ledger row, and confirmed the statement is the one issue 44 item 3 asks for: weight -1 on R^8, the lift of v ↦ Σ v_i G_i, and bijectivity from surjectivity and equal finrank. It found one overclaim: the module docstring said two left multiplications anticommute "only" for the octonion block and the doubling unit, and no theorem states that. bdeec98 fixes it; the docstring now scopes the claim to e_1 .. e_8.
- **Codex.** Three runs from 10:00Z to 10:54Z on 2026-11-19 hung at startup, after the plugin sync of the user configuration, and printed nothing, one of them on a trivial prompt. A run with `--ignore-user-config` (same model, effort and sandbox) read bdeec98 and reported no P1, P2 or P3 finding. Claims 1 to 4 were justified: the statement and generators; the three kernel decisions and the finrank argument; the conventions and the C1463 ledger row; the absence of sorry, axioms and `native_decide`. `git diff --check` passes.

## Validation

`sh ci/check.sh` exits 0 on a remote host at 373a3ba, with ruff 0.14.11 and actionlint 1.7.12, the versions the `lean` workflow pins. Its log ends "kernel replay accepted 19 tracked module(s) and rejected the fixture" and "check: passed". bdeec98 changes only a docstring.

## Advisor

The final verdict is recorded at the last call before the merge.
