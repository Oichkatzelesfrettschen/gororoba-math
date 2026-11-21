# Review: external-kernel check of the headline theorems

Pull request 91 of gororoba-math. Reviewers: the `codex` command-line agent (gpt-daybreak-blue, high effort, read-only) on head c60585b, then the Advisor last. The owner's ruling of 2026-11-18 sets the chain at local codex and the Advisor.

| Finding (codex, c60585b) | Check | Resolution |
|---|---|---|
| P1: an empty or unreadable headline inventory passes with exit 0 | Confirmed: the loop runs zero times | 91c7746: the parsed rows must be nonempty, and the number of theorems checked must equal the number of rows; each read failure exits 2 |
| P1: an export is not tied to the requested names; a broken exporter could return any acceptable file | Confirmed | 91c7746: `ci/external_kernel_export.py` requires each requested theorem to be declared as a theorem in the export. It also requires the export to declare no axiom outside the allow list, since con-leche and con-ron accept a declared axiom, and to declare something. Fidelity of `leanexport` stays a stated trust boundary |
| P2: nanoda status 101 with a `src/tc.rs` panic is not specific to rejection | Confirmed: the pinned source panics on internal invariants as well | 91c7746: con-leche (`invalid:`) and con-ron (`rejected:`) report rejections by name and drive the verdict. A nanoda failure counts as not accepted. Any other checker outcome exits 2 |
| P2: the installer compares the logical path, so a symbolic link escapes the containment check | Confirmed | 91c7746: the installer is removed; the tools come from the toolchain |
| P2: "lean4lean has no 4.35 port" is false; the 4.35 toolchain bundles `lean4lean` | Confirmed: `bin/` of v4.35.0 holds `lean4lean`, `leanchecker-paranoid`, `leanexport`, `con-leche`, `con-ron` and `nanoda_bin` | 91c7746: the check uses the bundled tools, and the record scopes the lean4lean failure to upstream commit 67f63b0 |
| P2: the PR body credits 34 modules to c60585b, which has 108 rows in 33 modules | Confirmed: the 110 and 34 run was at b00bb43 | The PR body states the 91c7746 run: 108 theorems in 33 modules |
| P3: setup failures exit 1, and `set -e` does not protect `check` inside `$(...) \|\| :` | Confirmed | 91c7746: `mktemp`, `cd` and `lake env lean --print-prefix` failures exit 2, and every command in `check` is guarded |

## Advisor

The Advisor confirmed the seven codex findings and the rewrite at 91c7746, and asked for three changes before the pull request leaves draft. All three are done in 2df618d:
- **The axiom rationale was unmeasured.** On the export of `AuditFixture.usesDeclaredAxiom`:
  - con-leche exits 2, "not implemented yet: non-standard axiom";
  - con-ron exits 2, "declined: non-standard axiom";
  - nanoda exits 1, "unpermitted axiom".
  The script, the record and AGENTS.md now state these measured refusals in place of the claim that the checkers accept declared axioms. The calibration also requires the export check to refuse that axiom.
- **The soundness claims were the tools' help text.** They are attributed to `--help`, and the record states con-ron's remaining hypothesis: the driver runs the extracted stages in the order it does on the file's bytes.
- **The record lacked the 91c7746 run.** It now carries that run (108 theorems in 33 modules). It also carries the 4.33.1 archive closure of 36,631 declarations that all four checkers accepted, which bounds the claim that the 4.35.0 checkers read 4.33.1 exports.
