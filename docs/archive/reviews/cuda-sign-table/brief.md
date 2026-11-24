# Brief: gororoba-math pull request 119, cuda: device sign table compared with Tower.sign

Read first: the workspace `AGENTS.md`, then the sections "Comments, commits and pull-request detail" and "Reviews and merges detail" of the workspace reference (`workspace/reference.md` of the infrastructure repository), then AGENTS.md of this repository. Work read-only: change no file; never commit, push, stash, submit to a provider or start a cloud resource; spawn no subagents. You may run git, grep, shellcheck and read files. Do not build Lean, do not run lake, nvcc or any GPU program, and do not run ci/check.sh; this host runs no builds. Keep each command under 2 minutes.

Material: this worktree, branch cuda-sign-table-kernel at commit cc8bff506511f0860298d0ef7b09ea7f3accde55. Read the change with `git diff origin/main...HEAD`. Files: cuda/SignTable.lean, cuda/lakefile.lean, cuda/README.md, cuda/lean-toolchain, cuda/.gitignore, ci/compare_cuda_signs.sh. Reference definitions: lean/GororobaMath/CayleyDickson/Tower.lean (negSign, sign), lean/audit/SignTable.lean, ci/compare_signs.sh, ci/check_signal_traps.sh, ci/check.sh.

## Claims under review (each is a claim, not a fact; justify or falsify it)

1. `negSignFrom 32 k p q false` in cuda/SignTable.lean equals `Tower.negSign k p q` for every level k from 1 to 10 and all indices below 2^k. Status: computed (tables identical at levels 3, 4, 5, 6, 8 on a device and its host). Support: the two definitions. Falsifier: a level and pair where the four-case recursion, the swap of arguments, the flip, or the early `true` case differs, including pairs whose low parts are zero.
2. The kernel index decomposition `p = t >>> level`, `q = t &&& (2^level - 1)` and the host printing loop place entry (p, q) at row p, column q, the format of lean/audit/SignTable.lean. Status: computed. Falsifier: a transposed or offset table that the comparison would still accept (consider symmetric structure of the table).
3. ci/compare_cuda_signs.sh fails closed: a missing tool, a failed build, a device program that exits with a status other than 0 or 3, an empty table and a differing table each end in a nonzero status, and the negated-entry control runs before any verdict. Status: hypothesis. Falsifier: an input or failure for which the script prints "identical" or exits 0 wrongly; a path where `set -e` ends the script without its message; a trap form ci/check_signal_traps.sh rejects.
4. The admission gate (ci/check.sh and the lean workflow) neither builds nor audits anything under cuda/, and no rule of the gate or of AGENTS.md is broken by a Lean file outside lean/. Status: hypothesis. Support: ci/check.sh takes modules from `git ls-files lean/GororobaMath`. Falsifier: a gate step, a text check or a guide rule the new files violate (ASCII rule for Markdown and shell, license headers, comment voice, a required AGENTS.md entry for a comparison script).
5. The comments and README state mechanisms and measured values in the voice the instruction files require, and carry no host name, local absolute path, private repository text or product-comparison framing. Status: hypothesis. Falsifier: a line that breaks one of those rules, with file:line.

## Questions to answer

- Defects: code, claims and records, with file:line, ranked by consequence.
- Is the statement in cuda/README.md about evidence class (a device result is a candidate until a kernel-checked proof or exact comparison accepts it) precise, or does any sentence overclaim?
- Does the CUDA_BUILD_DIR containment check in ci/compare_cuda_signs.sh hold for symbolic links and for a relative path?

Print the report as your answer, under 120 lines, every finding tied to a file:line or a command with its output, each marked proved, computed, measured or hypothesis.
