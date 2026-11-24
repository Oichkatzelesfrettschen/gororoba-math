# Review record: device sign table compared with Tower.sign (pull request 119)

One local reviewer ran, by the owner's selection for this pull request: the `codex` command-line agent on
`gpt-daybreak-blue-latest` at high effort, read-only, on [brief.md](brief.md), reading commit `cc8bff506`. The
Advisor reviewed the reconciliation last. Fixes follow in `5620cbb1e` and `21f10887b`.

## Reviewer findings and reconciliation

| # | Finding (reviewer's class) | Check against the source | Outcome | Advisor |
|---|---|---|---|---|
| 1 | `CUDA_BUILD_DIR` containment is bypassed by a symbolic link: the script compared logical paths, and `/proc/self/cwd` was accepted (measured) | confirmed; `cd DIR && pwd` returns the logical path | fixed in `5620cbb1e`: both paths resolve with `pwd -P`, the nearest existing ancestor is read before `mkdir` and the directory again after it. `/proc/self/cwd`, a link with a missing leaf and the relative `cuda/x` each exit 2 and create nothing | confirmed; asked for the relative-path test, which was added |
| 2 | An unchecked level lets the Lean producer print `4 ^ LEVEL` entries before the device rejects it (proved) | confirmed | fixed in `5620cbb1e`: each level is read against 1 to 10 before a producer runs; 0, 11 and a 20-digit level exit 2 | confirmed |
| 3 | The package conflicts with the evidence axis of `AGENTS.md` ("Statements and proofs"), which makes a certificate that a proof evaluates and a definition compiled to running code Rocq artifacts (proved) | the axis governs a result that the README or a record cites; the package records no result and no certificate, and the guide names no category for a device probe | `cuda/README.md` states that no record cites a device table as a certificate and points at the axis; the guide's wording is the owner's decision | survives as an owner decision, taken before the hosted review |
| 4 | The README called the device result evidence "of a compiled program" (proved) | confirmed; compilation is build evidence and execution is runtime evidence | fixed in `5620cbb1e`: runtime evidence on a named device, driver, toolkit and architecture, for the enumerated inputs | confirmed |
| 5 | The header's exit-status contract is wider than the code: a failing `mkdir`, `mktemp` or `cp` ends the script through `set -e` with that utility's status (proved) | confirmed; every such path still ends nonzero | fixed in `5620cbb1e`: the header states it and the tool check names the utilities | confirmed |
| 6 | "sm_80 and newer" extends three measurements to a range (measured) | confirmed | fixed in `5620cbb1e`: `sm_80` and `sm_89` compile, `sm_75` fails, execution at 8.9 alone | confirmed |

The reviewer's dispositions of the brief's claims: the recurrence equals `Tower.negSign` by induction on the level
with the invariant `negSignFrom fuel level p q acc = acc xor negSign level p q` (source-level argument, not
kernel-checked); the index decomposition is row-major and matches `lean/audit/SignTable.lean`; the level-1 table is
symmetric, and from level 2 on a transposed table differs, so the default levels detect a transposition.

## Advisor findings beyond the reviewer's

| Finding | Outcome |
|---|---|
| The lakefile comment named GCC 15 and 16 for the link failure; it was observed with GCC 16.2 alone | fixed in `21f10887b` |
| The package named a locally linked toolchain with no public install record | fixed in `21f10887b`: release, archive URL, sha256 and the link step are in `cuda/README.md` |
| The comparison runs printed "with uncommitted changes", and their reference table came from a build tree shared with the primary checkout | rerun at `21f10887b` with a clean tree (below); the shared tree is stated below |

## Qualifying run

Commit `21f10887b`, clean tree; RTX 4070 Ti, compute capability 8.9, driver 620.70.06, CUDA 13.4, architecture
`sm_89`; `CUDA_HOME=/opt/cuda CUDA_BUILD_DIR=DIR sh ci/compare_cuda_signs.sh 2 3 4 5 6 8`:

```text
compare_cuda_signs: level 2: 16 signs identical on the device, on its host and in Tower.sign
compare_cuda_signs: level 3: 64 signs identical on the device, on its host and in Tower.sign
compare_cuda_signs: level 4: 256 signs identical on the device, on its host and in Tower.sign
compare_cuda_signs: level 5: 1024 signs identical on the device, on its host and in Tower.sign
compare_cuda_signs: level 6: 4096 signs identical on the device, on its host and in Tower.sign
compare_cuda_signs: level 8: 65536 signs identical on the device, on its host and in Tower.sign
compare_cuda_signs: gororoba-math 21f10887b24a0b92770d159e4e0e7bd5a3846e4e, architecture sm_89, toolchain lean4-cuda-nightly-2026-11-21
```

The reference tables came from the Lake tree of the primary checkout, linked into the worktree for the run, where
the guide gives each worktree a tree of its own; the run built nothing in it. That tree's `Tower` object was built
before four later commits to `Tower.lean` (`61bca3a3f`, `f58c82b89`, `f744c732b`, `d185db672`), which add and remove
theorems and leave `negSign` and `sign` unchanged. As a second reference, the device tables of levels 5 and 8
equal the tables of `cd_sign` of gororoba-quantum at `95a9f95c8`, the function `ci/compare_signs.sh` compares with
`Tower.sign`.
