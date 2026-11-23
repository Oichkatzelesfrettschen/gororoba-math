# Review record: instance bridges of three fixed-level certificates (pull request 94)

Brief: `brief.md` beside this file. The local seats read commit cf05fea37. Reviewer: the `codex` command-line agent on gpt-daybreak-blue at high effort. Red-teamers: `agy` on gemini-4-neon-high, on the red-team paragraph of the brief; `agy` on gemini-3.8-flash-high was not run (the service answered 429, individual quota reached). The Advisor reviewed last, at 2e1570453, with every finding and its resolution. The fixes are in 2e1570453.

| Finding | Seats | Check | Resolution |
|---|---|---|---|
| The W8 kernel bridge states `h(2) a_l = 0` and leaves `a_l = 0` and the membership of the vectors in the kernel unstated, so its theorems are not the three parts of the Lean `Basis` | codex (P1), Neon (P2) | Confirmed against `Tower.ker_mulLeft_basis_of_certificate` | Fixed in 2e1570453: `CanonicalKernelsBridge.W8_kernel_vectors` and `W8_vectors_independent`, which concludes `a l = D.zero` where `h(2)` has an inverse; both are closed under the global context at `Zmod7` |
| The header of the ideal bridge calls the Rocq statement narrower in the ideal; `is_ideal` asks for no membership of zero, so the empty predicate satisfies it | codex (P1), Neon (P2) | Confirmed against `Twisted.is_ideal` and Mathlib's `Ideal` | Fixed in 2e1570453: the header and plan row 121 say that the theorem holds at every Lean `Ideal`, read as its membership predicate, and is wider in the ideal; the statement keeps the form of the cited source theorem |
| Row A5-500 is overstated as `proved`: the certificate theorem does not state `F` in the span where 6 is a nonzero divisor, and the Gaussian instance was unlisted | Neon (P1), codex (P2) | Confirmed: over a ring where 6 is regular and not a unit, the three clauses of `derivation_dimension_certificate` do not give a free module on the tables | Fixed in 2e1570453: the row reads `partial` and names `derivations_spanned_gaussian` and `derivations_independent`; its note says which conjunction no single theorem states |
| Row A5-453 omits `G2Derivations.derivation_1` to `derivation_14`, the transported Leibniz rule | Neon (P3) | Confirmed | Fixed in 2e1570453 |
| `A5W8ArcMatrixRanksBridge.v` holds a non-ASCII character in its header | Neon (P3) | Confirmed | Fixed in 2e1570453 |
| `ci/claims/README.md` tally | Neon (P2) | Follows from the A5-500 status | No change: with A5-500 `partial` the tally of Rocq rows stands |

Survived every seat: each bridge functor takes the module arguments of its source functor; the arc-matrix bridge is the substituted proposition with `h(d)` regular; no source that a retained record cites changed bytes; the warning rows are sorted and each name is listed in `ci/rocq-warnings/causes.tsv`. The fix adds one warning row, `using-fallback-loc` for `CdTowerCanonicalKernelsBridge.v`, which its `Add Ring` prints.

## Advisor

The Advisor agreed with every resolution above, the `partial` reading of A5-500 and the header-only correction of the ideal bridge included, and asked that the pull-request body state the final statuses, name the three theorems of the kernel bridge and the five warning rows, and report the local `ci/check_rocq.sh` run as not completed. The first commit subject of the branch is 82 columns; it was pushed before the length check and stays.
