# Review record: real A_5 Stiefel zero divisors and the Rocq bridge (pull request 147)

Branch lean/stiefel-real-bridge. Heads: 45810001c under local review, 38bd46531 after the fixes.

## Reviewers (owner's selection, 2026-11-27)
- agy gemini-4-neon-medium, red team; the Advisor last.

## Findings and resolutions
| Finding | Class | Resolution |
|---|---|---|
| The bridge comment of StiefelA5RealBridge.v uses Unicode R in a Rocq file | read from source (AGENTS.md text rule for Rocq trees) | Fixed in 38bd46531 |
| The comment calls the Rocq statement narrower while saying the parametrizations agree; ry5 reaches every pure pair, so it is an equivalent reparametrization; "if j = 0" against the source's Nat.eqb | read from source | Fixed in 38bd46531 |
| TrivStarComplex: identity star on C is a valid StarRing, and the def blocks Mathlib's conjugation instance; reC and imC unfold to Complex.re and Complex.im | read from source | Note |
| The descent is complete: xr = 0 forces xi != 0 through x = map xr + I • map xi | read from source | Note |
| stiefel_zero_divisor_real drops the hypothesis mk p q != 0 (trivial at p = q = 0), slightly stronger than the ledger wording | read from source | Note |
| Partners by role, not by name: Lean Tower.map along the real-to-complex map with reC and imC per coordinate plays Rocq emb, re and im of StiefelA5Real.v, and the products on both sides of mul_emb are each prover's own tower product; TrivStarComplex and repr_map have no Rocq counterpart (the first name grep missed the role partners) | read from source (parent, after the comparison worker) | Boundary: ci/compare_complexification.sh (a5d1ac38d) compares the role partners on a Gaussian-integer wrapper with identity star; its mutants change re, im and emb, so a wrong product is caught only as a Lean-Rocq disagreement, not by a planted mutant |
| ci/compare_complexification.sh: 24 cases at levels 4 and 5, 4096 values agree over the integers and the Gaussian integers; the Rocq reference with re and im exchanged and with coordinate 3 of emb negated are rejected | measured (one workstation run, 8G scope, 4 min 16 s) | Recorded |
| Conjecture: the descent uses only 2 != 0, so base change to AdjoinRoot (X^2 + 1) gives the zero-divisor theorem over every field of characteristic other than 2, without i | hypothesis | Open item; falsifier: a field of characteristic other than 2 with a Stiefel pair whose mulLeft is invertible |

## Validation
- Lean (workstation, 4.35.0): lake build --wfail exit 0; axioms propext, Classical.choice, Quot.sound; replay exit 0. Rocq 9.3: StiefelA5RealBridge.vo builds; ci/check_claims_ledger.py: 1,327 rows match.

## After the local reviewer
Read by the parent, line by line, after the agy round on 3257d72b1:
- a5d1ac38d: ci/compare_complexification.sh and .py and the AGENTS.md registration (owner-approved); the Lean side evaluates the library Tower.map and tower product through a GI wrapper, the Rocq side the definitions of StiefelA5Real.v by vm_compute over placeholder reals.
- 8c75d0b50: this record.
- bc7e5550f: merge of main (PRs 145 and 146); no conflict.
- 725057c2d and its successor: the lean gate time after the replay driver (owner chose an update after a main run; folded into this pull request) and the registration wording.

## Advisor
- Asked for: checks on the merged head, a read of the compare scripts, a restated partner row, this coverage list, the gate time worded as one run, and kernel evidence by dispatch or a not-run mark. All applied; the rocq times of the gate table (67 min) differ from the runs of 2026-11-27 (1 h 42 min on aab280686, 34 min on d9816eb07) and stay as they are, since only the lean figure was approved; reported to the owner.
