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
| No Rocq partner holds TrivStarComplex, repr_map, reC or imC (grep of StiefelA5Real.v and StiefelA5ZeroDivisor.v) | read from source (parent) | Boundary: those four stay Lean-only; the definitions both provers hold (the embedding, re, im and the mul_emb step) are compared by ci/compare_complexification.sh, added in a5d1ac38d |
| ci/compare_complexification.sh: 24 cases at levels 4 and 5, 4096 values agree over the integers and the Gaussian integers; the Rocq reference with re and im exchanged and with coordinate 3 of emb negated are rejected | measured (one workstation run, 8G scope, 4 min 16 s) | Recorded |
| Conjecture: the descent uses only 2 != 0, so base change to AdjoinRoot (X^2 + 1) gives the zero-divisor theorem over every field of characteristic other than 2, without i | hypothesis | Open item; falsifier: a field of characteristic other than 2 with a Stiefel pair whose mulLeft is invertible |

## Validation
- Lean (workstation, 4.35.0): lake build --wfail exit 0; axioms propext, Classical.choice, Quot.sound; replay exit 0. Rocq 9.3: StiefelA5RealBridge.vo builds; ci/check_claims_ledger.py: 1,327 rows match.
