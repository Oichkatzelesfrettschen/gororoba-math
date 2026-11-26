# Review record: unit-norm octonions as a Moufang loop in Lean and Agda

Pull request 137, branch `agda/pilot-moufang-loop`. Reviewers: `agy` (gemini-4-neon-low, red team) and
`codex` (gpt-daybreak-blue, read-only) on head `9ffb68bcc` (the Agda pilot and the comparison) and on the
delta `9ffb68bcc..4fe2a9be2` (the Lean port and the first round's fixes); the hosted Codex round and the
Advisor follow on the final head.

## Round 1 (head 9ffb68bcc)

| Finding | Source | Disposition |
|---|---|---|
| The comment "the basis triple does not associate" outruns `not-associative`, which proves associativity implies `1# + 1# ≈ 0#` | codex (blocking), agy (nit) | Fixed in a03640645: comments state the coordinate-7 associator and the condition on `1# + 1#`; the theorem stays as stated, true in every characteristic |
| The associator comment and README assert `(e₁ e₂) e₄ = e₇` and `e₁ (e₂ e₄) = - e₇`; the theorem states coordinate 7 only | codex, agy | Fixed in a03640645 |
| "Exactly the solutions" where the corollaries prove uniqueness | codex, agy | Fixed in a03640645: "every solution equals"; existence is `leftDivides` and `rightDivides` |
| The planted associativity copy passes on any failure at its line | codex, agy | Fixed in a03640645: the log must hold `[UnequalTerms]`, the empty type and `Zero (norm` at the line; a copy with an unknown identifier on the planted line is now rejected (measured), and the earlier line test accepted it |
| The postulate copy matches any log with `safe` | codex, agy (nit) | Fixed in a03640645: `[SafeFlagPostulate]` at the appended line |
| Toolchain pins not enforced | codex | Fixed in a03640645 for agda-stdlib (a git checkout at the v2.4 commit with unmodified tracked files); Boundary for the Agda executable: the script constrains the version string, and the README records the digest of the unpacked Linux executable (7539cc7c7) |
| "All three can work axiom-free" contradicts the Lean axiom list | codex | Fixed in 4fe2a9be2 |
| The issue count of the `false` label lacks a query and overreaches as a trust measure | codex, agy | Fixed in 4fe2a9be2 and 7539cc7c7: the query and its date are recorded, the responses are not retained, and the text calls the count bug history |
| Peregrine's trusted base is stated beyond its documents' disagreement | codex | Fixed in 4fe2a9be2: admitted preconditions, unverified printers and the open `trust_coq_kernel` question named |
| Coq-HoTT and peregrine-tool cited at moving branches | codex, agy | Fixed in 4fe2a9be2: commits `44729ef6920c` and `386251fedf5f`; the four Coq-HoTT paths exist at that commit (read through the GitHub contents API) |
| `AGENTS.md` omits `agda/` | codex, agy | Fixed in 4fe2a9be2 with the owner's approved text; the workspace guide sentence is gororoba-infrastructure pull request 68 |
| British spellings in prose | codex, agy | Fixed in a03640645 and 4fe2a9be2; `TCOptimised` is an agda-stdlib module name and keeps its spelling |
| Timings disagree between the README and the comparison | agy | Fixed in a03640645: three runs, 309.6 s to 323.3 s |
| Extraction timings without retained logs | agy | Fixed in 4fe2a9be2: marked as unretained single runs |

## Round 2 (delta to 4fe2a9be2)

| Finding | Source | Disposition |
|---|---|---|
| Lean fields, variable order of `identical`, instance hypotheses, `not_mul_assoc` generality, proof hygiene, ledger paths | agy, codex | Verified by both, no defect |
| The C-578 note says "associativity fails" over every commutative ring | codex | Fixed in 7539cc7c7: "when 2 ≠ 0" (`exists_mul_assoc_ne_iff` and `not_mul_assoc` both need it) |
| The Agda executable is version-constrained, not pinned | codex | Boundary: the README states the constraint and the measured digest (7539cc7c7) |
| Issue counts without a retained response | codex (nit) | Fixed in 7539cc7c7: stated as not retained |

## Hosted Codex round (head a4574f289)

| Finding | Disposition |
|---|---|
| P1: the C-578 proof column names the structure `CayleyDickson.IsMoufangLoop`, which `ci/check_claims_ledger.py` rejects as a proof entry (the hosted `quick` and `build` checks failed on it) | Fixed in 041116e06; `quick`, `build`, `rocq-changed` and `main-gate` pass on that head |
| P2: a relative `AGDA` path resolves inside the temporary copy | Fixed in 041116e06: a path with a slash resolves against the caller directory first; `AGDA=tools/agda` (relative link) runs the check to exit 0 (measured) |

## Measurements on the reviewed heads

- Lean, module `GororobaMath.CayleyDickson.OctonionMoufangLoop` at 4fe2a9be2: `lake build --wfail` exit 0; the eight new theorems depend on `propext`, `Classical.choice`, `Quot.sound` only; `leanchecker` replay exit 0 (Lean 4.35.0, Mathlib v4.35.0).
- Agda, `ci/check_agda.sh` on an export of 4fe2a9be2: exit 0, 326.6 s, 0.69 GB; on 9ffb68bcc: exit 0, 323.3 s, 0.68 GB.
