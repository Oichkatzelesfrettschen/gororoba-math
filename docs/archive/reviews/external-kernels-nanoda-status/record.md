# Review record: gororoba-math PR 107 (ci/check_external_kernels.sh, nanoda status classes)

Owner's selection (2026-11-24): no local reviewer; red-teamer opencode on opencode-go/glm-5.3; the Advisor last; then the
hosted Codex round. The first opencode attempt ended with "provider.no-route: Model unavailable" before a report; the
second returned one (`attempts.tsv` of each run, kept outside the repository).

## Red-team findings and dispositions (round 1, head 430b03409)

| # | Finding | Disposition |
|---|---|---|
| 1 | A nanoda panic in src/tc.rs whose message misses the five excluded phrases (an allocation failure, an unwrap on None) reads as a rejection, so the denylist cannot make "a failure that is not a verdict reads as error" hold | Fixed in 312a63727: the 101 arm now rejects only on a type-checker verdict message (failed definitional-equality assertion, a term that is not a sort or a function type, a non-positive occurrence, an oversized constructor argument; each string occurs in the bundled binary, measured with `strings`), and reads any failure marker or unlisted panic as error |
| 2 | The first-panic pairing reads the line after the location, which eight concurrent threads can interleave, and `getline` at end of file repeats the location line | Fixed in 312a63727: the arm matches whole message lines anywhere in the log, with no pairing |
| 3 | The status-1 reject arm has no live calibration: the AuditFixture export never reaches nanoda | Fixed in 312a63727: calibration runs nanoda on that export under the strict rule and requires reject (measured: status 1, "export file declares unpermitted axiom \"AuditFixture.declaredAxiom\"") |
| 4 | The missing-declaration carve-out has no live calibration | Fixed in 312a63727: the same export under the relaxed rule must read as error (measured: status 101, "declaration not found in infer_const, AuditFixture.declaredAxiom" at src/tc.rs) |
| 5 | Claims 1, 3, 5, 6 hold; `for case in` uses a keyword as a loop variable | Renamed to `fixture` in 312a63727 |
| 6 | The note says issue #103 gave nanoda_bin three classes; the binary gains nothing | Fixed in 312a63727: "until the script read nanoda_bin statuses in the same three classes (issue #103)" |
| - | One-line panic format of older Rust releases | Covered: the whole-log match reads it (case `oneline` below) |

## Validation at 312a63727

- `nanoda_verdict` on 14 cases (the Windows workstation's WSL, 2026-11-24): retained logs of the bad-fixture closure (101, reject), the
  unpermitted axiom (1, reject), the relaxed-rule missing axiom (101, error), a missing export (1, error), a truncated
  export (101 from src/parser.rs, error), a non-JSON configuration (101 from src/util.rs, error), an empty log at 0
  (accept), 137 and 2 (error); synthetic logs of an allocation failure and an unwrap panic in src/tc.rs (error),
  interleaved verdict panics (reject), a location line without its message (error), the one-line format (reject).
  14 of 14 as expected.
- `sh ci/check_external_kernels.sh` on the same workstation: calibration passed with the new cases;
  "all 110 headline theorems accepted by con-leche, con-ron and nanoda" (34 modules), exit 0, 439.3 s.

## Advisor (last)

Confirmed on reading that no nonzero status reaches accept, that the 101 arm matches whole lines without positional
pairing, and that the four red-team dispositions match the source. Required: no host name in the record or the
pull-request body (fixed: the first record commit named the workstation's host; the name stays in that commit of
this pull request's history), and one reading of the lean workflow on the final head before the hosted review.
