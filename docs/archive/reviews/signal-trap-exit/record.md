# Review record: signal traps that exit with the signal status

Pull request 69, issue 66. The owner chose `codex` on gpt-daybreak-blue and no red-team. The Advisor reviewed last.

Advisor column: "confirmed" means the Advisor read the finding, its reconciliation and the resolution as stated; "refuted" means the Advisor agreed the finding does not hold, for the reason given; "requested" means the Advisor required the change named in the row, which landed after its verdict and reaches the hosted review.

Codex round 1 read 98964a5; round 2 read be65c8f.

| # | Round | Finding | Severity | Resolution | Advisor |
|---|---|---|---|---|---|
| 1 | 1 | Scratch `check.sh` reaches `ci/check_signal_traps.sh` before its `shellcheck` trigger, so the harness fails | P1 | Refuted by measurement: the shellcheck loop of `check.sh` precedes the helper call, and the harness reported 10 runs (5 subjects, 2 signals) at 98964a5 and at every later head. | refuted |
| 2 | 1 | The lexical rule misses multiline traps, signal numbers and `SIG` names, and reports correct noncanonical spellings | P2 | Fixed in 73de91b and f1539de: every trap command outside three one-line forms is reported, fail closed. | confirmed |
| 3 | Advisor | The `check.sh` mutant exits 0 rather than running on, so "each mutant runs on" is false for it; the rule misses `then`, `do`, `else` and `!`; the `env` claim for the hosted runner is unmeasured; the step-1 comment and AGENTS.md are stale | - | Fixed in be65c8f: the summary reads "each mutant fails the test" and the header states what each mutant does; the header names the measured uutils `env`; `check.sh` and AGENTS.md describe the three forms. | requested |
| 4 | 2 | Two rejected samples run `rm -r` without `</dev/null`, so the removal rule of `check.sh` fails the hosted gate at be65c8f | P1 | Fixed in 0424dbc: the samples use `unlink`. | confirmed |
| 5 | 2 | The rule misses case arms, assignment and `command` prefixes, and quoted or escaped command names | P2 | Fixed in 0424dbc and d0222c1: the rule reads the word `trap` on every non-comment line, not command positions; a command name built by quoting or expansion is stated outside it. | confirmed |
| 6 | 2 | Coverage reads only `*.sh` paths | P2 | Fixed in 0424dbc: tracked files whose first line is a shell `#!` line are read too (none exists today; the count stays 18). | confirmed |
| 7 | 2 | "The first command after its traps" is inaccurate for `check.sh`; only the four comparison mutants equal `origin/main` | P3 | Fixed in 0424dbc and the body: "the first stubbed tool it reaches after its traps are set"; the body names the `check.sh` mutant synthetic. | confirmed |

Codex justified claim 1 in both rounds: the four script diffs change only the signal bindings, and the EXIT cleanup and ordinary control flow are unchanged.
