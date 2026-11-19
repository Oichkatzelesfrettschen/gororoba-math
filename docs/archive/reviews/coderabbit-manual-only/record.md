# Review: CodeRabbit manual-only configuration

Pull request 85 of gororoba-math. Reviewers: the `codex` command-line agent (gpt-daybreak-blue, high effort, read-only) and the Advisor.

| Finding (codex, e1ce42f) | Check | Resolution |
|---|---|---|
| P3: the PR body states more than the file proves (that the defaults posted a status, and that CodeRabbit "runs only" on request) | Partly confirmed. The status is observed: pull request 84's checks list a skipped CodeRabbit entry. The "runs only" wording outran the file. | The body now says that with automatic review off, a review starts only from an explicit request. |
| Claim 1: the keys are CodeRabbit v2 schema names | Justified. The file is byte-equal to gororoba-quantum's configuration apart from its comment. | - |

## Advisor

Not called separately. The change mirrors gororoba-quantum's reviewed configuration file.
