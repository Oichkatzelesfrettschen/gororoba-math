# Review: CodeRabbit manual-only configuration

Pull request 85 of gororoba-math. Reviewers: the `codex` command-line agent (gpt-daybreak-blue, high effort, read-only) and the Advisor.

| Finding (codex, e1ce42f) | Check | Resolution |
|---|---|---|
| P3: the PR body states more than the file proves (that the defaults posted a status, and that CodeRabbit "runs only" on request) | Partly confirmed. The status is observed once: pull request 84, after it left draft, carries a skipped CodeRabbit check run ("manual review required for this OSS repository"). Pull requests 76 to 83 showed only the two gate checks, and the "runs only" wording outran the file. | The body now says that with automatic review off, a review starts only from an explicit request. |
| Claim 1: the keys are CodeRabbit v2 schema names | Justified. The file is byte-equal to gororoba-quantum's configuration apart from its comment. | - |

## Advisor

The Advisor found that the status claim was contradicted. gororoba-quantum carries the same keys, and its pull request 955 still showed a skipped CodeRabbit check run ("automatic reviews are disabled"). The schema the file names (schema.v2.json, read 2026-11-19) places two keys under `reviews`: `review_progress` reports each review as a check run on GitHub, and `commit_status` posts a commit status when `review_progress` is off. Both default to true. The file now sets both to false. The same two keys go to gororoba-quantum's and gororoba-open's files in their own pull requests.
