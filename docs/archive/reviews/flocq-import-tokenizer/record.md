# Review record: one Flocq import tokenizer for the producer and its consumer

Pull request 65. The owner chose `codex` on gpt-daybreak-blue and no red-team for this round. The Advisor reviewed last.

Advisor column: "confirmed" means the Advisor read the finding, its reconciliation and the resolution as stated; "requested" means the Advisor required the change named in the row, which landed after its verdict and reaches the hosted review.

Codex read gororoba-math 7c505c9 and gororoba-open 03452b94 together.

| # | Finding | Severity | Resolution | Advisor |
|---|---|---|---|---|
| 1 | The change migrates the evidence contract for the newly recognized commands (for example `Redirect "replay" Require Import Flocq.Core.Core`); it is not contract-preserving | P2 | Accepted and bounded. The body states the migration. No tracked source of the three repositories changes classification (152,173 commands). The corpus holds each new form as a regression row. The fail-closed guard against Flocq reached through the default load path is issue 64. | confirmed |
| 2 | The consumer's corpus pin is documentary; no gate compares the vendored bytes with gororoba-math | P2 | Fixed in gororoba-open 54732574: an ignored hosted test byte-compares the vendored corpus with the gororoba-math checkout, and a proofs.yml lane runs it. gororoba-open keeps its proof-tree pin (`ci/gororoba_math.pin`), which the retained kernel receipts bind: a trial move of it to this pull request's head failed the control-plane lane (gororoba-open 06565b55, reverted in c07df8c9). The corpus instead has its own pin, `ci/flocq_import_corpus.pin` (bbcd0ab5), and the lane fetches only the corpus file at that commit. | confirmed; the dedicated pin follows the Advisor's fallback |
| 3 | The new consumer comments cite internal repository paths | P3 | Fixed in gororoba-open 54732574. | confirmed |

Codex found no command on which the Python and Rust rules differ, and it justified the prefix list against the Rocq 9.3 grammar.
