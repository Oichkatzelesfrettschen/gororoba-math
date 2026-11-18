# Review record: components of the zero-divisor graph and k - 1 bridges

Pull request 77, issue 44 item 2. The owner chose the `codex` command-line reviewer on gpt-daybreak-blue and the Advisor, and no hosted review round (ruling of 2026-11-18). The Advisor reviewed last.

Advisor column: "confirmed" means the Advisor read the finding, its reconciliation and the resolution as stated; "requested" means the Advisor required the change named in the row, which landed after its verdict.

Codex read abf5c51; GitHub was unreachable from its sandbox, so it read the issue text from its brief. Its brief asked for a verdict on four claims (the adjacency is tied to the product, the components are the seven box-kites, sufficiency is general and not vacuous, the VM cast and the scope are sound).

| # | Round | Finding | Severity | Resolution | Advisor |
|---|---|---|---|---|---|
| 1 | 1 | `boxkites_are_components` equates reachability with a computed label, and no theorem ties each label fiber to its list of `BoxKite.boxkites` in both directions | P2 | Confirmed. Fixed in 39e6e6d: `box_comp_iff_member` (the label of a vertex is c exactly when its assessor is in the c-th list) and `boxkites_are_components_member` (two vertices are joined by a path exactly when one list holds both). | confirmed |
| 2 | 1 | The edge list is tied to `zd_adj` only for distinct vertices; nothing excludes an assessor adjacent to itself | P3 | Confirmed. Fixed in 39e6e6d: `zd_adj_irreflexive` for all 42 vertices and `zd_edges_adj_total`, the specification with no distinctness hypothesis. The gate passed at 39e6e6d. | confirmed |
| 3 | Advisor | Degree 4 and 84 edges make each component an octahedron, while the header of `C010_ConnectivityObstruction.v` says "7 K6 cliques" | - | Recorded in the pull-request body and on issue 44; the original file keeps its bytes and `ci/census/header-verdicts.tsv` already marks its theorems as overclaiming. | requested |
| 4 | Advisor | The census of `rocq/open/verified` describes the tree before this source | - | Counted in the census update that lands with the last of the three pull requests: this source adds 3 closed rows (helper lemmas) and 18 file-local candidates. | requested |

Codex rated claims 3 and 4 justified and claims 1 and 2 unsettled on rows 1 and 2.
