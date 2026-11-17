# Header verdicts of the census-listed theorems

`header-verdicts.tsv` holds one row per theorem that `ci/theorem_census.py` lists
(a statement that names no constant of `OpenGororoba` or `OpenGororobaVerified`),
read against the header and docstring of its file. With Rocq 9.3.0 the census
lists 106 theorems in 33 files on the tree at commit abff5ec, and 115 in 36
files on the tree that holds the successor modules: the nine added rows are
helper lemmas of C1138_WickDampingMaximum, C1141_ZDGraphCountingIdentities and
C1142_XORScatterGatherSums, and the other successors list none.

Criterion. The verdict is `statement is the claim` when the docstring of the
declaration or the module header describes the declaration as the arithmetic or
propositional content it states (a helper lemma, a numerator form, an arithmetic
inventory, a module that says it proves arithmetic). The verdict is
`header overclaims` when the header credits the declaration with an object or
quantifier the statement does not mention (a graph, group, integral, algorithm
equivalence, every dimension), or when the statement is a tautology under a header
that claims a count or a structure. The census is a lower bound: a theorem over a
definition local to its file is not listed, and the table makes no statement about
declarations the census omits. The `addressed_by` column names the successor
module that proves the claimed structure or scopes the claim; `owed` marks a
successor not yet landed. A claim over every level of the Cayley-Dickson tower
goes to the Lean library (`AGENTS.md`, "Lean library"), so its row names the
Lean module and theorem.

## Successors of the original files

The 14 files below carry a `header overclaims` row and keep their bytes, since
retained records cite them by sha256. Each row of `header-verdicts.tsv` names the
successor in its `addressed_by` column; this table reads that column by file. A
successor lives beside its original under `rocq/open/verified`, except the one
Lean module. `C029_FermionGenerationArithmetic.v` landed in pull request 27.

| Original file | Overclaiming theorems | Successor |
|---|---|---|
| `C872_PillarCasimirFinite.v` | `C872_pillar_casimir_finite` | `C872_WorldlineQuadratureBound.v` |
| `C873_SphereInCylinderFinite.v` | `C873_sphere_casimir_finite` | `C872_WorldlineQuadratureBound.v` |
| `C882_ParityCliqueExact.v` | `C882_octahedron_edges`, `C882_spectral_gap_k222` | `C882_OctahedronGraphSpectrum.v` |
| `C016_M3TrilinearSplit.v` | `C016_vector_sector`, `C016_total_split` | `C016_FanoOrientedTriples.v` |
| `C029_FermionGenerations.v` | `C029_three_embeddings`, `C029_orbit_stabilizer` | `C029_FermionGenerationArithmetic.v` |
| `C036_TrialityClusteringBound.v` | `C036_k4_clustering`, `C036_k222_edges`, `C036_k222_triangles` | `C036_CliqueClusteringCounts.v` |
| `C956_RoutonAVT.v` | `avt_nonempty_witness` | `lean/GororobaMath/CayleyDickson/NonAssociative.lean` (`Tower.exists_mul_assoc_ne`) |
| `C1138_WickDampingFriction.v` | `maximal_damping_at_pi_half` | `C1138_WickDampingMaximum.v` |
| `C1141_ZDGraphGeneralStructure.v` | `zd_missing_edge_count`, `zd_vertex_count`, `edge_density_increases`, `missing_fraction_decreases` | `C1141_ZDGraphCountingIdentities.v` |
| `C1142_XORScatterGatherDuality.v` | `la_source_index_correct`, `scatter_gather_roundtrip`, `scatter_gather_duality` | `C1142_XORScatterGatherSums.v` |
| `C016_ParityFlips.v` | `even_odd_split`, `parity_decomposition` | `C016_FanoOrientedTriples.v` |
| `C010_ConnectivityObstruction.v` | `min_bridges_needed`, `connectivity_obstruction` | `C010_ComponentBridgeBound.v` |
| `C1463_ArithmeticInventory.v` | `minimal_ideal_dim` | `C1463_MatrixColumnIdeal.v` |
| `C1636_Cariow2013SedenionSchedule.v` | `C1636_cariow2013_multiplier_count` | `C1636_ScheduleProductCount.v` |

`C872_WorldlineQuadratureBound.v` answers both C872 and C873, and
`C016_FanoOrientedTriples.v` answers both C016 files. A successor proves part of
the claimed structure and scopes the rest; its header states which part. The 26
overclaim rows are the rows of these 14 files, and every other row of the table
reads `statement is the claim`.
