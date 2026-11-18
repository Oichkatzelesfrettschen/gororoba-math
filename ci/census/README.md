# Header verdicts of the census-listed theorems

`header-verdicts.tsv` holds one row per theorem that `ci/theorem_census.py` lists
(a statement that names no constant of `OpenGororoba` or `OpenGororobaVerified`),
read against the header and docstring of its file. With Rocq 9.3.0 the census
lists 106 theorems in 33 files on the tree at commit abff5ec, and 115 in 36
files on the tree that holds the successor modules: the nine added rows are
helper lemmas of C1138_WickDampingMaximum, C1141_ZDGraphCountingIdentities and
C1142_XORScatterGatherSums, and the other successors list none. The three
sources of issue 44 items 2 to 4 raise the listing to 125 theorems in 38 files:
ten more helper lemmas, three of C010_ZDGraphComponents and seven of
C1463_CliffordMatrixBasis, while C1636_ScheduleProgramCount lists none.

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

The 14 files that carry a `header overclaims` row keep their bytes, since
retained records cite them by sha256. The `addressed_by` column of
`header-verdicts.tsv` is the one home of the mapping from an original file to
its successor, and a reader finds the successor of a file with

    awk -F'\t' -v f=PATH 'index($1, f) == 1 {print $5}' ci/census/header-verdicts.tsv

where `PATH` is the file's path from the repository root. A successor proves
part of the claimed structure and scopes the rest; its header states which part.

## File-local candidates

`python3 -I ci/theorem_census.py --objects DIR --file-local` also lists a theorem
whose statement names only definitions of its own file (the default listing
leaves these out, since a local definition is a project constant). Measured with
Rocq 9.3.0 on the tree that holds the three sources of issue 44 items 2 to 4
(178 verified sources, 956 declarations): the default mode lists 125 theorems,
and the file-local mode lists those 125 plus 233 more, in 33 files. 126 of the
233 sit in the 14 successor modules and 107 in 19 other files. With more than
80 new rows, the rows carry no verdict yet:
`file-local-candidates.tsv` holds them with an empty `verdict` column, and
`local_names` gives the file-local definitions each statement names. The file
is the output of the census with `--file-local --candidates
ci/census/file-local-candidates.tsv`: the file-local rows that have no row in
`header-verdicts.tsv`, so a run after a verdict lands drops that row. A verdict
reads the file header and the statement under the criterion above, and its row
then moves to `header-verdicts.tsv`.

The mode calibrates itself before it reports. Known good: `at_attractor_vanishes`
of `C_OverImbalancedSign` and `pg32_length_labels` of `C881_GF2CubicMinDegree`
list as file-local with exactly the named definition. Known bad:
`C028_lo_subalgebra_closed`, whose statement names a local definition and a
`theories/` constant, stays out. Six printed types check the name rule alone
(another file, a stem that extends this one, a local name beside a `theories/`
name, a nested module, no project name). A calibration that reads a changed
expectation exits 1 (three mutated copies each exited 1).
