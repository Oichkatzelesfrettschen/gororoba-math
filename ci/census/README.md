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
successor not yet landed.
