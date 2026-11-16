# Review record: CertiRocq trusted base and extraction digests

Pull request 52. The owner chose `codex` on gpt-daybreak-blue and an `agy` red-team for pull requests 50 to 53. `agy` ran on Gemini 4 Hydrogen at `high` and on Gemini 3.8 Flash at `high`, both on one red-team brief covering pull requests 50 to 54. The Advisor reviewed last.

Every reviewer read head 10b09d6. The fixes landed afterwards, as new commits.

Advisor column: "confirmed" means the Advisor read the finding, the reconciliation and the resolution as stated in this row and upheld it. "requested" means the Advisor required the change named in the row, which landed after its verdict; the hosted review reads it.

| # | Finding | Reviewer, severity | Resolution | Advisor |
|---|---|---|---|---|
| 1 | Stale outputs or objects can satisfy the digest check | codex P2, Hydrogen P1 | Fixed in d0b262f, which removes expected outputs before emission and compiles the R2VB theories under the running switch. Then 87a3e75 gives extract-c the same theory compile. | d0b262f confirmed; 87a3e75 requested |
| 2 | A failing `gcc --version` is masked by the pipe | codex P2 | Fixed in d0b262f: the version is captured before it is trimmed. Measured in sh: with gcc missing, the group fails. | confirmed; the negative test requested |
| 3 | The headers still say "Verified" and leave the decisive gaps unnamed | codex P2, Hydrogen P2, Flash P2 | Fixed in d0b262f. Read in the installed package source: Admitted lemmas in LambdaBoxMut, LambdaBoxLocal, LambdaANF, HashMap and the Codegen correctness file; printer axioms in `Compiler/pipeline.v`; the plugin built through `theories/Extraction/extraction.v` with Extract Inductive directives; and `plugin/Loader.v`. | confirmed; the source reading requested |
| 4 | The warning exceptions are broader than measured and cover hand-written code | codex P2 | Fixed in d0b262f; each set was measured with gcc 15.2. Hand-written code is clean under `-Wall -Wextra -Werror`; emitted units need `-Wno-int-conversion` only; the glue also needs `-Wno-format` and `-Wno-format-security`; gc_stack.c is clean under `-Werror`. | confirmed |
| 5 | A prebuilt `gc_stack.o` is linked unchecked | Hydrogen P1, Flash P2 | Fixed in d0b262f: gc_stack.c is compiled from the source that the runtime golden file pins. | confirmed |
| 6 | The FP24 check pins no digest | Hydrogen P1, Flash P1 | Fixed in 34cc390: `golden/fp24_admit_extraction.sha256`, equal across two emissions. A changed golden digest exits 2. | confirmed |
