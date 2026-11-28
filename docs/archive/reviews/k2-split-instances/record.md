# Review record: K2 cofactor instances of E8-bar to VB under a nightly gate (pull request 150)

Branch rocq-k2-split-instances. Heads: ad85db15e under the opencode review, 1777f46d3 after its fixes and under the Advisor.

## Reviewers
- The owner's question of 2026-11-27 (which gate tier runs the modules; which local reviewers run) stayed unanswered for two hours. The session took the recommended tier (a nightly gate of its own) and the reviewer of pull request 148, opencode on a free model, and recorded both defaults in the pull request and the work ledger.
- opencode, red team: opencode/deepseek-v4.1-flash-free, 13 findings on ad85db15e.
- The Advisor last, on 1777f46d3.
- Hosted Codex after this record.

## Findings and resolutions
| Finding | Reviewer | Class | Resolution |
|---|---|---|---|
| The drift step, the one check that ties the tree to the certificate export, is skipped in the scheduled run, since the export is tracked nowhere | opencode | read from source | Boundary: the script reports the skip; the export (39.6 MB) is an untracked file of gororoba-quantum. Open item of the work ledger: give the export a tracked or published home |
| The warning reader took only a tag alone on its line with a category, so a tag at the end of a text line or without a category was invisible | opencode | read from source, probe | Fixed in 1777f46d3: warning_names reads a tag at the end of any line, calibrated on the three shapes |
| The one-digit mutant changed the name of the check lemma, so it failed at name resolution and never reached check_step_data | opencode | read from source, probe | Fixed in 1777f46d3: the mutant changes the last hexadecimal digit of the last cofactor word and must fail with "Unable to unify"; passed in the next two gate runs |
| The changed tier of the admission gate skipped the declared-assumption scan on a K2 source | opencode | read from source | Fixed in 1777f46d3: check_declared_axioms compares a changed K2 source with rocq/k2-instances/kernel-assumptions.txt. Known-bad run on the compute workstation: a planted Axiom in K2CofactorE8barVBc02.v fails sh ci/check_rocq.sh --changed with status 1 |
| The textual scan missed Admit Obligations and Context | opencode | read from source | Fixed in 1777f46d3, each with a planted line |
| --check wrote a bytecode cache beside the generator | opencode | read from source, probe | Fixed in eb23cfdc9: sys.dont_write_bytecode before the import |
| The inventory compared top-level sources only; a tracked object or nested source would ride along under -norec | opencode | hypothesis | Fixed in 1777f46d3: the file list of the directory, at any depth, equals the listed sources and three named files |
| The textual scan read a grep error as "no forbidden line" | opencode | read from source | Fixed in 1777f46d3: status 1 alone passes |
| No pull-request check compiles the directory | opencode | read from source | Boundary: the tier is the nightly gate; the script passed four times on the compute workstation, and the first hosted run follows the merge by dispatch |
| The scheduled pure-kernel run was unmeasured against the job time limit | opencode, Advisor | hypothesis | Measured: 6,041 s of processor time for the 64 pure checks against 880 s with the bytecode machine. The nightly run now uses the bytecode machine and the pure kernel runs on dispatch |
| A piece larger than the product bound would sit alone in a step above the bound | opencode | hypothesis | Refuted: --plan lists 591,802 products as the largest step |
| confine_output refused symbolic links and accepted a hard link | opencode | read from source | Fixed in eb23cfdc9: a file with a second hard link is refused |
| "No step of the admission gate reads them" overstated: the export comparison lists the paths | opencode | read from source | Fixed in 1777f46d3: the inventory comment and the README say compiles and checks |
| The full rocq gate, with its object save, had not run over the tree | Advisor | process | Run: hosted rocq workflow on 1777f46d3 with save_objects, green in 41 minutes; the quick workflow dispatched on the branch afterwards |
| The warning comparison was one-sided, so a reader that extracted nothing passed | Advisor | read from source | Fixed: the printed names must equal the two allowed names; passed in the fourth gate run |
| The pull-request body described the script before its fixes | Advisor | process | Rewritten before the hosted round |
| The tier default and the AGENTS.md description wait for the owner | Advisor | process | Open rows of the work ledger; AGENTS.md is unchanged by this pull request |

## Measurements
rocq/k2-instances/README.md holds them. The four gate runs of ci/check_k2_instances.sh on the compute workstation: a first run stopped at the first kernel check (it required an empty axiom list, and -norec lists 26 admitted Stdlib and Corelib fields), then three passes, the last on the bytes of this record's commit.
