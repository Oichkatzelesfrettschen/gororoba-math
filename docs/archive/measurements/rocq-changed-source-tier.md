# Rocq changed-source tier

Baseline measured 2026-11-26 from the logs of hosted runs (ubuntu-26.04, GitHub Actions; `gh run view --json jobs` step times and `gh run view --log` timestamps of the lines `check_rocq:`). Each row is one run; the number is wall-clock seconds.

## Baseline of the full gate

| Run | Event, kernel conversion | Switch | Step | Seconds |
|---|---|---|---|---|
| 45765041902 (rocq.yml) | dispatch, bytecode | restored | system packages | 18 |
| 45765041902 | | | switch restore | 14 |
| 45765041902 | | | install (no-op on a restored switch) | 0 |
| 45765041902 | | | whole gate (`ci/check_rocq.sh`) | 1418 |
| 45759205680 (rocq.yml) | dispatch, bytecode | installed | switch install from source | 1244 |
| 45759205680 | | | switch save | 8 |
| 45759205680 | | | whole gate | 1772 |
| 45589354987 (rocq.yml) | nightly, checker's own reduction | restored | whole gate | 7051 |

Phases of the gate in run 45765041902 (bytecode kernel conversion), from its log lines:

| Phase | Seconds |
|---|---|
| kernel replay evidence calibration | 87 |
| `make all` of rocq/open (382 sources) | 603 |
| check-schur-geometry, check-admissions, check-plugins, extract-check, nullity certificate | 116 |
| rocq/quantum compile with its calibrations (79 sources) | 234 |
| rocq/delegation compile (4 sources) | 46 |
| compile total | about 1086 |
| rocq/quantum kernel check (concurrent with the rocq/open kernel check) | 299 |
| rocq/delegation kernel check | 32 |

The same phases in the nightly run 45589354987 (pure conversion): rocq/open `make all` 754 s, rocq/quantum compile 287 s, rocq/quantum kernel check 5625 s, rocq/delegation compile 61 s and kernel check 66 s.

Caches before this tier: the opam switch (key from `rocq/open/opam/**` and `ci/install_rocq.sh`, saved by rocq.yml on a miss) and nothing of compiled objects; every gate run compiled all 382 + 79 + 4 listed sources.

For comparison, the `quick` workflow on a pull request (run 45764957870): job `quick` 19 s (`ci/check.sh --quick` 12 s), job `build` 220 s (toolchain and Mathlib cache 97 s, `ci/check.sh --build` 115 s), job `main-gate` 4 s.

Consequence: the floor of a Rocq check on a hosted runner is the system packages (about 18 s) plus the switch restore (about 14 s), about 32 s before any compile, so a change-driven tier of ten seconds is out of reach on a runner; the tier targets that floor plus the compile of the changed sources and their dependents.

## Design

- Decision. `ci/check_rocq_changed.sh` compares the git blob of every path of `rocq/` and of `ci/install_rocq.sh` at HEAD with the manifest saved beside the objects.
- Saved tree. After a green gate on `main` (push, nightly) or a dispatch with `save_objects`, `ci/check_rocq.sh` copies the `.vo`, `.glob` and `.aux` files of the four project directories, the manifest and the switch identity (Rocq version and the md5 of `ltac_plugin.cmxs`) into one directory and checks the copy against its list; rocq.yml saves it, after its report step and without failing the run, under `rocq-objects-<hash of the ports and installer>-<sha>`, and the quick job restores the newest entry of that prefix.
- Incremental compile. The saved objects are laid over an export of HEAD; every object is dated to the restore and every other file 2000-01-01, so that no saved clock matters (objects older than the library objects of the switch rebuild, measured locally); the objects of each changed source are deleted and the source touched; `make` compiles the changed sources and the sources that import them, with the `_RocqProject` options; each changed source's object must then be newer than a stamp taken before the build; the warning check reads the logs with `--new-only`.
- Trees. rocq/open runs when one of its project sources changed; rocq/quantum when one of its sources or rocq/open changed; rocq/delegation when one of its sources changed.
- Sources outside the project files. A group of checkpoint, test or extraction sources compiles with the flags of its `make` target when a path of its directory changed or when it names a rebuilt module (a textual match); a full compile runs every group, so that the warning check without `--new-only` sees every source the allow-list names.
- Checks of every run that the tier reads a path for: export equal to the tree (`.gitattributes`), the lists of sources outside the project files and the delegation inventory check (shared with the gate in `ci/rocq_inventory.sh`), the admission scan of the three trees, and the assumption scan of the changed sources against `kernel-assumptions.txt`.
- Fail closed to a full compile: no saved tree, an empty, unreadable or different switch identity, a deleted path, a changed `_RocqProject`, `Makefile`, `rocq/open/opam/` path or `ci/install_rocq.sh`, or a changed warning parser or list.
- Skip: none of the paths that the tier reads differs between the base and HEAD (`touched_paths` of the script lists them).
- Left to the full rocq workflow (every push to main, nightly, dispatch): the kernel check and the axiom ledgers, the evidence calibration, the mutation harnesses and kernel check of check-schur-geometry, and the sources held uncompiled; `AGENTS.md` ("Landing") gives each with its worst-case time on main.

## Measured times of the tier

Hosted runs of branch ci/rocq-changed-source-tier, 2026-11-26 (ubuntu-26.04, 4 vCPU, `jobs=4`). The saved tree of run 45769425714 (rocq.yml dispatch with `save_objects`) holds 1395 files (461 objects with their `.glob` and `.aux` files), 31.9 MB compressed, saved in 2 s; its manifest lists 552 paths. The opam switch cache is 830 MB.

```tsv
run	case	switch	objects	changed	rebuilt	compile_step_s	job_s
45770055162	pull request, no saved tree	installed 926 s	absent	all	382+79+4	786	1732
45774476190	dispatch, probe rocq/quantum/E8RootExchange.v (a leaf)	restored 14 s	restored 1 s	1	1	11	635 (603 of it one stalled apt step)
45775888688	dispatch, probe rocq/open/theories/Prelude.v (root of rocq/open)	restored	restored	1	236	490	about 650
```

Reading.
- A one-file change to a leaf source: the compile step takes 11 s (3.6 s of it the calibration, 7.6 s the compile); the job without the stalled apt step (13 to 23 s in the other runs) adds checkout 2 s, switch restore 14 s and object restore 1 s, about 45 s in all.
- The root of rocq/open rebuilds its 236 dependents in 490 s, against 603 s for the whole of `make all` in the full gate.
- Without a saved tree the job compiles every source: 786 s (jobs=4), plus 926 s to install the switch when no cache holds one.
- The pull request run reads caches of `main` only. `main` held no opam switch entry at 2026-11-26 06:37 (the entry sat on lean/pfaffian-16), and `rocq-objects` entries are saved on main only by a rocq run there, so pull requests run the fallback until the first rocq run on main after the merge.
- The skip path (no touched path) is checked locally and by the calibration case "HEAD against itself"; no hosted run of it is recorded.
- These three runs measured the first version of the tier, which ran no `rocq check`, no admission scan and no inventory check and compiled no source outside the project files; the version below adds the scans, the checks and the outside sources, and its times follow.

## Measured times with the admission, assumption and inventory checks

Run 45791312742 (quick.yml dispatch with probe rocq/quantum/E8RootExchange.v, a leaf), restored switch and objects of run 45781246662 (rocq.yml dispatch with `save_objects`: 1404 objects, 555 manifest paths, gate step about 41 min that day):

```tsv
run	case	apt_s	switch_restore_s	objects_restore_s	compile_step_s	rebuilt	job_s
45788085671	leaf probe, objects dated by separate touch calls	15	12	1	309	58	about 340
45791312742	leaf probe, objects dated to one instant	24	17	2	27	1	77
45781267449	pull request, only tier scripts changed (no tree compiled)	17	15	0	13	0	50
```

- The compile step of run 45791312742 holds the calibration (8 s), the admission scan (2 s), the assumption and inventory checks, the compile of the one changed object and the warning check: 27 s, 1 object rebuilt.
- Run 45788085671 measured a defect: dating each saved object by its own touch call put a quantum object before the open object it imports, and make rebuilt 58 objects; dating all objects from one reference file fixed it (run 45791312742).
- Two dispatched runs stalled in the apt step for more than ten minutes (one of them cancelled after 17 minutes); the step now has a timeout.
- Run 45793361765 (leaf of rocq/open that the nullity certificate imports, with the switch-off scan and the flag search): 1 open object and the schur-geometry group (38 s of the compile step) compiled; compile step 56 s, job 90 s.
- The hub probe (rocq/open/theories/Prelude.v, 236 objects, 490 s) was measured with the first version only.

## Calibration

Each run checks the decision on seven synthetic manifests, an absent baseline, HEAD against itself and an assumption scan on a synthetic source, including the skip and `--plan` paths. A run that compiles also builds a three-source fixture, saves its objects with the save routine, dates them 2099 and restores them over a fresh export three times: a changed Base.v rebuilds Dependent.v and leaves Other.v, a Base.v change that breaks Dependent.v fails, and a broken proof fails; the admission scan must reject an `Admitted` fixture.
