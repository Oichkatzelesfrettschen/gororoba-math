# Brief: red team of gororoba-math PR 153 (lean: doubling unit anticommutes with doubly pure elements)

Read first: WORKSPACE/AGENTS.md, then WORKTREE/AGENTS.md. Work read-only: change no file (print your report as your answer); never commit, push or stash; spawn no subagents. Lean builds do not run on this machine: if you build, run over the compute workstation in WORKTREE/lean (commit b947d1e36, clean tree; `git log -1` confirms) with `export PATH=$HOME/.elan/bin:$PATH`, e.g. `lake build --wfail GororobaMath.CayleyDickson.DoublingUnit`, each command under 15 minutes, scratch files only under SCRATCH.

Material: `git -C WORKTREE diff origin/main...HEAD`: lean/GororobaMath/CayleyDickson/DoublingUnit.lean and its import in lean/GororobaMath.lean. Product convention: lean/GororobaMath/CayleyDickson/Basic.lean. Prior art: math_0511691.pdf (Proposition 5.3, Lemmas 5.7, 6.4).

## Claims under review (each a claim; justify or falsify it)

1. h (h z) = -z for h = (0, 1) and every z, over every NonAssocRing with StarRing. Status: proved (Lean). Falsifier: a hypothesis the statement hides, or a convention mismatch with Basic.lean.
2. For doubly pure x = (a, b) (star a = -a, star b = -b), h (x z) + x (h z) = 0. Status: proved. Falsifier: the statement says less than the docstring (for example "every level" when it needs more), or the docstring's half formulas are wrong.
3. The docstring's attribution to BDI Proposition 5.3 and Lemma 6.4 is accurate, and the module follows the repository rules (module docstring with convention, namespace, SPDX line, import added, no sorry, scope at the generality of the proof).

## Questions

- Which claims fall, by what evidence; is the statement at its natural generality (could the hypotheses be weaker, for example only star a + a = 0 central)?
- What should follow: the parity step for ker L_p n ker L_q at every level, with its cheapest Lean route.

Report ranked by consequence, every claim tied to a file:line, a command with its output, or a theorem name. Print it as your answer, under 120 lines.
