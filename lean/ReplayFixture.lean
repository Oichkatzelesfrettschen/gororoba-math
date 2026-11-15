/- SPDX-License-Identifier: Apache-2.0 -/
import Lean

/-!
# Known-bad input of the kernel replay

A command adds the theorem `ReplayFixture.bogus` of type `False` with the
value `True.intro`, under `debug.skipKernelTC`, the option that adds a
declaration without the kernel. The module then builds with warnings as
errors, and `collectAxioms` reports no axiom for `ReplayFixture.derived`
(measured under Lean 4.35.0), so neither the build nor the axiom audit
sees it. `ci/check.sh` builds this module and requires `leanchecker`,
which type-checks the compiled declarations again in a second process, to
reject it naming `ReplayFixture.bogus`. No library module imports this
file.
-/

open Lean Elab Command

namespace ReplayFixture

/-- Adds `ReplayFixture.bogus : False := True.intro` to the environment. -/
elab "add_replay_fixture" : command => do
  let decl := Declaration.thmDecl
    { name := `ReplayFixture.bogus, levelParams := [], type := mkConst ``False,
      value := mkConst ``True.intro }
  liftCoreM <| addDecl decl

set_option debug.skipKernelTC true in
add_replay_fixture

theorem derived : False := bogus

/-- info: 'ReplayFixture.derived' does not depend on any axioms -/
#guard_msgs in #print axioms derived

end ReplayFixture
