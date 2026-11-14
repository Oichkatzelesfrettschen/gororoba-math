/- SPDX-License-Identifier: Apache-2.0 -/
module

/-!
# Known-bad input of the axiom audit

Declarations the audit must reject, one per route by which an unproved
statement enters a library: `sorry`, a declared axiom, `native_decide`, and
a `private` theorem closed by `sorry` that no other declaration uses, which
shows that the audit's plain `import` of a `module` file reaches private
declarations (measured under Lean 4.35.0). `ci/check.sh` builds this module
and requires `#audit_axioms AuditFixture` to fail naming all four. No
library module imports this file.
-/

@[expose] public section

namespace AuditFixture

set_option warn.sorry false in
theorem usesSorry : (2 : Nat) + 2 = 4 := sorry

axiom declaredAxiom : (1 : Nat) = 1

theorem usesDeclaredAxiom : (1 : Nat) = 1 := declaredAxiom

theorem usesNativeDecide : (10 : Nat) < 11 := by native_decide

set_option warn.sorry false in
private theorem privateSorry : (3 : Nat) + 3 = 6 := sorry

end AuditFixture
