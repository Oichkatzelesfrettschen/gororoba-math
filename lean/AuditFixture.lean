/- SPDX-License-Identifier: Apache-2.0 -/
module

/-!
# Known-bad input of the axiom audit

Three declarations the audit must reject, one per route by which an
unproved statement enters a library: `sorry`, a declared axiom, and
`native_decide`. `ci/check.sh` builds this module and requires
`#audit_axioms AuditFixture` to fail naming all three. No library module
imports this file.
-/

@[expose] public section

namespace AuditFixture

set_option warn.sorry false in
theorem usesSorry : (2 : Nat) + 2 = 4 := sorry

axiom declaredAxiom : (1 : Nat) = 1

theorem usesDeclaredAxiom : (1 : Nat) = 1 := declaredAxiom

theorem usesNativeDecide : (10 : Nat) < 11 := by native_decide

end AuditFixture
