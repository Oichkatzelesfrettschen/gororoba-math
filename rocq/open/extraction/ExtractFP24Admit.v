(* Verified Gallina -> C extraction of the r300 typed-carry admission gate.

   CertiRocq (rocq-certirocq 0.9.1+9.1) compiles sint_range_admit -- the signed
   production predicate faithful to r300_nir_ssa_cut.c lines 433-439: a carry
   interval [lo, hi] is admitted iff -131072 <= lo and hi <= 131072 (inclusive).
   sint_range_admit_exact (FP24Representable.v) proves every value an admitted
   interval carries is FP24-exact.  The uint form (uint_range_admit) and the
   inclusive value gate (fp24_value_admit) sit alongside it; the strict B <= 127
   IDCT-operand policy is a separate function and is not this gate.

   The emitted C is correct relative to a trusted base, not to a proved
   pipeline. CertiRocq 0.9.1+9.1 verifies large parts of its compiler and not
   others (its README), holds no correctness theorem for its C back ends, and
   both back ends admit the validity obligation of to_float. The base also
   holds the CertiRocq runtime, the C compiler with its flags, and the
   runtime objects of the switch.
   R300_MP_FP24_EXACT_INT = 131072 = 2^17 in r300_numeric_domain.c.  ASCII only. *)
From CertiRocq.Plugin Require Import CertiRocq.
From OpenGororoba Require Import FP24Representable.

CertiRocq Compile sint_range_admit.
