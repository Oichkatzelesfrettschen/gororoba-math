(* Verified Gallina -> C extraction of the R2VB DP4 transform kernel.

   CertiRocq (rocq-certirocq 0.9.1+9.1) compiles dp4 -- the 4-term integer dot
   product that is one lane of the producer's four-DP4 matrix apply -- and
   dp4_operand_admit, the operand-magnitude gate 0 <= B /\ 4 B^2 <= 131072.
   dp4_operand_admit_exact and mvp4_rows_exact (R2VBTransformDP4.v) prove that
   every lane of an admitted transform is FP24-exact in FLX(17); the tight
   admission boundary is B = 181 (dp4_admit_boundary).

   The emitted C is correct relative to a trusted base, not to a proved
   pipeline. CertiRocq 0.9.1+9.1 verifies large parts of its compiler and not
   others (its README), holds no correctness theorem for its C back ends, and
   both back ends admit the validity obligation of to_float. The base also
   holds the CertiRocq runtime, the generated glue, the C compiler with its
   flags, and the runtime objects of the switch; make extract-r2vb-check
   compares the emitted sources and headers, the glue and the runtime sources
   with extraction/golden/, and records the switch packages, the runtime
   object and the compiler. ASCII only. *)
From CertiRocq.Plugin Require Import CertiRocq.
From OpenGororoba Require Import R2VBTransformDP4.

CertiRocq Compile dp4.
CertiRocq Compile dp4_operand_admit.

CertiRocq Generate Glue -file "r2vb_dp4_glue" [ Corelib.Numbers.BinNums.Z, Corelib.Numbers.BinNums.positive, bool ].
