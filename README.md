This repository contains the supporting Isabelle/HOL theories
for the paper "Walking Backwards and Forwards with Separation Logic".

Hoare_Sep_Tactics/ contains the main relevant theory files, they are

 * Det_Monad, the formalisation of a deterministic state monad with failure (Section 2)
 * Hoare_Sep_Tactics, the currently in-use weakest-precondition separation logic method (Section 5)
 * Extended_Separation_Algebra, which contains theories about septraction, separating coimplication and theorems relating the two (Section 4),
 * Simple_Separation_Example, which contains the examples of weakest preconditions and strongest postconditions from the paper (Sections 5 and 6), and
 * Unified_Correctness, which contains the Unified Correctness material (Section 7).

The theories compile with Isabelle2016-1:

    isabelle build -v -D .
