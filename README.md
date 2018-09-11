This repository contains the supporting Isabelle/HOL theories
for the thesis "Forward with Separation Logic".


sep_algebra/ contains the theory files for the formalisation of separation algebras in Isabelle/HOL and some of the tactics for separation logic

 * Separation_Algebra, the formalisation of separation algebras in Isabelle/HOL (Chapter 4),
 * Sep_Rotate, the generic ‘rotator’ upon which most of the tactics are built (Chapter 5),
 * Sep_Select, the method for manual manipulation of separation logic formulas (Chapter 5),
 * Sep_Provers, the sep_drule, sep_rule, and sep_erule methods for separation logic (Chapter 5),
 * Sep_Cancel, the method for proof by cancellation in separation logic (Chapters 5 and 6),
 * Sep_Solve, the simple solver for separation logic formula based on sep_cancel (Chapter 5 and 6)

Hoare_Sep_Tactics/ contains the main relevant theory files for Chapters 6, 7, and 9, they are

 * Det_Monad, the formalisation of a deterministic state monad with failure (Chapter 3),
 * Hoare_Sep_Tactics, the currently in-use weakest-precondition separation logic method (Chapter 6),
 * Extended_Separation_Algebra, which contains theories about septraction, separating coimplication and theorems relating the two (Chapter 4),
 * SP, which contains the strongest-postcondition method (Chapter 7),
 * Sep_SP, which contains the strongest-postcondition separation logics (Chapter 7),
 * Sep_Forward, which contains the simplifier for septraction and separating coimplication, and
 * Simple_Separation_Example, which contains the examples of weakest preconditions and strongest postconditions from the paper (Chapters 6 and 7)
 * Failure Model, which contains the model of separation logic with failure, with some example proofs (Chapter 9). 

case_study/ contains a copy of the l4v project, of interest to the paper are
* proof/capDL-api/*, which contains a portion of the system initialisation proofs (Chapter 6)
* proof/capDL-api/KHeap_Forward_DP, which contains the use of the forward reasoning framework on
  a portion of the system initialisation proofs (Chapter 7), and
* sys-init/* which contains the remainder of the system initialisation proofs (Chapter 6)

Predicate_Transformers.thy contains the notion of predicate transformers that we use and the results in separation logic
we prove in Chapter 8. 


The theories compile with Isabelle2016-1:

    export L4V_ARCH=ARM
    isabelle build -v -D .
