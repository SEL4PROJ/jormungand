Abstract Spec Invariant Proof
=============================

This proof defines and proves the global invariants of seL4's
[abstract specification](../../spec/abstract/). The invariants are
phrased and proved using a [monadic Hoare logic](../../lib/wp/NonDetMonad.thy)
described in a TPHOLS '08 [paper][1].

  [1]: http://nicta.com.au/pub?id=483 "Secure Microkernels, State Monads and Scalable Refinement"

Building
--------

To build from the `l4v/` directory, run:

    ./isabelle/bin/isabelle build -d . -v -b AInvs

Important Theories
------------------

The top-level theory where the invariants are proved over the kernel is
[`Syscall_AI`](Syscall_AI.thy); the bottom-level theory where they are
defined is [`Invariants_AI`](Invariants_AI.thy).

