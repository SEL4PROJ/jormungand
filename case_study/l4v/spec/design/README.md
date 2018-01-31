The Executable Design Specification of seL4
===========================================

    l4v/spec/design/

This directory contains the Isabelle sources of the executable design
specification for seL4.

Most theory files in this directory are tool-generated, do not edit!

The files here are also not particularly well suited for human consumption, it
is recommended to directly read the corresponding Haskell code in
`seL4/haskell` instead.


Top-Level Theory
----------------

The top-level theory file that draws the whole specification together is
`API_H`, the top-level function in that theory is `callKernel`.

Similarly to the abstract specification, this top-level function is later in
the proofs further wrapped in an automaton that describes system behaviour on
this level of abstraction.


Building
--------

The corresponding Isabelle session is `ExecSpec`. Build in `l4v/spec/` with

    make ExecSpec


Remarks
-------

 * for regenerating the design spec from Haskell sources, go to directory
   `l4v/tools/haskell-translator` and run

          ./make_spec.sh

 * skeleton files that define which parts of which Haskell files get mapped
   to which Isabelle theories are found in the sub directories `skel` and
   `m-skel` for `design` and `machine` respectively.

