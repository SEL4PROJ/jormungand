CapDL Separation Logic Proof
============================

This proof defines a separation logic for the [capDL](../../spec/capDL/)
kernel specification. It builds on a generic [separation
algebra](../../lib/sep_algebra/), described in the [ITP 2012
paper][Klein_KB_12].

The separation logic is defined on a lifted heap where we lift the
object heap and IRQ table into an object-component heap and an IRQ table
heap. This gives us a separation algebra with a capability-level of
granularity.

This separation logic is used by the [CapDL API Proofs](../capDL-api/)
and the [system initialiser](../../sys-init/) specification.

This separation logic is described in the [ICFEM '13 paper][Boyton_13]
and Andrew Boyton's PhD thesis.

  [Boyton_13]: http://www.nicta.com.au/pub?id=7047        "Formally Verified System Initialisation"
  [Klein_KB_12]: http://www.nicta.com.au/pub?id=5676      "Mechanised separation algebra"


Building
--------

To build from the `l4v/` directory, run:

        ./isabelle/bin/isabelle build -d . -v -b SepDSpec


Important Theories
------------------

* The definitions of heap disjunction, heap addition and showing that
  they produce a separation algebra is found in
  [`AbstractSeparation_SD`](AbstractSeparation_SD.thy).

* The "arrows" are defined in  [`Separation_SD`](Separation_SD.thy).

* The "frame rule" for specific leaf functions is defined in
  [`Frame_SD`](Frame_SD.thy). This "frame rule" is different from the
  traditional frame rule as we use a shallow embedding.

