(*:maxLineLen=78:*)

theory Preface
  imports Main Base
begin

text \<open>
  The \<^emph>\<open>Isabelle\<close> system essentially provides a generic
  infrastructure for building deductive systems (programmed in
  Standard ML), with a special focus on interactive theorem proving in
  higher-order logics.  Many years ago, even end-users would refer to
  certain ML functions (goal commands, tactics, tacticals etc.) to
  pursue their everyday theorem proving tasks.
  
  In contrast \<^emph>\<open>Isar\<close> provides an interpreted language environment
  of its own, which has been specifically tailored for the needs of
  theory and proof development.  Compared to raw ML, the Isabelle/Isar
  top-level provides a more robust and comfortable development
  platform, with proper support for theory development graphs, managed
  transactions with unlimited undo etc.

  In its pioneering times, the Isabelle/Isar version of the
  \<^emph>\<open>Proof~General\<close> user interface @{cite proofgeneral and
  "Aspinall:TACAS:2000"} has contributed to the
  success of for interactive theory and proof development in this
  advanced theorem proving environment, even though it was somewhat
  biased towards old-style proof scripts.  The more recent
  Isabelle/jEdit Prover IDE @{cite "Wenzel:2012"} emphasizes the
  document-oriented approach of Isabelle/Isar again more explicitly.

  \<^medskip>
  Apart from the technical advances over bare-bones ML
  programming, the main purpose of the Isar language is to provide a
  conceptually different view on machine-checked proofs
  @{cite "Wenzel:1999:TPHOL" and "Wenzel-PhD"}.  \<^emph>\<open>Isar\<close> stands for
  \<^emph>\<open>Intelligible semi-automated reasoning\<close>.  Drawing from both the
  traditions of informal mathematical proof texts and high-level
  programming languages, Isar offers a versatile environment for
  structured formal proof documents.  Thus properly written Isar
  proofs become accessible to a broader audience than unstructured
  tactic scripts (which typically only provide operational information
  for the machine).  Writing human-readable proof texts certainly
  requires some additional efforts by the writer to achieve a good
  presentation, both of formal and informal parts of the text.  On the
  other hand, human-readable formal texts gain some value in their own
  right, independently of the mechanic proof-checking process.

  Despite its grand design of structured proof texts, Isar is able to
  assimilate the old tactical style as an ``improper'' sub-language.
  This provides an easy upgrade path for existing tactic scripts, as
  well as some means for interactive experimentation and debugging of
  structured proofs.  Isabelle/Isar supports a broad range of proof
  styles, both readable and unreadable ones.

  \<^medskip>
  The generic Isabelle/Isar framework (see
  \chref{ch:isar-framework}) works reasonably well for any Isabelle
  object-logic that conforms to the natural deduction view of the
  Isabelle/Pure framework.  Specific language elements introduced by
  Isabelle/HOL are described in \partref{part:hol}.  Although the main
  language elements are already provided by the Isabelle/Pure
  framework, examples given in the generic parts will usually refer to
  Isabelle/HOL.

  \<^medskip>
  Isar commands may be either \<^emph>\<open>proper\<close> document
  constructors, or \<^emph>\<open>improper commands\<close>.  Some proof methods and
  attributes introduced later are classified as improper as well.
  Improper Isar language elements, which are marked by ``\<open>\<^sup>*\<close>'' in the subsequent chapters; they are often helpful
  when developing proof documents, but their use is discouraged for
  the final human-readable outcome.  Typical examples are diagnostic
  commands that print terms or theorems according to the current
  context; other commands emulate old-style tactical theorem proving.
\<close>

end
