(*  Title:      HOL/Proofs/ex/Proof_Terms.thy
    Author:     Makarius

Basic examples involving proof terms.
*)

theory Proof_Terms
imports Main
begin

text \<open>
  Detailed proof information of a theorem may be retrieved as follows:
\<close>

lemma ex: "A \<and> B \<longrightarrow> B \<and> A"
proof
  assume "A \<and> B"
  then obtain B and A ..
  then show "B \<and> A" ..
qed

ML_val \<open>
  (*proof body with digest*)
  val body = Proofterm.strip_thm (Thm.proof_body_of @{thm ex});

  (*proof term only*)
  val prf = Proofterm.proof_of body;
  Pretty.writeln (Proof_Syntax.pretty_proof @{context} prf);

  (*all theorems used in the graph of nested proofs*)
  val all_thms =
    Proofterm.fold_body_thms
      (fn (name, _, _) => insert (op =) name) [body] [];
\<close>

text \<open>
  The result refers to various basic facts of Isabelle/HOL: @{thm [source]
  HOL.impI}, @{thm [source] HOL.conjE}, @{thm [source] HOL.conjI} etc. The
  combinator @{ML Proofterm.fold_body_thms} recursively explores the graph of
  the proofs of all theorems being used here.

  \<^medskip>
  Alternatively, we may produce a proof term manually, and turn it into a
  theorem as follows:
\<close>

ML_val \<open>
  val thy = @{theory};
  val ctxt = @{context};
  val prf =
    Proof_Syntax.read_proof thy true false
      "impI \<cdot> _ \<cdot> _ \<bullet> \
      \   (\<^bold>\<lambda>H: _. \
      \     conjE \<cdot> _ \<cdot> _ \<cdot> _ \<bullet> H \<bullet> \
      \       (\<^bold>\<lambda>(H: _) Ha: _. conjI \<cdot> _ \<cdot> _ \<bullet> Ha \<bullet> H))";
  val thm =
    prf
    |> Reconstruct.reconstruct_proof ctxt @{prop "A \<and> B \<longrightarrow> B \<and> A"}
    |> Proof_Checker.thm_of_proof thy
    |> Drule.export_without_context;
\<close>

end
