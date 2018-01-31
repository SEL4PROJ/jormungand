(*  Title:      HOL/TPTP/ATP_Problem_Import.thy
    Author:     Jasmin Blanchette, TU Muenchen
*)

section \<open>ATP Problem Importer\<close>

theory ATP_Problem_Import
imports Complex_Main TPTP_Interpret "~~/src/HOL/Library/Refute"
begin

ML_file "sledgehammer_tactics.ML"

ML \<open>Proofterm.proofs := 0\<close>

declare [[show_consts]] (* for Refute *)
declare [[smt_oracle]]

declare [[unify_search_bound = 60]]
declare [[unify_trace_bound = 60]]

ML_file "atp_problem_import.ML"

(*
ML {* ATP_Problem_Import.isabelle_tptp_file @{theory} 50 "$TPTP/Problems/PUZ/PUZ107^5.p" *}
*)

end
