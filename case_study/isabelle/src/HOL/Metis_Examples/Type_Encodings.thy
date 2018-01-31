(*  Title:      HOL/Metis_Examples/Type_Encodings.thy
    Author:     Jasmin Blanchette, TU Muenchen

Example that exercises Metis's (and hence Sledgehammer's) type encodings.
*)

section \<open>
Example that Exercises Metis's (and Hence Sledgehammer's) Type Encodings
\<close>

theory Type_Encodings
imports Main
begin

declare [[metis_new_skolem]]

text \<open>Setup for testing Metis exhaustively\<close>

lemma fork: "P \<Longrightarrow> P \<Longrightarrow> P" by assumption

ML \<open>
val type_encs =
  ["erased",
   "poly_guards",
   "poly_guards?",
   "poly_guards??",
   "poly_guards@",
   "poly_tags",
   "poly_tags?",
   "poly_tags??",
   "poly_tags@",
   "poly_args",
   "poly_args?",
   "raw_mono_guards",
   "raw_mono_guards?",
   "raw_mono_guards??",
   "raw_mono_guards@",
   "raw_mono_tags",
   "raw_mono_tags?",
   "raw_mono_tags??",
   "raw_mono_tags@",
   "raw_mono_args",
   "raw_mono_args?",
   "mono_guards",
   "mono_guards?",
   "mono_guards??",
   "mono_tags",
   "mono_tags?",
   "mono_tags??",
   "mono_args"]

fun metis_exhaust_tac ctxt ths =
  let
    fun tac [] st = all_tac st
      | tac (type_enc :: type_encs) st =
        st (* |> tap (fn _ => tracing (@{make_string} type_enc)) *)
           |> ((if null type_encs then all_tac else resolve_tac ctxt @{thms fork} 1)
               THEN Metis_Tactic.metis_tac [type_enc]
                    ATP_Problem_Generate.combsN ctxt ths 1
               THEN COND (has_fewer_prems 2) all_tac no_tac
               THEN tac type_encs)
  in tac type_encs end
\<close>

method_setup metis_exhaust = \<open>
  Attrib.thms >>
    (fn ths => fn ctxt => SIMPLE_METHOD (metis_exhaust_tac ctxt ths))
\<close> "exhaustively run Metis with all type encodings"

text \<open>Miscellaneous tests\<close>

lemma "x = y \<Longrightarrow> y = x"
by metis_exhaust

lemma "[a] = [Suc 0] \<Longrightarrow> a = 1"
by (metis_exhaust last.simps One_nat_def)

lemma "map Suc [0] = [Suc 0]"
by (metis_exhaust list.map)

lemma "map Suc [1 + 1] = [Suc 2]"
by (metis_exhaust list.map nat_1_add_1)

lemma "map Suc [2] = [Suc (1 + 1)]"
by (metis_exhaust list.map nat_1_add_1)

definition "null xs = (xs = [])"

lemma "P (null xs) \<Longrightarrow> null xs \<Longrightarrow> xs = []"
by (metis_exhaust null_def)

lemma "(0::nat) + 0 = 0"
by (metis_exhaust add_0_left)

end
