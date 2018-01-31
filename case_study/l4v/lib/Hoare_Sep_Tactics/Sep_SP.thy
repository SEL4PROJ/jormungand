theory Sep_SP
 imports
 Sep_Forward
 SP
begin

named_theorems sep_sp

ML {* 
fun attrib thm ctxt thm' =
    ( [thm'] MRS thm)
    |> Goal.norm_result ctxt
  handle THM _ => thm'

fun try_then xs = Thm.rule_attribute [] (attrib xs o Context.proof_of )

*}

attribute_setup TRY_THEN = {* Attrib.thm >>  try_then *}

method sep_sp uses rl spec declares sep_sp  = (sp sp: spec[TRY_THEN sep_sp] rl )

lemma "(\<not>(P \<and>* (\<lambda>s. \<not> Q s)) s) = ((P \<leadsto>* Q) s)"
              "(\<not>((\<lambda>s. \<not> Q s) \<and>* P) s) = ((P \<leadsto>* Q) s)"                                                            
 apply (clarsimp simp: sep_coimpl_def pred_neg_def)
 by (clarsimp simp: sep_coimpl_def pred_neg_def sep_conj_commute)


lemma sep_conj_coimpl_precise: "(P \<and>* R) s \<Longrightarrow> precise P \<Longrightarrow> (P \<leadsto>* R) s" 
  by (simp add: precise_conj_coimpl)


  

end