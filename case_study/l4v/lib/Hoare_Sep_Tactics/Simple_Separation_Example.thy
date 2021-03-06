
theory Simple_Separation_Example
imports
  "Extended_Separation_Algebra"
  "Hoare_Sep_Tactics"
  "../Monad_WP/WhileLoopRules"
  "Sep_SP"
begin

declare [[syntax_ambiguity_warning = false]]

type_synonym heap = "((nat \<Rightarrow> nat option))"

definition maps_to:: "nat \<Rightarrow> nat \<Rightarrow> heap \<Rightarrow> bool" ("_ \<mapsto> _" [56,51] 56)
  where "x \<mapsto> y \<equiv> \<lambda>h. h = [x \<mapsto> y] "
  
notation pred_ex  (binder "\<exists>" 10)

definition maps_to_ex :: "nat \<Rightarrow> heap \<Rightarrow> bool" ("_ \<mapsto> -" [56] 56)
  where "x \<mapsto> - \<equiv> (\<lambda>s. \<exists>y. (x \<mapsto> y) s)"


lemma maps_to_maps_to_ex [elim!]:
  "(p \<mapsto> v) s \<Longrightarrow> (p \<mapsto> -) s"
  by (auto simp: maps_to_ex_def)

declare maps_to_maps_to_ex[sep_cancel]
  
  
  lemma precise_weaken_pre: "precise P \<Longrightarrow> \<lbrace>P \<leadsto>* R\<rbrace> f \<lbrace>\<lambda>_. Q \<and>* R\<rbrace>  \<Longrightarrow> \<lbrace>P \<and>* R\<rbrace> f \<lbrace>\<lambda>_. Q \<and>* R\<rbrace> "
  apply (rule hoare_weaken_pre, assumption)
by (simp add: precise_conj_coimpl)

definition "delete_ptr p = do x <- gets (\<lambda>s. s p);
                           assert (x \<noteq> None);
                           (modify (\<lambda>s x.  if x = p then None else s x )) od" 

                           
definition "get_ptr p = do x <- gets (\<lambda>s. s p);
                           assert (x \<noteq> None);
                           (return (the x)) od"

definition "set_ptr p v = do x <- gets (\<lambda>s. s p);
                           assert (x \<noteq> None);
                           (modify (\<lambda>s. s(p \<mapsto> v))) od" 

                               
definition "new_ptr  = do  ptrs <- gets dom;
                           p <- (select ptrs);
                           x <- gets (\<lambda>s. s p);   
                           assert (x = None);
                           (modify (\<lambda>s. s(p \<mapsto> 0)));
                           return p od" 
                           
lemma new_ptr_sp: "\<lbrace>R\<rbrace> new_ptr \<lbrace>\<lambda>rv. (rv \<mapsto> - \<and>* R) \<rbrace>"
  apply (clarsimp simp: new_ptr_def, wp select_wp)
  apply (simp add: Ball_def, intro allI impI)
  apply (clarsimp simp: sep_conj_def)
 done
    
lemma delete_ptr_sp: "\<lbrace>(p \<mapsto> - \<leadsto>* R)\<rbrace> delete_ptr p \<lbrace>\<lambda>_. R \<rbrace>"
  apply (clarsimp simp: delete_ptr_def, wp)
  apply (intro allI impI)
  apply (clarsimp simp: sep_conj_def sep_coimpl_def pred_neg_def)
  apply (erule_tac x="[p \<mapsto> y] :: heap" in allE)
   apply (drule mp)
  apply (clarsimp simp: maps_to_ex_def maps_to_def, fastforce)
  apply (erule_tac x=" (\<lambda>a. if a = p then None else s a)" in allE)
   apply (drule mp)
  apply (rule ext, clarsimp simp: plus_fun_def plus_option_def)
   apply (drule mp)
  apply (clarsimp simp: sep_disj_fun_def sep_disj_option_def)
  apply (assumption)
done 
    
lemma set_ptr_sp: "\<lbrace>(p \<mapsto> - \<leadsto>* R)\<rbrace> set_ptr p v  \<lbrace>\<lambda>_. (p \<mapsto> v \<and>* R) \<rbrace>"
  apply (clarsimp simp: set_ptr_def, wp)
  apply (intro allI impI)
  apply (clarsimp simp: sep_conj_def sep_coimpl_def pred_neg_def)
   apply (erule_tac x="[p \<mapsto> y] :: heap" in allE)
  apply (drule mp)
  apply (clarsimp simp: maps_to_ex_def maps_to_def, fastforce)
  apply (erule_tac x=" (\<lambda>a. if a = p then None else s a)" in allE)
  apply (drule mp)
   apply (rule ext, clarsimp simp: plus_fun_def plus_option_def)
  apply (drule mp)
   apply (clarsimp simp: sep_disj_fun_def sep_disj_option_def)
  apply (rule_tac x="[p \<mapsto> v] :: heap" in exI)
  apply (rule_tac x=" (\<lambda>a. if a = p then None else s a)" in exI)
  apply (clarsimp, intro conjI)
    apply (clarsimp simp: sep_disj_fun_def sep_disj_option_def)
   apply (rule ext, clarsimp simp: plus_fun_def plus_option_def)
  apply (clarsimp simp: maps_to_ex_def maps_to_def)
done 

lemma set_ptr_sp': "\<lbrace>(R)\<rbrace> set_ptr p v  \<lbrace>\<lambda>rv. (p \<mapsto> v \<and>* (p \<mapsto> - -* R )) \<rbrace>"
 apply (rule hoare_chain, rule set_ptr_sp)
  apply (erule (1) sep_snake_septraction, assumption)
 done
 
 lemma get_ptr_wp: "\<lbrace>EXS x. (p \<mapsto> x \<and>* (p \<mapsto> x \<longrightarrow>* R x ))\<rbrace> get_ptr p \<lbrace>R \<rbrace>"
  apply (clarsimp simp: get_ptr_def, wp)
  apply (intro allI impI)
  apply (clarsimp simp: sep_coimpl_def sep_conj_def pred_neg_def sep_impl_def maps_to_def)
  apply (clarsimp simp: sep_disj_commute sep_add_commute)
  apply (subgoal_tac "x=y")
   apply (clarsimp)
  apply (clarsimp simp: plus_fun_def plus_option_def split: option.splits)
 done
 
 
lemma get_ptr_sp_weak: "\<lbrace>(R)\<rbrace> get_ptr p \<lbrace>\<lambda>rv. R and (ALLS x. (p \<mapsto> x \<leadsto>* (\<lambda>s. rv = x))) \<rbrace>"
  apply (clarsimp simp: get_ptr_def,wp)
  apply (intro allI impI)
  apply (clarsimp simp: sep_conj_def) 
  apply (clarsimp simp: sep_coimpl_def pred_neg_def sep_conj_def)
  apply (clarsimp simp: septraction_def plus_fun_def plus_option_def pred_neg_def sep_impl_def maps_to_def sep_disj_fun_def sep_disj_option_def split: option.splits if_split_asm)
done

 
lemma get_ptr_sp: "\<lbrace>(R)\<rbrace> get_ptr p \<lbrace>\<lambda>rv. (p \<mapsto> rv \<and>* (p \<mapsto> rv -* R)) \<rbrace>"
  apply (clarsimp simp: get_ptr_def, wp)
  apply (intro allI impI)
  apply (clarsimp simp: sep_conj_def)
  apply (rule_tac x="[p \<mapsto> y] :: heap" in exI)
  apply (rule_tac x=" (\<lambda>a. if a = p then None else s a)" in exI)
  apply (intro conjI)
    apply (clarsimp simp: sep_disj_fun_def sep_disj_option_def)
     apply (rule ext, clarsimp simp: plus_fun_def plus_option_def)
       apply (clarsimp simp: maps_to_ex_def maps_to_def)
  apply (clarsimp simp: sep_coimpl_def sep_conj_def pred_neg_def sep_impl_def septraction_def)
    apply (rule_tac x="[p \<mapsto> y] :: heap" in exI)
             apply (clarsimp simp: maps_to_ex_def maps_to_def, rule conjI)
                 apply (clarsimp simp: sep_disj_fun_def sep_disj_option_def split: option.splits)
    apply (erule back_subst[where P=R])
      apply (rule ext, clarsimp simp: plus_fun_def plus_option_def split: option.splits)
 done
 
 lemma get_ptr_sp': "\<lbrace>\<lambda>s. (R (the (s p)) s )\<rbrace> get_ptr p \<lbrace>\<lambda>rv. (p \<mapsto> rv \<and>* (p \<mapsto> rv -* R rv)) \<rbrace>"
  apply (clarsimp simp: get_ptr_def, wp)
  apply (intro allI impI)
  apply (clarsimp simp: sep_conj_def)
  apply (rule_tac x="[p \<mapsto> y] :: heap" in exI)
  apply (rule_tac x=" (\<lambda>a. if a = p then None else s a)" in exI)
  apply (intro conjI)
    apply (clarsimp simp: sep_disj_fun_def sep_disj_option_def)
     apply (rule ext, clarsimp simp: plus_fun_def plus_option_def)
       apply (clarsimp simp: maps_to_ex_def maps_to_def)
  apply (clarsimp simp: sep_coimpl_def sep_conj_def pred_neg_def sep_impl_def septraction_def)
    apply (rule_tac x="[p \<mapsto> y] :: heap" in exI)
             apply (clarsimp simp: maps_to_ex_def maps_to_def, rule conjI)
                 apply (clarsimp simp: sep_disj_fun_def sep_disj_option_def split: option.splits)
    apply (erule_tac P="R y" in back_subst)
      apply (rule ext, clarsimp simp: plus_fun_def plus_option_def split: option.splits)
 done
 
 
 lemma extract_forall_septract:"(P -* (ALLS x. R x)) s \<Longrightarrow> \<forall>x. (P -* (R x)) s"
  apply (clarsimp simp: septraction_def pred_neg_def sep_impl_def)
  apply (erule_tac x=x in allE)
  apply (fastforce)
 done
 
 lemma septraction_snake_trivial_alls: "(P x -* (ALLS x. P x  \<leadsto>* R x)) s \<Longrightarrow> R x s" 
  apply (clarsimp simp: septraction_def )
  apply (clarsimp simp: pred_neg_def)
  apply (erule contrapos_np)
  apply (erule sep_curry[rotated])
  apply (rule_tac x=x in exI)
  apply (clarsimp simp: sep_coimpl_def)
  apply (sep_cancel)
  apply (clarsimp simp: pred_neg_def)
 done
 
 lemma get_ptr_valid: "\<lbrace>ALLS x. (p \<mapsto> x \<leadsto>* R x) \<rbrace> get_ptr p \<lbrace>\<lambda>rv. (p \<mapsto> rv \<and>* R rv) \<rbrace>"
 apply (rule hoare_strengthen_post, rule get_ptr_sp)
 apply (sep_cancel)
 apply (erule septraction_snake_trivial_alls)
 done
 

 definition "copy_ptr p p' = do x <- get_ptr p;
                                set_ptr p' x od"


 
 lemma precise_maps_to[precise]: "precise (p \<mapsto> v)"
  apply (clarsimp simp: precise_def maps_to_def)
  done
  
 lemma precise_maps_to_ex[precise]: "precise (p \<mapsto> -)"
  apply (clarsimp simp: precise_def maps_to_def maps_to_ex_def)
  apply (rule ext, clarsimp simp: sep_substate_def)
  apply (clarsimp simp: plus_fun_def plus_option_def)
  apply (drule fun_cong[where x=p], clarsimp split: option.splits) 
 by (metis (full_types) fun_upd_same option.distinct(2) option.simps(5) sep_disj_fun_def sep_disj_option_def)


lemma septract_maps_to:"(p \<mapsto> v -* (p \<mapsto> v' \<and>* R)) s \<Longrightarrow> R s \<and> v = v'"
 apply (clarsimp simp: septraction_def pred_neg_def sep_impl_def maps_to_def sep_conj_def)
 apply (rule conjI)
  apply (erule back_subst[where P=R])
  apply (rule ext)
  apply (drule_tac x=x in fun_cong)
  apply (clarsimp simp: plus_fun_def plus_option_def sep_disj_fun_def sep_disj_option_def)
  apply (erule_tac x=x in allE)
  apply (erule_tac x=x in allE)
  apply (clarsimp split: option.splits if_split_asm)
 apply (drule_tac x=p in fun_cong)
 apply (clarsimp simp: plus_fun_def plus_option_def sep_disj_fun_def sep_disj_option_def)
 apply (erule_tac x=p in allE)
 apply (erule_tac x=p in allE)
 apply (clarsimp split: option.splits)
done



lemma precise_conj_coimpl': "precise P \<Longrightarrow> (\<And>s R. (P \<and>* R) s \<Longrightarrow> (P \<leadsto>* R) s) "
  by (clarsimp simp: precise_conj_coimpl)
  
lemma septraction_precise_conj: "precise P \<Longrightarrow> (P -* (P \<and>* R)) s \<Longrightarrow> R s "
  apply (drule septraction_impl2)
   apply (erule (1) precise_conj_coimpl')
 by (erule septraction_snake_trivial)

                    
lemma septract_lift_pure[simp]: "(P -* (\<lambda>s. p \<and> Q s)) s \<longleftrightarrow> (P -* Q) s \<and> p"
  apply (rule iffI, rule conjI)
    using septraction_impl2 apply blast
   apply (clarsimp simp: septraction_def pred_neg_def sep_impl_def)
  apply (clarsimp simp: septraction_def pred_neg_def sep_impl_def)
 done

 lemma 
copy_ptr_wp: "\<lbrace>EXS x. (p \<mapsto> x \<and>* (p \<mapsto> x \<longrightarrow>* p' \<mapsto> - \<and>* (p' \<mapsto> x \<longrightarrow>* R))) \<rbrace> copy_ptr p p' \<lbrace>\<lambda>rv. R \<rbrace>"
  apply (clarsimp simp: copy_ptr_def)
  apply (rule hoare_seq_ext)
  apply (rule hoare_strengthen_post, rule precise_weaken_pre[OF precise_maps_to_ex], rule set_ptr_sp)
  apply (sep_erule (direct) sep_mp)
  apply (rule get_ptr_wp)
  done
  
  
 lemma sep_All_mp:"(P x \<and>* (ALLS v. P v \<longrightarrow>* R v)) s \<Longrightarrow> R x s"
   apply (clarsimp simp: sep_conj_def sep_impl_def)
   apply (erule_tac x=x in allE, erule_tac x=xa in allE)
  by (simp add: sep_add_commute sep_disj_commuteI)

  (* new_rules can be run in both directions *)

  lemma copy_ptr_wp': 
  "\<lbrace>ALLS x. (p \<mapsto> x \<leadsto>* (ALLS x. (p \<mapsto> x \<longrightarrow>* (p' \<mapsto> - \<leadsto>* p' \<mapsto> x \<longrightarrow>* R)) ))  \<rbrace> 
   copy_ptr p p'  \<lbrace>\<lambda>rv. R\<rbrace>"
  apply (clarsimp simp: copy_ptr_def)
  apply (rule hoare_seq_ext)
   apply (rule hoare_strengthen_post, rule set_ptr_sp)
   apply (sep_erule (direct) sep_mp)
  apply (rule hoare_strengthen_post, rule get_ptr_valid)
  apply (erule sep_All_mp)
  done
  
 
lemma copy_ptr_sp: 
  "\<lbrace>R\<rbrace> copy_ptr p p'  \<lbrace>\<lambda>rv. \<exists>x. (p' \<mapsto> x \<and>* (p' \<mapsto> - -*  (p \<mapsto> x \<and>* (p \<mapsto> x -* R)))) \<rbrace>" 
   apply (clarsimp simp: copy_ptr_def )
   apply (rule seq_ext)
    apply (rule get_ptr_sp)
   apply (rule hoare_chain)   
      apply (rule set_ptr_sp, erule (1) sep_snake_septraction)
   apply (rule_tac x=x in exI, clarsimp)
  done
   
 
  lemma copy_ptr_valid: "\<lbrace>(p \<mapsto> x \<and>* p' \<mapsto> - \<and>* R)\<rbrace> copy_ptr p p'  \<lbrace>\<lambda>_. (p \<mapsto> x \<and>* p' \<mapsto> x \<and>* R) \<rbrace>" 
   apply (wp copy_ptr_wp)
   apply (rule_tac x=x in exI)
   apply (sep_solve)
  done

lemma copy_ptr_valid'': "\<lbrace>(p \<mapsto> x \<and>* p' \<mapsto> - \<and>* (p \<mapsto> x \<and>* p' \<mapsto> x \<longrightarrow>* R))\<rbrace> copy_ptr p p'  \<lbrace>\<lambda>_. (R) \<rbrace>" 
   apply (rule hoare_chain, rule copy_ptr_valid)
   apply (assumption)
   apply (sep_solve)
  done

lemma copy_ptr_wp'': "\<lbrace>EXS x. (p \<mapsto> x \<and>* p' \<mapsto> - \<and>* (p \<mapsto> x \<and>* p' \<mapsto> x \<longrightarrow>* R))\<rbrace> 
   copy_ptr p p'  \<lbrace>\<lambda>_. (R) \<rbrace>" 
 apply (rule hoare_weaken_pre, rule copy_ptr_wp, clarsimp)
 apply (rule_tac x=x in exI)
 apply (sep_cancel)+
 apply (sep_solve)
done

        
lemma copy_ptr_valid': "\<lbrace>(p \<mapsto> x \<and>* p' \<mapsto> - \<and>* R)\<rbrace> copy_ptr p p'  \<lbrace>\<lambda>_. (p \<mapsto> x \<and>* p' \<mapsto> x \<and>* R) \<rbrace>" 
  apply (rule hoare_strengthen_post[OF copy_ptr_sp], elim exE)
  apply (sep_drule septraction_impl2)
   apply (sep_drule septract_maps_to, assumption, clarsimp simp: sep_conj_assoc)
  apply (sep_drule septraction_impl2, erule precise_conj_coimpl'[OF precise_maps_to_ex])
  apply (sep_drule septraction_snake_trivial)
  apply (sep_solve)
done   

definition "swap_ptr p p' = do np <- new_ptr;
                              copy_ptr p np;
                              copy_ptr p' p;
                              copy_ptr np p';
                              delete_ptr np od"

lemma delete_ptr_sp': "\<lbrace>R\<rbrace> delete_ptr p \<lbrace>\<lambda>_. (p \<mapsto> - -* R)\<rbrace>"
 apply (rule hoare_weaken_pre[OF delete_ptr_sp])
 apply (erule (1) sep_snake_septraction)
 done

lemma extract_exs_septraction_simp[simp]: "(P -* (EXS v. R v)) = (EXS v. (P -* R v) )"  
 apply (rule ext, rule iffI)
 apply (fastforce simp: septraction_def sep_impl_def pred_neg_def)
 apply (fastforce simp: septraction_def sep_impl_def pred_neg_def)
done
 

lemma extract_exs_septraction_simp'[simp]: "((EXS v. R v) -* P ) = (EXS v. (R v -* P) )" 
 apply (rule ext, rule iffI; fastforce simp: septraction_def sep_impl_def pred_neg_def)
 done
 


lemma new_ptr_wp: "\<lbrace>ALLS p. (p \<mapsto> - \<longrightarrow>* R p)\<rbrace> new_ptr \<lbrace> R \<rbrace>"
   apply (rule hoare_chain, rule new_ptr_sp, assumption)
using sep_conj_commuteI sep_conj_sep_impl2 by blast


lemma delete_ptr_valid: "\<lbrace>(p \<mapsto> - \<and>* R )\<rbrace> delete_ptr p \<lbrace>\<lambda>_. R  \<rbrace>"
 apply (rule hoare_weaken_pre[OF delete_ptr_sp])
 by (erule precise_conj_coimpl'[OF precise_maps_to_ex])


lemma swap_ptr_valid: "\<lbrace>(p \<mapsto> v \<and>* p' \<mapsto> v' \<and>* R)\<rbrace> swap_ptr p p' \<lbrace>\<lambda>_. (p \<mapsto> v' \<and>* p' \<mapsto> v \<and>* R)\<rbrace>"
   apply (clarsimp simp: swap_ptr_def)
   apply (wp delete_ptr_valid)
        apply (wp copy_ptr_wp new_ptr_wp)+ 
   apply (clarsimp simp: sep_conj_exists)
   apply (sep_cancel)
   apply (rule_tac x=v in exI)
   apply (sep_cancel)+
   apply (rule_tac x=v' in exI)
   apply (sep_cancel add: maps_to_maps_to_ex)+
   apply (rule exI)
   by (sep_solve add: maps_to_maps_to_ex)

lemma septraction_lens: "((P -* Q) \<and>* R) s \<Longrightarrow> (\<And>s. Q' s = Q s) \<Longrightarrow> ((P -* Q') \<and>* R) s" 
  apply (sep_cancel) using septract_cancel by blast  

lemmas septraction_lens' = septraction_lens[where R=\<box>, simplified]  
  
ML{*
  fun septraction_drule thms ctxt = 
     let val lens  = dresolve0_tac  [@{thm septraction_lens}]
         val r = rotator' ctxt
      in sep_drule_tac (dresolve0_tac thms |> r lens) ctxt
   end; 

fun septraction_drule_method  thms ctxt = SIMPLE_METHOD' (septraction_drule  thms ctxt) 

 fun septraction_drule' thms ctxt = 
     let val lens  = dresolve0_tac  [@{thm septraction_lens'}]
         val r = rotator' ctxt
      in (dresolve0_tac thms |> r lens)
   end; 

fun septraction_drule_method'  thms ctxt = SIMPLE_METHOD' (septraction_drule'  thms ctxt) 

*}

method_setup septract_drule = {*
  (Attrib.thms) >>  septraction_drule_method
*}

method_setup septract_drule' = {*
  (Attrib.thms) >>  septraction_drule_method'
*}
   
lemma septract_maps_to1:"((p \<mapsto> v -* (p \<mapsto> v' \<and>* R)) \<and>* Q) s \<Longrightarrow> ((R \<and>* Q) and K(v = v')) s"
by (sep_drule septract_maps_to, clarsimp)

lemma septract_maps_to2: "((p \<mapsto> v -* (p \<mapsto> - \<and>* R)) \<and>* Q) s \<Longrightarrow> (R \<and>* Q) s" 
apply (sep_cancel)
  using precise_maps_to_ex septraction_impl1 septraction_precise_conj by fastforce

lemma septract_maps_to3: "((p \<mapsto> - -* (p \<mapsto> v' \<and>* R)) \<and>* Q) s \<Longrightarrow> (R \<and>* Q) s " 
  apply (sep_cancel)
  by (smt maps_to_maps_to_ex precise_conj_coimpl precise_maps_to_ex sep_rule sep_septraction_snake)

lemma septract_maps_to4: "((p \<mapsto> - -* (p \<mapsto> - \<and>* R)) \<and>* Q) s \<Longrightarrow> (R \<and>* Q) s"
  apply (sep_cancel)
 using precise_maps_to_ex septraction_precise_conj by blast 

lemmas septract_maps_to_set = septract_maps_to1 septract_maps_to2 septract_maps_to3 septract_maps_to4

lemmas septract_maps_to_set' = septract_maps_to_set[where Q=sep_empty, simplified]

lemma septraction_extract_pure[simp]: "(P -* (\<lambda>s. R s \<and> r)) = ((P -* R) and K r)"
  by (rule ext, rule iffI; fastforce simp: septraction_def sep_impl_def pred_neg_def) 
(*
method septract_cancel = ((septract_drule septract_maps_to_set | septract_drule' septract_maps_to_set') |
                          ((sep_drule septraction_impl2 | drule septraction_impl2), septract_cancel, assumption))  
          
 (* now forwards *)
*)
        
lemma maps_to_pointer[precise]: "pointer (maps_to p)" 
 apply (clarsimp simp:  pointer_def maps_to_def 
  sep_conj_def sep_coimpl_def pred_neg_def)
  apply (subgoal_tac "x=y", simp)
  apply (metis sep_add_cancelD sep_add_commute sep_disj_commuteI)
  apply (drule_tac x=p in fun_cong)
 apply (clarsimp simp: plus_fun_def plus_option_def split: option.splits)
  apply (clarsimp simp: sep_disj_fun_def)
  apply (erule_tac x=p in allE)
  apply (erule_tac x=p in allE)
apply (clarsimp simp: sep_disj_fun_def sep_disj_option_def)
done

            
lemma swap_ptr_valid': "\<lbrace>(p \<mapsto> v \<and>* p' \<mapsto> v' \<and>* R)\<rbrace> swap_ptr p p' 
                       \<lbrace>\<lambda>_. (p \<mapsto> v' \<and>* p' \<mapsto> v \<and>* R)\<rbrace>"
  apply (clarsimp simp: swap_ptr_def, intro seq_ext)
      apply (rule new_ptr_sp)
     apply (rule copy_ptr_sp)+
  apply (rule hoare_strengthen_post[OF delete_ptr_sp'])
    apply (clarsimp simp: sep_conj_exists2 sep_conj_assoc)
  apply (sep_invert, sep_forward+, simp, sep_solve)
done
 
 
primrec
  list :: "nat \<Rightarrow> nat list \<Rightarrow> heap \<Rightarrow> bool"
where
  "list i [] = (\<langle>i=0\<rangle> and \<box>)"
| "list i (x#xs) = (\<langle>i=x \<and> i\<noteq>0\<rangle> and (EXS j. i \<mapsto> j ** list j xs))"

lemma list_empty [simp]:
  shows "list 0 xs = (\<lambda>s. xs = [] \<and> \<box> s)"
  by (cases xs) auto
  
lemma list_nonempty:
 shows "0 < i \<Longrightarrow> list i xs = (EXS h t.  (\<langle>i= (h) \<and> i\<noteq>0 \<and> xs = h#t \<rangle> and (EXS j. i \<mapsto> j ** list j (t))))"
  apply (cases xs; clarsimp)
  defer
  apply (rule ext, rule iffI)
  apply (clarsimp simp: pred_conj_def)
    apply (clarsimp simp: pred_conj_def)
done



lemma "
 \<lbrace>((p \<mapsto> - and (\<lambda>s. p \<noteq>0)) \<and>* list q qs)\<rbrace>
 set_ptr p q
 \<lbrace>\<lambda>_. list p (p#qs) \<rbrace>"
  apply (rule hoare_chain, rule precise_weaken_pre[OF precise_maps_to_ex], rule set_ptr_sp)
  defer
  apply (sep_erule (direct) sep_mp)
  apply (clarsimp simp: pred_conj_def)
  apply (sep_cancel)
  apply (sep_lift)
  apply (rule_tac x=q in exI, sep_solve)
  done

 lemma set_ptr_wp: "\<lbrace>(p \<mapsto> - \<and>* (p \<mapsto> v \<longrightarrow>* R)) \<rbrace> set_ptr p v \<lbrace>\<lambda>_. R\<rbrace>"
  apply (rule hoare_chain, rule set_ptr_sp)
  apply (erule precise_conj_coimpl'[OF precise_maps_to_ex])
  apply (sep_solve)
 done
  

definition "NULL \<equiv> 0::nat"

declare NULL_def[simp]

definition list_rev where  
  "list_rev p = do (hd_ptr, rev)  <- whileLoop  (\<lambda>(hd_ptr, rev) s. hd_ptr \<noteq> NULL)
                                    (\<lambda>(hd_ptr, rev). do next_ptr <- get_ptr hd_ptr;
                                                   set_ptr hd_ptr rev;
                                                   return (next_ptr, hd_ptr) od) (p, NULL) ;
                    return rev 
                    od   " 

definition "reverse_inv xs list' rev' =
                 (EXS ys zs. (list list' ys \<and>*
                     list rev' zs) 
                    and (\<lambda>s. rev xs = rev ys @ zs) )"


lemma list_rev_valid_wp:"
  \<lbrace>(list p ps)\<rbrace>
  list_rev p
  \<lbrace>\<lambda>rv. list (rv) (rev ps) \<rbrace>"
  apply (clarsimp simp: list_rev_def, wpsimp)
   apply (subst whileLoop_add_inv [where
        I="\<lambda>(list', rev'). (EXS ys zs. (list list' ys \<and>*
                     list rev' zs) 
                    and (\<lambda>s. rev ps = rev ys @ zs)) ",
        unfolded reverse_inv_def])
   apply (wp whileLoop_wp_inv; clarsimp)
   apply (wp set_ptr_wp get_ptr_wp)
   apply (clarsimp simp: pred_conj_def  sep_conj_exists sep_conj_assoc)
   apply (case_tac x; clarsimp simp: pred_conj_def sep_conj_exists sep_conj_assoc)
   apply (rule_tac exI)
   apply (sep_cancel add: maps_to_maps_to_ex)+
   apply (rule_tac x=lista in exI)
   apply (rule_tac x="aa # xa" in exI)
   apply (intro conjI)
   apply (clarsimp)
    apply (sep_cancel)
    apply (rule_tac x=b in exI)
    apply (sep_cancel)
   apply (clarsimp)
  apply (clarsimp split: prod.splits)
 done

    
 lemma septract_extra_pure1[simp]: "(P -* (\<lambda>s. Q s \<and> q)) = ((P -* Q) and (\<lambda>s. q))"
 by (rule ext, rule iffI; fastforce simp: pred_conj_def septraction_def sep_impl_def pred_neg_def)
 lemma septract_extra_pure2[simp]: "(P -* (\<lambda>s. q \<and> Q s)) = ((P -* Q) and (\<lambda>s. q))"
 by (rule ext, rule iffI; fastforce simp: pred_conj_def septraction_def sep_impl_def pred_neg_def)
    

lemma septract_false[simp] :"(P -* (sep_false)) = sep_false"
  using sep_septraction_snake by blast

lemma whileLoop_sp_inv:
  "\<lbrakk> \<And>r. \<lbrace>\<lambda>s. I r s \<and> C r s\<rbrace> B r \<lbrace>I\<rbrace>; \<And>s. P s \<Longrightarrow> I r s \<rbrakk>
      \<Longrightarrow> \<lbrace> P \<rbrace> whileLoop_inv C B r I M \<lbrace>\<lambda>rv s. I rv s \<and> \<not> C rv s  \<rbrace>"
  apply (clarsimp simp: whileLoop_inv_def) 
  apply (rule hoare_weaken_pre)
  apply (rule valid_whileLoop [where P=I and I=I]; fastforce)
  apply (assumption)
  done


lemma sep_conj_coimpl_mp:"(P \<and>* R) s \<Longrightarrow> (P \<leadsto>* Q) s \<Longrightarrow> (P \<and>* (Q and R)) s"
 apply (drule (2) sep_coimpl_mp_gen, clarsimp simp: pred_conj_def conj_commute)
done

 lemma list_rev_valid_sp: "
  \<lbrace>(list p ps \<and>* R)\<rbrace>
  list_rev p
  \<lbrace>\<lambda>rv. (list (rv) (rev ps) \<and>* R) \<rbrace>"
  apply (clarsimp simp: list_rev_def)
  apply (subst whileLoop_add_inv [where
  I="\<lambda>(list', rev') s. (reverse_inv ps list' rev' \<and>* R) s ",
  unfolded reverse_inv_def])
  apply (sp sp: whileLoop_sp_inv)
  apply (clarsimp)
  apply (sp sp: get_ptr_sp set_ptr_sp')
 apply (clarsimp)
  apply (clarsimp simp: pred_conj_def sep_conj_exists sep_conj_assoc, case_tac x; clarsimp simp: pred_conj_def sep_conj_exists sep_conj_assoc)
  apply (sep_invert; sep_forward+)
  apply (clarsimp)
  apply (rule exI, rule exI, intro conjI, fastforce)
 apply (clarsimp simp: pred_conj_def sep_conj_exists)
  apply (rule_tac exI)
 apply (sep_solve)
  apply (clarsimp)+
  apply (sp, clarsimp)
done


lemma "P s \<Longrightarrow> Q s \<Longrightarrow> (P \<and>* (Q -* (P and Q))) s"
  by (metis disjoint_zero_sym pred_andI pred_neg_def sep_add_zero_sym sep_conjI sep_conj_commuteI sep_mp septraction_def)




end