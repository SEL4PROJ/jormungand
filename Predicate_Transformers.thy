(*
 * Copyright 2017, Data61, CSIRO
 *
 * This software may be distributed and modified according to the terms of
 * the BSD 2-Clause license. Note that NO WARRANTY is provided.
 * See "LICENSE_BSD2.txt" for details.
 *
 * @TAG(DATA61_BSD)
 *)

(*
  A simple example of strongest-post and weakest-pre reasoning in separation
  logic with wand and snake.
 *)

theory Predicate_Transformers
imports
  "Hoare_Sep_Tactics/Simple_Separation_Example"
begin

definition "select s = (SOME p. s p = None)"

definition "wlp P f Q \<equiv> (\<forall>P'. \<lbrace>P'\<rbrace> f \<lbrace>Q\<rbrace> \<longrightarrow> 
          (\<forall>s. P' s \<longrightarrow> P s) \<and> \<lbrace>P\<rbrace> f \<lbrace>Q\<rbrace>)"   

lemma maps_to_none_snake: " s p = None \<Longrightarrow> (p \<mapsto> - \<leadsto>* sep_false) s"
 apply (clarsimp simp: sep_coimpl_def sep_conj_def pred_neg_def)
 apply (clarsimp simp: plus_fun_def plus_option_def maps_to_def maps_to_ex_def)
done
 

lemma wlp_snake_delete: "wlp (p \<mapsto> - \<leadsto>* Q ()) (delete_ptr p) Q "
 unfolding wlp_def
 apply (safe)
 apply (clarsimp simp: valid_def delete_ptr_def 
         bind_def gets_def assert_def get_def return_def modify_def 
        put_def  fail_def split: prod.splits if_splits)
 apply (erule_tac x=s in allE, simp)
 apply (erule disjE)
 apply (clarsimp simp: sep_coimpl_def sep_conj_def pred_neg_def)
 apply (clarsimp simp: plus_fun_def maps_to_def maps_to_ex_def sep_disj_fun_def)
 apply (erule_tac x=p in allE)
 apply (fastforce simp: sep_disj_option_def)
 apply (erule disjE)
 apply (fastforce)
 apply (clarsimp simp: fun_upd_def[symmetric])
 apply (clarsimp simp: sep_coimpl_def sep_conj_def pred_neg_def)
 apply (erule subst[rotated, where P="Q ()"]) 
 apply (rule ext)
 apply (clarsimp simp: plus_fun_def maps_to_def maps_to_ex_def sep_disj_fun_def)
 apply (erule_tac x=p in allE)
 apply (fastforce simp: sep_disj_option_def)
  using delete_ptr_sp hoare_chain by fastforce


lemma wlp_snake_get: "wlp (\<lambda>s. \<forall>x. (p \<mapsto> x \<leadsto>* (p \<mapsto> x \<longrightarrow>* Q x)) s) (get_ptr p) Q"
 unfolding wlp_def
  apply (safe)
  apply (clarsimp simp: valid_def get_ptr_def return_def modify_def 
                        bind_def gets_def assert_def get_def 
                        put_def  fail_def 
                 split: prod.splits if_splits)
  apply (erule_tac x=s in allE, simp)
  apply (erule disjE)
   apply (drule maps_to_none_snake)
  using sep_coimpl_cancel sep_coimpl_weaken apply fastforce
   apply (erule disjE, blast)
   apply (case_tac "x = (the (s p))", simp)
    apply (clarsimp simp: sep_coimpl_def sep_conj_def pred_neg_def sep_impl_def maps_to_def
                          maps_to_ex_def)
    apply (erule_tac P="Q (the (s p))" in subst[rotated])
    apply (rule ext)
    apply (clarsimp simp: plus_fun_def )
    apply (intro conjI)
     apply (clarsimp simp: the_def)
     apply (frule_tac x=p in fun_cong)
     apply (clarsimp simp: plus_fun_def sep_add_commute sep_disj_commute)
     apply (metis (no_types, lifting) fun_upd_same sep_add_commute sep_disj_fun_def)
    apply (frule_tac x=x in fun_cong)
    apply (clarsimp simp: plus_fun_def sep_add_commute sep_disj_commute)
   apply (subgoal_tac "(p \<mapsto> x \<leadsto>* sep_false) s")
  using sep_coimpl_cancel' apply blast
   apply (simp add: sep_coimpl_def)
   apply (rule notI)
   apply (clarsimp simp: sep_conj_def pred_neg_def)
   apply (erule notE)
   apply (clarsimp simp: maps_to_def)
   apply (clarsimp simp: sep_disj_fun_def)
   apply (erule_tac x=p in allE, clarsimp simp: sep_disj_option_def)
   apply (clarsimp simp: plus_fun_def plus_option_def)
  apply (clarsimp simp: get_ptr_def, Det_Monad.wp)
  apply (clarsimp)
  apply (erule_tac x=y in allE)
  apply (clarsimp simp: sep_coimpl_def sep_conj_def pred_neg_def sep_impl_def maps_to_def
                        maps_to_ex_def)
  apply (erule_tac x="s(p:= None)" in allE)
  apply (drule mp)
   apply (clarsimp simp: sep_disj_fun_def)
  apply (drule mp)
   apply (rule ext, clarsimp simp: plus_fun_def)
  apply (drule mp)
   apply (clarsimp simp: sep_disj_fun_def)
  apply (erule_tac P="Q y" in subst[rotated])
  apply (rule ext, clarsimp simp: plus_fun_def)
  done

lemma wlp_snake_set: "wlp (p \<mapsto> - \<leadsto>* (p \<mapsto> v \<longrightarrow>* Q ())) (set_ptr p v) Q "
  unfolding wlp_def
  apply (safe)
  apply (clarsimp simp: valid_def set_ptr_def get_def return_def modify_def
                        bind_def gets_def assert_def put_def fail_def
                 split: prod.splits if_splits)
   apply (erule_tac x=s in allE, simp)
   apply (erule disjE)
    apply (drule maps_to_none_snake)
  using sep_coimpl_cancel' apply blast
   apply (erule disjE)
    apply (blast)
 apply (clarsimp simp: sep_coimpl_def sep_conj_def pred_neg_def sep_impl_def maps_to_def
                       maps_to_ex_def)
   apply (erule_tac P="Q ()" in subst[rotated])
   apply (rule ext)
   apply (clarsimp simp: plus_fun_def)
   apply (subgoal_tac "ya p = 0", simp)
   apply (clarsimp simp: sep_disj_fun_def sep_disj_option_def, erule_tac x=p in allE, fastforce)
  apply (rule hoare_chain[OF set_ptr_sp], fastforce)
  apply (sep_mp)
  by simp

lemma wlp_wand_new: "wlp (\<lambda>s. (select s \<mapsto> 0 \<longrightarrow>* Q (select s)) s) 
                     (new_ptr) Q "
  unfolding wlp_def select_def
  apply (safe)
   apply (clarsimp simp: valid_def new_ptr_def bind_def gets_def assert_def
                         get_def return_def modify_def put_def fail_def
                  split: prod.splits if_splits)
   apply (erule_tac x=s in allE, simp)
   apply (erule disjE)
    apply (clarsimp simp: sep_impl_def maps_to_def maps_to_ex_def)
    apply (erule_tac x="(SOME p. s p = None)" in allE)
    apply (clarsimp simp: sep_disj_fun_def)
    apply (erule_tac x="(SOME p. s p = None)" in allE)
    apply (fastforce simp: sep_disj_option_def)
   apply (erule disjE)
    apply (blast)
   apply (clarsimp simp: sep_impl_def)
   apply (clarsimp simp: maps_to_ex_def maps_to_def)
   apply (erule_tac P="Q (SOME p. s p = None)" in subst[rotated])
   apply (rule ext, clarsimp simp: plus_fun_def )
   apply (subgoal_tac "s (SOME p. s p = None) = 0") 
    apply (clarsimp)
   apply (clarsimp simp: zero_option_def)
   apply (metis (mono_tags) fun_upd_same option.simps(5)
          sep_disj_commuteI sep_disj_fun_def sep_disj_option_def)
  apply (clarsimp simp: new_ptr_def, Det_Monad.wp)
  apply (clarsimp)
  apply (clarsimp simp: sep_impl_def)
  apply (erule_tac x= "[(SOME p. s p = None) \<mapsto> 0] :: heap" in allE)
  apply (drule mp)
   apply (intro conjI)
    apply (clarsimp simp: sep_disj_fun_def)
   apply (clarsimp simp: maps_to_def)
  apply (erule_tac P="Q (SOME p. s p = None)" in subst[rotated])
  apply (rule ext)
  apply (clarsimp simp: plus_fun_def)
  done


lemma[wp_pre']: " \<lbrakk>\<lbrace>P\<rbrace> f \<lbrace>Q\<rbrace>!; \<And>s. R s \<Longrightarrow> P s\<rbrakk> \<Longrightarrow> \<lbrace>R\<rbrace> f \<lbrace>Q\<rbrace>!"
  by (clarsimp simp: validNF_def)

declare bind_wp_nf[rotated, wp']

lemma put_wp_nf[wp']:  "\<lbrace>\<lambda>s'. P () s\<rbrace> put s \<lbrace>P\<rbrace>!" by (clarsimp simp: validNF_def put_def)
lemma get_wp_nf[wp']:  "\<lbrace>\<lambda>s. P s s\<rbrace> get \<lbrace>P\<rbrace>!" by (clarsimp simp: validNF_def get_def)
lemma return_wp_nf[wp']:  "\<lbrace>P x\<rbrace> return x \<lbrace>P\<rbrace>!" by (clarsimp simp: validNF_def return_def)

lemma assert_wp_nf[wp']:  "\<lbrace>\<lambda>s. Q \<and> P () s\<rbrace> assert Q \<lbrace>P\<rbrace>!" 
 apply (clarsimp simp: validNF_def assert_def return_def)
done

lemma modify_wp_nf[wp']: "\<lbrace>\<lambda>s. P () (f s)\<rbrace> modify f \<lbrace>P\<rbrace>!" by 
 (clarsimp simp: modify_def, Det_Monad.wp)

 lemma hoare_chainNF:
  "\<lbrakk> \<lbrace>P\<rbrace> f \<lbrace>Q\<rbrace>!; \<And>s. R s \<Longrightarrow> P s; \<And>r s. Q r s \<Longrightarrow> S r s \<rbrakk> \<Longrightarrow> \<lbrace>R\<rbrace> f \<lbrace>S\<rbrace>!"
  by (fastforce simp: validNF_def)

lemma sep_conj_exists: "(p \<mapsto> - \<and>* R) s \<Longrightarrow> \<exists>v. s p = Some v" 
  apply (clarsimp simp: sep_conj_def maps_to_def maps_to_ex_def)
  apply (rule_tac x=y in exI)
  apply (clarsimp simp: plus_fun_def sep_disj_fun_def sep_disj_option_def)
  by (smt None_plus fun_upd_same option.simps(5))

definition "wp P f Q \<equiv> (\<forall>P'. \<lbrace>P'\<rbrace> f \<lbrace>Q\<rbrace>! \<longrightarrow> 
          (\<forall>s. P' s \<longrightarrow> P s) \<and> \<lbrace>P\<rbrace> f \<lbrace>Q\<rbrace>!)"

lemma wp_star_delete: "wp (p \<mapsto> - \<and>* Q ()) (delete_ptr p) Q"
unfolding wp_def
  apply (safe)
  defer
  apply (clarsimp simp:delete_ptr_def gets_def, Det_Monad.wp)
  apply (rule conjI)
  apply (erule sep_conj_exists)
  apply (clarsimp simp: sep_conj_def)
  apply (erule subst[where P="Q()", rotated])
  apply (rule ext)
  apply (clarsimp simp: sep_disj_fun_def)
  apply (erule_tac x=p in allE)
  apply (clarsimp simp: maps_to_def maps_to_ex_def sep_disj_option_def plus_fun_def)
  apply (clarsimp simp: validNF_def delete_ptr_def bind_def gets_def put_def 
                        assert_def get_def return_def modify_def fail_def
                 split: prod.splits if_splits)
  apply (erule_tac x=s in allE)
  apply (clarsimp, safe; simp?)
    apply (fastforce)
   apply (fastforce)
  apply (fold fun_upd_def)
  apply (clarsimp simp:  sep_conj_def pred_neg_def)
  apply (clarsimp simp: maps_to_ex_def maps_to_def)
  apply (rule_tac x="[p \<mapsto> y] :: heap" in exI)
  apply (rule_tac x="(s(p := None))" in exI)
  apply (clarsimp)
  apply (intro conjI)
    apply (clarsimp simp: plus_fun_def maps_to_def maps_to_ex_def sep_disj_fun_def)
   apply (rule ext)
   apply (clarsimp simp: plus_fun_def maps_to_def maps_to_ex_def sep_disj_fun_def)
  apply (blast)
  apply (blast)
  apply (blast)
  done

lemma wp_star_set: "wp (p \<mapsto> - \<and>* (p \<mapsto> v \<longrightarrow>* Q ())) (set_ptr p v) Q"
 unfolding wp_def
 apply (safe)
apply (clarsimp simp: validNF_def set_ptr_def bind_def gets_def assert_def get_def
          return_def modify_def put_def fail_def split: prod.splits if_splits)
  apply (erule_tac x=s in allE)
  apply (clarsimp, safe; (simp | blast)?)
  apply (clarsimp simp: sep_conj_def)
  apply (rule_tac x="[p \<mapsto> y] :: heap" in exI)
  apply (rule_tac x="s(p := 0)" in exI)
  apply (intro conjI)
     apply (clarsimp simp: sep_disj_fun_def)
    apply (rule ext, clarsimp simp: plus_fun_def)
   apply (fastforce simp: maps_to_ex_def maps_to_def)
  apply (clarsimp simp: sep_impl_def)
  apply (erule subst[where P="Q()", rotated])
  apply (rule ext, clarsimp simp: plus_fun_def)
  apply (clarsimp simp: maps_to_def sep_disj_fun_def sep_disj_option_def)
  apply (clarsimp simp: set_ptr_def gets_def, Det_Monad.wp)
  apply (rule conjI)
  apply (erule sep_conj_exists)
  apply (clarsimp simp: sep_conj_def sep_impl_def maps_to_ex_def maps_to_def)
  apply (drule mp)
  apply (clarsimp simp: sep_disj_fun_def)
  apply (erule_tac x=p in allE, clarsimp simp: sep_disj_option_def)
  apply (erule subst[where P="Q()", rotated])
  apply (rule ext, clarsimp simp: plus_fun_def)
  apply (clarsimp simp: maps_to_def sep_disj_fun_def sep_disj_option_def)
  by (simp add: option.case_eq_if)

lemma wp_star_get: "wp (EXS x. (p \<mapsto> x \<and>* (p \<mapsto> x \<longrightarrow>* Q x))) (get_ptr p) Q"
  unfolding wp_def
  apply (safe)
   apply (clarsimp simp: validNF_def get_ptr_def  bind_def gets_def fail_def
                         assert_def get_def return_def modify_def put_def
                  split: prod.splits if_splits)
   apply (erule_tac x=s in allE)
   apply (clarsimp, safe; (simp | blast)?)
   apply (rule_tac x=y in exI)
   apply (clarsimp simp: sep_conj_def)
   apply (rule_tac x="[p \<mapsto> y] :: heap" in exI)
   apply (rule_tac x="s(p := 0)" in exI)
   apply (intro conjI)
      apply (clarsimp simp: sep_disj_fun_def)
     apply (rule ext, clarsimp simp: plus_fun_def)
    apply (fastforce simp: maps_to_ex_def maps_to_def)
   apply (clarsimp simp: sep_impl_def)
   apply (erule_tac P="Q y" in subst[rotated])
   apply (rule ext, clarsimp simp: plus_fun_def)
   apply (clarsimp simp: maps_to_def sep_disj_fun_def sep_disj_option_def)
  apply (clarsimp simp: get_ptr_def gets_def)
  apply (Det_Monad.wp)
  apply (clarsimp)
  apply (rule conjI)
   apply (sep_drule maps_to_maps_to_ex)
   apply (erule sep_conj_exists)
  apply (clarsimp simp: sep_conj_def sep_impl_def maps_to_ex_def maps_to_def)
  apply (drule mp)
   apply (clarsimp simp: sep_disj_fun_def)
   apply (erule_tac x=p in allE, clarsimp simp: sep_disj_option_def)
  apply (subgoal_tac "the (([p \<mapsto> x] + y) p) = x", simp)
   apply (erule_tac P="Q x" in subst[rotated])
   apply (rule ext, clarsimp simp: plus_fun_def)
   apply (clarsimp simp: maps_to_def sep_disj_fun_def sep_disj_option_def)
   apply (simp add: option.case_eq_if)
  apply (clarsimp simp: plus_fun_def)
  by (clarsimp simp: plus_option_def sep_disj_option_def sep_disj_fun_def split: option.splits)

lemma wp_septract_new: "wp (\<lambda>s. (select s \<mapsto> 0 -* Q ((select s))) s)
            (new_ptr) Q"
  unfolding wp_def select_def
  apply (safe)
   apply (clarsimp simp: validNF_def new_ptr_def bind_def gets_def assert_def
                         get_def return_def modify_def put_def fail_def
                  split: prod.splits if_splits)
   apply (erule_tac x=s in allE)
   apply (clarsimp, safe; (simp | blast)?)
    apply (erule_tac x=p in allE)
    apply (fastforce)
   apply (clarsimp simp: septraction_def sep_impl_def pred_neg_def)
   apply (rule_tac x="[(SOME p. s p = None) \<mapsto> 0] :: heap" in exI)
   apply (intro conjI)
     apply (clarsimp simp: sep_disj_fun_def)
    apply (fastforce simp: maps_to_ex_def maps_to_def)
   apply (erule_tac P="Q (SOME p. s p = None)" in subst[rotated])
   apply (rule ext, clarsimp simp: plus_fun_def)
  apply (clarsimp simp: new_ptr_def gets_def)
  apply (Det_Monad.wp)
  apply (clarsimp)
  apply (rule conjI)
   apply (rule_tac x="(SOME p. s p = None)" in exI)
   apply (clarsimp simp: septraction_def sep_impl_def pred_neg_def)
   apply (clarsimp simp: maps_to_ex_def maps_to_def)
   apply (smt fun_upd_same option.simps(5) sep_disj_commuteI sep_disj_fun_def sep_disj_option_def)
  apply (clarsimp simp: septraction_def sep_impl_def pred_neg_def)
  apply (clarsimp simp: maps_to_ex_def maps_to_def)
  apply (erule_tac P="Q (SOME p. s p = None)" in subst[rotated])
  apply (rule ext, clarsimp simp: plus_fun_def)
  by (smt fun_upd_same option.simps(4) option.simps(5)
          plus_option_def sep_disj_commuteI sep_disj_fun_def sep_disj_option_def)


definition "sp P f Q \<equiv>  (\<forall>Q'. \<lbrace>P\<rbrace> f \<lbrace>Q'\<rbrace> \<longrightarrow> 
          (\<forall>s rv . Q rv s \<longrightarrow> Q' rv s) ) \<and> \<lbrace>P\<rbrace> f \<lbrace>Q\<rbrace> "

lemma sp_snake_delete: "sp (P) (delete_ptr p) (\<lambda>_. p \<mapsto> - -* P) "
  unfolding sp_def
  apply (clarsimp simp: sp_def)
  apply (intro conjI)
   apply (clarsimp simp: valid_def delete_ptr_def bind_def gets_def assert_def get_def
                      return_def modify_def put_def fail_def
               split: prod.splits if_splits)
   apply (clarsimp simp: septraction_def pred_neg_def sep_impl_def)
   apply (erule_tac x="s + h'" in allE)
   apply (clarsimp)
   apply (clarsimp simp: sep_disj_fun_def plus_fun_def maps_to_def 
                         maps_to_ex_def plus_option_def 
                  split: option.splits)
    apply (erule_tac x=p in allE)
    apply (erule_tac P="Q' ()" in back_subst)
    apply (rule ext)
    apply (clarsimp)
    apply (clarsimp simp: sep_disj_fun_def plus_fun_def maps_to_def 
                          maps_to_ex_def plus_option_def 
                   split: option.splits)
   apply (erule_tac x=p in allE)
   apply (fastforce simp: sep_disj_option_def)
  by (simp add: delete_ptr_sp')

lemma sp_snake_set: "sp (P) (set_ptr p v) (\<lambda>_. (p \<mapsto> v \<and>* (p \<mapsto> - -* P))) "
  unfolding sp_def
  apply (clarsimp simp: sp_def)
  apply (intro conjI)
   apply (clarsimp simp: valid_def set_ptr_def bind_def gets_def
                      assert_def get_def return_def modify_def 
                      put_def fail_def
               split: prod.splits if_splits)
   apply (clarsimp simp: sep_conj_def septraction_def pred_neg_def sep_impl_def)
   apply (erule_tac x="y + h'" in allE)
   apply (clarsimp)
   apply (clarsimp simp: sep_disj_fun_def plus_fun_def maps_to_def maps_to_ex_def plus_option_def 
                  split: option.splits)
    apply (erule_tac x=p in allE)
    apply (erule_tac P="Q' ()" in back_subst)
    apply (rule ext)
    apply (clarsimp)
    apply (clarsimp simp: sep_disj_fun_def plus_fun_def maps_to_def maps_to_ex_def plus_option_def 
                   split: option.splits)
   apply (erule_tac x=p in allE)
   apply (fastforce simp: sep_disj_option_def)
  by (simp add:set_ptr_sp')

lemma congE: "P = Q \<Longrightarrow> x = y \<Longrightarrow> P x \<Longrightarrow> Q y"
 by auto

lemma sp_snake_get: "sp (P) (get_ptr p) (\<lambda>rv s. \<exists>v. rv = v \<and> (p \<mapsto> v \<and>* (p \<mapsto> v -* P) ) s) "
  unfolding sp_def
  apply (clarsimp simp: sp_def)
  apply (intro conjI)
   apply (clarsimp simp: valid_def get_ptr_def put_def fail_def
                         bind_def gets_def assert_def get_def return_def modify_def 
                  split: prod.splits if_splits)
   apply (clarsimp simp: sep_conj_def septraction_def pred_neg_def sep_impl_def)
   apply (erule_tac x="y + h'" in allE)
   apply (clarsimp)
   apply (clarsimp simp: sep_disj_fun_def plus_fun_def maps_to_def maps_to_ex_def plus_option_def 
                  split: option.splits)
    apply (erule_tac x=p in allE)
    apply (erule_tac  f1=Q' in congE[OF cong,rotated 3], rule refl )
     apply (clarsimp simp: sep_disj_fun_def plus_fun_def maps_to_def maps_to_ex_def plus_option_def 
                    split: option.splits)
    apply (erule_tac x=p in allE)
    apply (clarsimp simp: sep_disj_option_def split: option.splits)
    apply (rule ext)
    apply (clarsimp simp: sep_disj_fun_def plus_fun_def maps_to_def maps_to_ex_def plus_option_def 
                   split: option.splits)
   apply (erule_tac x=p in allE)
   apply (simp add: option.case_eq_if sep_disj_option_def)
  by (simp add: get_ptr_sp)


lemma sep_disj_positive_fun: "(x + y) p = None \<Longrightarrow> x ## y \<Longrightarrow> x p = None \<and> y p = None"
  apply (clarsimp simp: plus_fun_def sep_disj_fun_def, erule_tac x=p in allE)
  by (metis sep_disj_positive_zero zero_option_def)


lemma fun_upd_sep_add: "(p \<mapsto> v) x \<Longrightarrow> x ## y \<Longrightarrow> y(p \<mapsto> v) = x + y" 
  apply (rule ext, clarsimp simp: maps_to_def)
  by (clarsimp simp: sep_disj_fun_def plus_fun_def
      plus_option_def sep_disj_option_def split: option.splits)

lemma modify_sp: "\<lbrace>P\<rbrace> modify f \<lbrace>\<lambda>_ s. \<exists>s'. P s' \<and> s = f s' \<rbrace>"
 apply (clarsimp simp: modify_def, Det_Monad.wp, fastforce)
done


lemma sp_get: "sp P get (\<lambda>rv s. P s \<and> rv = s)"
 apply (clarsimp simp: sp_def, intro conjI)
 apply (clarsimp simp: get_def valid_def)
  by (simp add: get_def valid_def)


lemma sp_assert: "sp P (assert B) (\<lambda>rv s. P s \<and> B)"
 apply (clarsimp simp: sp_def, intro conjI)
 apply (clarsimp simp: assert_def valid_def return_def split: option.splits)
  by (simp add: assert_sp)

lemma sp_return: "sp P (return x) (\<lambda>rv s. P s \<and> rv = x)"
 apply (clarsimp simp: return_def sp_def valid_def)
done

lemma sp_modify: "sp P (modify f) (\<lambda>rv s. \<exists>s'. P s' \<and> s = f s')"
  apply (clarsimp simp: return_def sp_def valid_def modify_def bind_def get_def put_def)
 by (blast)

lemma sp_subst: "sp P f Q' \<Longrightarrow> Q = Q' \<Longrightarrow> sp P f Q"
 by blast

lemma sp_snake_new: " sp (P) (new_ptr) (\<lambda>rv s. (rv \<mapsto> 0 \<and>* (\<lambda>s. P s \<and> rv = select s)) s) "
  apply (clarsimp simp: sp_def select_def)
  apply (intro conjI)
   apply (clarsimp)
   apply (clarsimp simp: valid_def new_ptr_def bind_def gets_def assert_def get_def
                         return_def modify_def put_def fail_def 
                  split: prod.splits if_splits)
   apply (clarsimp simp: sep_conj_def)
   apply (erule_tac x=y in allE)
   apply (clarsimp)
   apply (elim disjE)
     apply (smt fun_upd_same maps_to_def option.simps(3) option.simps(5) sep_disj_fun_def sep_disj_option_def)
    apply (fastforce)
   apply (erule_tac  f1=Q' in congE[OF cong,rotated 3], rule refl, rule refl )
   apply (erule (1) fun_upd_sep_add)
  apply (clarsimp simp: new_ptr_def )
  apply (sp sp: modify_sp)
  apply (clarsimp)
  apply (clarsimp simp: sep_conj_def)
  apply (rule_tac x="[(SOME p. x p = None) \<mapsto> 0] :: heap" in exI)
  apply (rule_tac x=x in exI)
  apply (clarsimp, intro conjI)
    apply (simp add: sep_disj_fun_def)
   apply (rule fun_upd_sep_add)
    apply (clarsimp simp: maps_to_def)
   apply (simp add: sep_disj_fun_def)
  apply (clarsimp simp: maps_to_def)
  done
 
 

end
