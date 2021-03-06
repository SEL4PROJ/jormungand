theory Total_Forward_Reasoning
imports Extended_Separation_Algebra
        Hoare_Sep_Tactics
        "~~/src/HOL/Library/Monad_Syntax"
begin

type_synonym heap = "nat \<Rightarrow> nat option"
type_synonym machine = "(heap \<times> bool)"

abbreviation "(heap :: machine \<Rightarrow> heap) \<equiv> fst"
abbreviation "(nf :: machine \<Rightarrow> bool) \<equiv> snd"

instantiation "prod" :: (cancellative_sep_algebra, cancellative_sep_algebra)
                         cancellative_sep_algebra
begin
  instance
 apply (intro_classes; clarsimp simp: sep_disj_prod_def plus_prod_def zero_prod_def)
 apply (simp add: sep_disj_positive)
 by (simp add: Extended_Separation_Algebra.cancellative_sep_algebra_class.sep_add_cancel)
end

instantiation "bool" :: cancellative_sep_algebra
begin
instance
 apply (intro_classes; (clarsimp simp: zero_bool_def plus_bool_def sep_disj_bool_def))
  by blast
end


definition maps_to:: "nat \<Rightarrow> nat \<Rightarrow> machine \<Rightarrow> bool" ("_ \<mapsto>u _" [56,51] 56)
  where "x \<mapsto>u y \<equiv> \<lambda>h. heap h = [x \<mapsto> y] \<and> nf h "
  
notation pred_ex  (binder "\<exists>" 10)

definition maps_to_ex :: "nat \<Rightarrow>  machine \<Rightarrow> bool" ("_ \<mapsto>u -" [56] 56)
  where "x \<mapsto>u - \<equiv> (\<lambda>s. \<exists>y. (x \<mapsto>u y) s)"


lemma maps_to_maps_to_ex [elim!]:
  "(p \<mapsto>u v) s \<Longrightarrow> (p \<mapsto>u -) s"
  by (auto simp: maps_to_ex_def)

lemma maps_to_ex_simp[simp]: " (p \<mapsto>u -) ([p \<mapsto> v], True)" 
   by (clarsimp simp: maps_to_ex_def maps_to_def, fastforce)


definition sept (infix "-&" 50) where 
"sept P Q \<equiv> (\<lambda>s. \<exists>h h'. P h \<and> Q h'  \<and>
            (if (nf h \<and> nf s) then 
                 (h + s = h' \<and> h ## s) 
                 else (nf h' \<longrightarrow> ((nf h  \<longrightarrow> h ## h') \<and> (nf s \<longrightarrow> s ## h')))))   "  

 definition sep_con (infix "\<and>&" 50) where 
  "sep_con P Q \<equiv> (\<lambda>s. \<exists>h h'. P h \<and>  Q h' \<and>  (if (nf h \<and> nf h') then ( h' + h = s \<and> h ## h') 
                      else (nf s \<longrightarrow>((nf h \<longrightarrow> h ## s) \<and> (nf h' \<longrightarrow>  s ## h'))))) "  



lemma "(p \<mapsto>u v -& p \<mapsto>u v) s \<Longrightarrow> \<box> s" 
   apply (clarsimp simp: sept_def  maps_to_def zero_prod_def sep_empty_def split: if_splits) 
    apply (drule mp)
    apply (clarsimp simp: sep_disj_prod_def sep_disj_fun_def  sep_disj_option_def split: if_splits option.splits)
   apply (metis )
   apply (clarsimp)
  by (metis Extended_Separation_Algebra.cancellative_sep_algebra_class.sep_add_cancelD disjoint_zero_sym sep_add_commute sep_add_zero_sym sep_disj_commuteI zero_prod_def)



                       
lemma sep_con_commute: "sep_con P Q s \<Longrightarrow> sep_con Q P s" 
   apply (clarsimp simp: sep_con_def)
   apply (rule_tac x="aa" in exI)
   apply (rule_tac x="ba" in exI)
    apply (intro conjI)
   apply (clarsimp)
   apply (rule_tac x="a" in exI)
   apply (rule_tac x="b" in exI)
    apply (intro conjI)
     apply (clarsimp, intro conjI impI)
     using sep_add_commute apply fastforce
   apply (clarsimp simp: sep_disj_commute sep_add_commute)+
  using sep_disj_commuteI by fastforce




definition sep_imp (infix "\<longrightarrow>&" 50) where "sep_imp P Q \<equiv> (not (sept P (not Q)))" 

definition sep_snake where "sep_snake P Q \<equiv> (not ( sep_con P (not Q)))" 
   
lemma sep_mp: "sep_con P (sep_imp P R) s \<Longrightarrow> R s"
  apply (clarsimp simp: sep_con_def sep_imp_def pred_neg_def sept_def )
  apply (erule_tac x=a in allE, erule_tac x=b in allE, simp)
  apply (erule_tac x="fst s" in allE, erule_tac x="snd s" in allE, simp)
  apply (elim disjE; clarsimp?)
  apply (erule notE)
 by (metis prod.collapse sep_add_commute sep_disj_commute)
 

lemma sep_curry: "R s \<Longrightarrow> sep_imp P (sep_con P R) s"
  apply (clarsimp simp: sep_con_def sep_imp_def pred_neg_def sept_def)
   apply (intro conjI; clarsimp)
   apply (erule_tac x=a in allE, erule_tac x=b in allE, simp)
   apply (erule_tac x="fst s" in allE, erule_tac x="snd s" in allE, simp)
   apply (clarsimp simp: sep_add_commute sep_disj_commute)+
  apply (metis (mono_tags, lifting) prod.collapse sep_disj_commuteI)
  apply (rule_tac x=a in exI, rule_tac x=b in exI, clarsimp)
  apply (rule_tac x="fst s" in exI, rule_tac x="snd s" in exI, simp)
  apply (metis (mono_tags, lifting) prod.collapse sep_disj_commuteI)
done


lemma sep_adjoint: "(\<forall>s. sep_con P (sep_imp P R) s \<longrightarrow> R s) \<longleftrightarrow> 
                      (\<forall>s. R s \<longrightarrow> sep_imp P (sep_con P R) s)"
 using Total_Forward_Reasoning.sep_curry Total_Forward_Reasoning.sep_mp by blast

    
lemma sep_con_collapse:"sep_con (p \<mapsto>u v) (R and nf) s \<Longrightarrow> (p \<mapsto>u v \<and>* R) s"
     apply (clarsimp simp: sep_con_def)
     apply (clarsimp simp: sep_conj_def maps_to_def pred_conj_def)
 by (metis sep_add_commute)
   

no_notation NonDetMonad.bind (infixl ">>=" 60)
hide_const NonDetMonad.bind return get put modify gets fail assert state_assert

translations
  "CONST bind_do" == "CONST bind"

no_notation valid ("\<lbrace>_\<rbrace>/ _ /\<lbrace>_\<rbrace>")
no_notation validNF ("\<lbrace>_\<rbrace>/ _ /\<lbrace>_\<rbrace>!")
hide_const valid validNF

type_synonym ('s,'a) det_monad = "'s \<Rightarrow> 'a \<times> 's \<times> bool"

definition
  bind :: "('s,'a) det_monad \<Rightarrow> ('a \<Rightarrow> ('s,'b) det_monad) \<Rightarrow> ('s,'b) det_monad"
where
  "bind f g \<equiv> \<lambda>s. let (r', s', c) = f s; 
                       (r'', s'', c') = g r' s'
                   in (r'', s'', c \<and> c')"

(* use do syntax for this state monad *)
adhoc_overloading
  Monad_Syntax.bind bind 

definition
  "return x \<equiv> \<lambda>s. (x, s, True)"

definition
  "get \<equiv> \<lambda>s. (s, s, True)"

definition
  "put s \<equiv> \<lambda>s'. ((), s, True)"

definition
  "fail \<equiv> \<lambda>s. ((), s, False)"


definition
  "modify f \<equiv> get >>= (\<lambda>x. put (f x))"

definition
  "gets f \<equiv> get >>= (\<lambda>x. return (f x))"

definition
  "assert P \<equiv> if P then return () else fail"

definition
  "state_assert P \<equiv> do { s \<leftarrow> get; assert (P s) }"

definition
  valid :: "('s \<Rightarrow> bool) \<Rightarrow> ('s,'a) det_monad \<Rightarrow> ('a \<Rightarrow> 's \<Rightarrow> bool) \<Rightarrow> bool" 
  ("\<lbrace>_\<rbrace>/ _ /\<lbrace>_\<rbrace>v")
where
  "\<lbrace>P\<rbrace> m \<lbrace>Q\<rbrace>v \<equiv> \<forall>s. P s \<longrightarrow> (let (r',s', c) = m s in c \<longrightarrow> Q r' s')"

definition
  validNF :: "('s \<Rightarrow> bool) \<Rightarrow> ('s,'a) det_monad \<Rightarrow> ('a \<Rightarrow> 's \<Rightarrow> bool) \<Rightarrow> bool" 
  ("\<lbrace>_\<rbrace>/ _ /\<lbrace>_\<rbrace>!")
where
  "\<lbrace>P\<rbrace> m \<lbrace>Q\<rbrace>! \<equiv> \<forall>s. P s \<longrightarrow> (let (r',s', c) = m s in Q r' s' \<and> c)"

definition
  validU :: "(('s \<times> bool)  \<Rightarrow> bool) \<Rightarrow> ('s,'a) det_monad \<Rightarrow> ('a \<Rightarrow> ('s \<times> bool) \<Rightarrow> bool) \<Rightarrow> bool" 
  ("\<lbrace>_\<rbrace>/ _ /\<lbrace>_\<rbrace>u")
where
  "\<lbrace>P\<rbrace> m \<lbrace>Q\<rbrace>u \<equiv> \<forall>s c. P (s, c) \<longrightarrow> (let (r',s',c') = m s in Q r' (s', c \<and> c'))"

lemma bind_wp[wp]:
  "(\<And>x. \<lbrace>B x\<rbrace> g x \<lbrace>C\<rbrace>v) \<Longrightarrow> \<lbrace>A\<rbrace> f \<lbrace>B\<rbrace>v \<Longrightarrow> \<lbrace>A\<rbrace> f >>= g \<lbrace>C\<rbrace>v"
  unfolding valid_def Let_def bind_def by (fastforce split: prod.splits)  

lemma bind_wp_nf:
  "\<lbrace>A\<rbrace> f \<lbrace>B\<rbrace>! \<Longrightarrow> (\<And>x. \<lbrace>B x\<rbrace> g x \<lbrace>C\<rbrace>!) \<Longrightarrow> \<lbrace>A\<rbrace> f >>= g \<lbrace>C\<rbrace>!"
  unfolding validNF_def Let_def bind_def by fastforce

lemma hoare_seq_ext:
  "\<lbrace>A\<rbrace> f \<lbrace>B \<rbrace>u \<Longrightarrow> (\<And>x.\<lbrace>B x\<rbrace> g x \<lbrace>C\<rbrace>u)  \<Longrightarrow> \<lbrace>A\<rbrace> f >>= g \<lbrace>C\<rbrace>u"
  unfolding validU_def Let_def bind_def by fastforce
   
lemma bind_wpU[wp]:
  "(\<And>x.\<lbrace>B x\<rbrace> g x \<lbrace>C\<rbrace>u) \<Longrightarrow> \<lbrace>A\<rbrace> f \<lbrace>B \<rbrace>u \<Longrightarrow> \<lbrace>A\<rbrace> f >>= g \<lbrace>C\<rbrace>u"
  by (rule hoare_seq_ext)

lemma hoare_chain:
  "\<lbrakk> \<lbrace>P\<rbrace> f \<lbrace>Q\<rbrace>v;
    \<And>s. R s \<Longrightarrow> P s;
    \<And>r s. Q r s \<Longrightarrow> S r s \<rbrakk> \<Longrightarrow>
   \<lbrace>R\<rbrace> f \<lbrace>S\<rbrace>v"
  by (fastforce simp: valid_def)

lemma hoare_pre[wp_pre]:
  "\<lbrakk> \<lbrace>P\<rbrace> f \<lbrace>Q\<rbrace>v;
    \<And>s. R s \<Longrightarrow> P s \<rbrakk> \<Longrightarrow>
   \<lbrace>R\<rbrace> f \<lbrace>Q\<rbrace>v"
  by (rule hoare_chain) blast

lemma hoare_chainU:
  "\<lbrakk> \<lbrace>P\<rbrace> f \<lbrace>Q\<rbrace>u;
    \<And>s. R s \<Longrightarrow> P s;
    \<And>r s. Q r s \<Longrightarrow> S r s \<rbrakk> \<Longrightarrow>
   \<lbrace>R\<rbrace> f \<lbrace>S\<rbrace>u"
  by (fastforce simp: validU_def)

lemma hoare_preU[wp_pre]:
  "\<lbrakk> \<lbrace>P\<rbrace> f \<lbrace>Q\<rbrace>u;
    \<And>s. R s \<Longrightarrow> P s \<rbrakk> \<Longrightarrow>
   \<lbrace>R\<rbrace> f \<lbrace>Q\<rbrace>u"
  by (fastforce simp: validU_def)

lemma get_wp[wp]: "\<lbrace>\<lambda>s. P s s\<rbrace> get \<lbrace>P\<rbrace>v"
  by (clarsimp simp: get_def valid_def)
    
lemma put_wp[wp]: "\<lbrace>\<lambda>s'. P () s\<rbrace> put s \<lbrace>P\<rbrace>v"
  by (clarsimp simp: put_def valid_def)
    
lemma fail_wp[wp]: "\<lbrace>\<lambda>s. True\<rbrace> fail \<lbrace>P\<rbrace>v"
  by (simp add: fail_def valid_def)

lemma return_wp[wp]: "\<lbrace>P x\<rbrace> return x \<lbrace>P\<rbrace>v"
  by (simp add: valid_def return_def)

lemma if_wp[wp]:
  "\<lbrakk> Q \<Longrightarrow> \<lbrace>A\<rbrace> f \<lbrace>P\<rbrace>v; \<not>Q \<Longrightarrow> \<lbrace>B\<rbrace> g \<lbrace>P\<rbrace>v\<rbrakk> \<Longrightarrow>
  \<lbrace>\<lambda>s. (Q \<longrightarrow> A s) \<and> (\<not>Q \<longrightarrow> B s)\<rbrace> if Q then f else g \<lbrace>P\<rbrace>v"
  by auto

(* partial ignores asserts *)
lemma assert_wp[wp]:
  "\<lbrace>\<lambda>s. Q \<longrightarrow> P () s\<rbrace> assert Q \<lbrace>P\<rbrace>v"
  unfolding assert_def by wp auto

lemma state_assert_wp[wp]:
  "\<lbrace>\<lambda>s. Q s \<longrightarrow> P () s\<rbrace> state_assert Q \<lbrace>P\<rbrace>v"
  unfolding state_assert_def by wp

lemma modify_wp[wp]:
  "\<lbrace>\<lambda>s. P () (f s)\<rbrace> modify f \<lbrace>P\<rbrace>v"
  unfolding modify_def by wpsimp


lemma get_wpU[wp]: "\<lbrace>\<lambda>s. P (fst s) s \<rbrace> get \<lbrace> P \<rbrace>u"
  by (clarsimp simp: get_def validU_def)
    
lemma put_wpU[wp]: "\<lbrace>\<lambda>s'. P () (s, snd s') \<rbrace> put s \<lbrace> P \<rbrace>u"
  by (clarsimp simp: put_def validU_def)
    
lemma fail_wpU[wp]: "\<lbrace>\<lambda>s. P () (fst s, False) \<rbrace> fail \<lbrace> P \<rbrace>u"
  by (simp add: fail_def validU_def)

lemma return_wpU[wp]: "\<lbrace>P x\<rbrace> return x \<lbrace>P\<rbrace>u"
  by (simp add: validU_def return_def)

lemma if_wpU[wp]:
  "\<lbrakk> Q \<Longrightarrow> \<lbrace>A\<rbrace> f \<lbrace>P\<rbrace>u; \<not>Q \<Longrightarrow> \<lbrace>B\<rbrace> g \<lbrace>P\<rbrace>u\<rbrakk> \<Longrightarrow>
  \<lbrace>\<lambda>s. (Q \<longrightarrow> A s) \<and> (\<not>Q \<longrightarrow> B s)\<rbrace> if Q then f else g \<lbrace>P\<rbrace>u"
  by auto

lemma assert_wpU[wp]:
  "\<lbrace>\<lambda>s. P () (fst s, Q \<and> snd s) \<rbrace> assert Q \<lbrace> P \<rbrace>u"
  unfolding assert_def by wp auto

lemma state_assert_wpU[wp]:
  "\<lbrace>\<lambda>s.  P () (fst s, Q (fst s) \<and> snd s) \<rbrace> state_assert Q \<lbrace> P \<rbrace>u"
  unfolding state_assert_def by wpsimp

lemma modify_wpU[wp]:
  "\<lbrace>\<lambda>s. P ()  (f (fst s), snd s)\<rbrace> modify f \<lbrace>P\<rbrace>u"
  unfolding modify_def by wpsimp

definition
  "delete_ptr p = do {
    state_assert (\<lambda>s.  s p \<noteq> None); 
    modify (\<lambda>s. (\<lambda>p'. if p = p' then None else s p'))
  }"

lemma delete_ptr_sp:"\<lbrace>R\<rbrace> delete_ptr p  \<lbrace>\<lambda>_. (sept (p \<mapsto>u -) R) \<rbrace>u"
 apply (clarsimp simp: delete_ptr_def)
 apply (rule hoare_seq_ext[rotated])
 apply (rule modify_wpU)
 apply (rule hoare_chainU[OF state_assert_wpU, rotated])
 apply (assumption)
 apply (clarsimp) 
 apply (case_tac "a p = 0"; clarsimp simp: zero_option_def sept_def)
 apply (rule_tac x=" [p \<mapsto> undefined]" in exI)
 apply (rule_tac x=" True" in exI)
 apply (intro conjI, fastforce)
 apply (rule_tac x=a in exI, rule_tac x=b in exI)
 apply (clarsimp)
 apply (clarsimp simp: sep_disj_prod_def sep_disj_fun_def sep_disj_option_def sep_disj_bool_def)
 apply (case_tac "b"; clarsimp)
  apply (rule_tac x="[p \<mapsto> y]" in exI)   
  apply (rule_tac x="True" in exI)    
 apply (intro conjI, fastforce)
 apply (clarsimp)
apply (rule_tac x=a in exI, rule_tac x=True in exI)
apply (clarsimp, intro conjI)
apply (clarsimp simp: plus_prod_def, intro conjI)
apply (rule ext)
apply (clarsimp simp: plus_fun_def plus_option_def)
apply (clarsimp simp: plus_bool_def)
 apply (clarsimp simp: sep_disj_prod_def sep_disj_fun_def sep_disj_option_def sep_disj_bool_def)
   apply (rule_tac x="[p \<mapsto> y]" in exI)
   apply (rule_tac x="True" in exI)
apply (intro conjI, fastforce)
 by blast

definition "the_f v d = (if (v = None) then d else (the v))"

lemma gets_wpU: "\<lbrace>\<lambda>s.  P (f (fst s)) s \<rbrace> gets f \<lbrace> P \<rbrace>u"
   by (clarsimp simp: gets_def get_def bind_def validU_def return_def)

definition
  "get_ptr p = do { 
     v <- gets (\<lambda>s. s p);
     assert (v \<noteq> None);
     return (the_f v (0))
   }"

lemma [simp]: "(p \<mapsto>u y) h = (h = ([p \<mapsto> y], True))" 
  by (metis (mono_tags, lifting) fst_conv maps_to_def prod_eqI snd_conv)

lemma get_ptr_sp: "\<lbrace>R\<rbrace> get_ptr p \<lbrace>\<lambda>rv. (p \<mapsto>u rv \<and>& (p \<mapsto>u rv -& R))\<rbrace>u"
  apply (clarsimp simp: get_ptr_def, (rule hoare_seq_ext[rotated])+)
  apply (rule return_wpU assert_wpU)+
  apply (rule hoare_chainU[OF gets_wpU, rotated]) 
  apply (assumption)
  apply (clarsimp simp: gets_def validU_def)
  apply (case_tac "(\<exists>y. a p = Some y)"; clarsimp simp: the_f_def  zero_option_def)
  apply (clarsimp simp: sep_con_def)
  apply (rule_tac x="(\<lambda>ptr. if ptr = p then None else  a ptr)" in exI)
  apply (rule_tac x="b" in exI)
  apply (clarsimp, intro conjI impI)
  apply (clarsimp simp: sept_def)
  apply (rule_tac x=a in exI, rule_tac x=b in exI, clarsimp, intro conjI)
  apply (clarsimp simp: plus_prod_def plus_bool_def)
  apply (rule ext, clarsimp simp: plus_fun_def plus_option_def)
  apply (clarsimp simp: sep_disj_prod_def sep_disj_fun_def sep_disj_option_def sep_disj_bool_def)
  apply (clarsimp simp: plus_prod_def plus_bool_def)
  apply (rule ext, clarsimp simp: plus_fun_def plus_option_def split: option.splits)
  apply (clarsimp simp: sep_disj_prod_def sep_disj_fun_def sep_disj_option_def sep_disj_bool_def)
  apply (clarsimp simp: sept_def)
  apply (blast)
  apply (clarsimp simp: sep_con_def)
  apply (rule_tac x="(\<lambda>ptr. if ptr = p then None else  a ptr)" in exI, rule_tac x= False in exI)
  apply (clarsimp)
  apply (clarsimp simp: sept_def)
  apply (rule_tac x=a in exI)
  apply (rule_tac x=b in exI)
  apply (clarsimp simp: sep_disj_prod_def sep_disj_fun_def sep_disj_option_def sep_disj_bool_def)
done

definition
  "set_ptr p v = do {
     x <- gets (\<lambda>s. s p);
     assert (x \<noteq> None);
     modify (\<lambda>s. s(p \<mapsto> v))
   }"

lemma set_ptr_sp: "\<lbrace>R\<rbrace> set_ptr p v \<lbrace>\<lambda>_. (p \<mapsto>u v \<and>& (p \<mapsto>u - -& R))\<rbrace>u" 
  apply (clarsimp simp: set_ptr_def, (rule hoare_seq_ext[rotated])+)
  apply (rule return_wpU assert_wpU modify_wpU)+
  apply (rule hoare_chainU[OF gets_wpU, rotated]) 
  apply (assumption)
  apply (clarsimp simp: gets_def validU_def)
  apply (case_tac "(\<exists>y. a p = Some y)"; clarsimp simp: the_f_def maps_to_ex_def zero_option_def)
  apply (clarsimp simp: sep_con_def)
  apply (rule_tac x="(\<lambda>ptr. if ptr = p then None else  a ptr)" in exI)
  apply (rule_tac x="b" in exI)
  apply (clarsimp, intro conjI impI)
  apply (clarsimp simp: sept_def)
  apply (rule_tac x="[p \<mapsto> y]" in exI, intro conjI, fastforce)
  apply (rule_tac x=b in exI, clarsimp)
  apply (rule exI, rule exI, intro conjI, fastforce)
  apply (clarsimp simp: plus_prod_def plus_bool_def)
  apply (rule ext, clarsimp simp: plus_fun_def plus_option_def)
  apply (clarsimp simp: sep_disj_prod_def sep_disj_fun_def sep_disj_option_def sep_disj_bool_def)
  apply (clarsimp simp: plus_prod_def plus_bool_def)
  apply (rule ext, clarsimp simp: plus_fun_def plus_option_def split: option.splits)
  apply (clarsimp simp: sep_disj_prod_def sep_disj_fun_def sep_disj_option_def sep_disj_bool_def)
  apply (clarsimp simp: sept_def)
  apply (blast)
  apply (clarsimp simp: sep_con_def)
  apply (rule_tac x="(\<lambda>ptr. if ptr = p then Some v else  a ptr)" in exI, rule_tac x= False in exI)
  apply (clarsimp)
  apply (clarsimp simp: sept_def)
  apply (rule_tac x="[p \<mapsto> undefined]" in exI)
apply (rule conjI)
apply (fastforce)
  apply (rule_tac x=True in exI)
  apply (clarsimp simp: sep_disj_prod_def sep_disj_fun_def sep_disj_option_def sep_disj_bool_def)
apply (blast)
done


definition "move_ptr p p' = get_ptr p >>= set_ptr p'" 


lemma sep_con_impl2: "(p \<and>& q) s \<Longrightarrow> (\<And>s. q s \<Longrightarrow> q' s) \<Longrightarrow> (p \<and>& q') s"
  apply (clarsimp simp: sep_con_def)
  apply (rule_tac x=a in exI, rule_tac x=b in exI)
  apply (clarsimp)
  apply (rule_tac x=aa in exI, rule_tac x=ba in exI, clarsimp)
  by auto

lemma sept_impl2: "(p -& q) s \<Longrightarrow> (\<And>s. q s \<Longrightarrow> q' s) \<Longrightarrow> (p -& q') s"
  apply (clarsimp simp: sept_def)
  apply (fastforce)
done 

lemma sept_success:"( p \<mapsto>u v -& (p \<mapsto>u v' \<and>* (R and nf))) s \<Longrightarrow> (R and (\<lambda>s. nf s \<and> v = v')) s" 
  apply (clarsimp simp: sept_def sep_conj_def maps_to_ex_def split: if_splits)
  apply (erule disjE, clarsimp simp: pred_conj_def)
  apply (subgoal_tac "v = v'", clarsimp)
  apply (metis Extended_Separation_Algebra.cancellative_sep_algebra_class.sep_add_cancelD sep_add_commute sep_disj_commuteI) 
  apply (clarsimp simp: plus_prod_def)
apply (drule fun_cong[where x=p], clarsimp simp: plus_fun_def plus_option_def split: option.splits)
apply (clarsimp simp: sep_disj_fun_def sep_disj_prod_def sep_disj_option_def split: if_splits, fastforce)
apply (clarsimp simp: pred_conj_def plus_prod_def) 
apply (clarsimp simp: plus_fun_def plus_option_def sep_disj_fun_def sep_disj_prod_def sep_disj_option_def plus_bool_def sep_disj_bool_def split: if_splits)
apply (fastforce)
done


lemma sept_success_ex:"( p \<mapsto>u - -& (p \<mapsto>u - \<and>* (R and nf))) s \<Longrightarrow> (R and (nf)) s"
apply (clarsimp simp: sept_def sep_conj_def maps_to_ex_def split: if_splits)
  apply (erule disjE, clarsimp simp: pred_conj_def)
  apply (subgoal_tac "y = ya", clarsimp)
  apply (metis Extended_Separation_Algebra.cancellative_sep_algebra_class.sep_add_cancelD sep_add_commute sep_disj_commuteI) 
  apply (clarsimp simp: plus_prod_def)
apply (drule fun_cong[where x=p], clarsimp simp: plus_fun_def plus_option_def split: option.splits)
apply (clarsimp simp: plus_fun_def plus_option_def sep_disj_fun_def sep_disj_prod_def sep_disj_option_def plus_bool_def sep_disj_bool_def split: if_splits)
apply (fastforce)
apply (clarsimp simp: plus_fun_def plus_prod_def plus_option_def sep_disj_fun_def sep_disj_prod_def sep_disj_option_def plus_bool_def sep_disj_bool_def split: if_splits)
apply (fastforce)
done


lemma sep_maps_to_success: "(p \<mapsto>u v \<and>* R) s \<Longrightarrow> (\<And>s. R s \<Longrightarrow> nf s) \<Longrightarrow> ((p \<mapsto>u v \<and>* R) and nf) s"
  apply (clarsimp simp: sep_conj_def pred_conj_def)
  by (simp add: plus_prod_def plus_bool_def)

lemma maps_to_nf: "(p \<mapsto>u v) s \<Longrightarrow> ((p \<mapsto>u v) and nf) s" 
by (clarsimp simp: pred_conj_def maps_to_def)

lemma maps_to_ex_nf: "(p \<mapsto>u -) s \<Longrightarrow> ((p \<mapsto>u -) and nf) s" 
by (clarsimp simp: pred_conj_def maps_to_ex_def maps_to_def)


lemma move_ptr_validU:"\<lbrace>(p \<mapsto>u v \<and>* p' \<mapsto>u -)\<rbrace> move_ptr p p' \<lbrace>\<lambda>_. (p \<mapsto>u v \<and>* p' \<mapsto>u v)\<rbrace>u"
  apply (clarsimp simp: move_ptr_def, rule hoare_seq_ext)
apply (rule hoare_chainU, rule get_ptr_sp, assumption, assumption)
  apply (rule hoare_chainU[OF set_ptr_sp])
 apply (assumption) 
   apply (subgoal_tac "x=v", clarsimp)
  apply (drule sep_con_impl2) 
  apply (drule sept_impl2)
  apply (drule sep_con_impl2)
    apply (drule sept_impl2)
    apply (sep_drule maps_to_ex_nf[where p=p'])
    apply (sep_select_asm 2, assumption)
 apply (drule sept_success, assumption+)
 apply (drule sep_con_impl2)
 apply (drule sept_impl2)
apply (rule sep_con_collapse[where p=p and R="p' \<mapsto>u -"])
 apply (erule sep_con_impl2)
 apply (clarsimp simp: pred_conj_def)
 apply (drule sept_impl2)
apply (sep_drule maps_to_nf)
 apply (sep_select_asm 2, assumption)
apply (drule sept_success_ex, assumption)
apply (drule sep_con_collapse, sep_solve)
  apply (drule sep_con_impl2)
  apply (drule sept_impl2)
  apply (drule sep_con_impl2)
    apply (drule sept_impl2)
    apply (sep_drule maps_to_ex_nf[where p=p'])
    apply (sep_select_asm 2, assumption)
 apply (drule sept_success, assumption+)
apply (clarsimp simp: pred_conj_def sep_con_def sept_def)
done



lemma "\<exists>s. (nf -& nf) s \<and> \<not>nf s"
 apply (rule_tac x="(undefined,False)" in exI)
 apply (clarsimp simp: sept_def)
 apply (rule_tac x="[p \<mapsto> v]" in exI)
 apply (rule_tac x=True in exI)
 apply (clarsimp)
apply (rule_tac x=0 in exI)
 apply (rule_tac x= True in exI)
 apply (clarsimp)
apply (clarsimp simp: sep_disj_prod_def sep_disj_bool_def)
done

abbreviation "NULL \<equiv> (0 :: nat)"

definition
  "new_ptr = do {
     s <- get; 
     p <- return (if (\<exists>x. s x = 0) then (SOME x. s x = 0) else NULL );
     _ <- if (p = NULL) then (return ()) else modify (\<lambda>s. s(p \<mapsto> undefined));
     return (p)
   }"

lemma new_ptr_sp: "\<lbrace>R\<rbrace> new_ptr \<lbrace>\<lambda>rv s. if (rv = NULL) then R s else (rv \<mapsto>u - \<and>* R) s\<rbrace>u"
  apply (clarsimp simp: new_ptr_def)
  apply (wp)
  apply (clarsimp)
  apply (clarsimp simp: sep_conj_def)
  apply (rule_tac x="[(SOME x. a x = 0) \<mapsto> undefined]" in exI)
  apply (rule_tac x=True in exI)
  apply (rule_tac x=a in exI)
  apply (rule_tac x=b in exI)
  apply (clarsimp, intro conjI)
  apply (clarsimp simp: sep_disj_prod_def sep_disj_fun_def zero_fun_def zero_option_def)
  apply (safe)
  apply (clarsimp simp: sep_disj_prod_def sep_disj_fun_def zero_fun_def sep_disj_option_def zero_option_def)
  apply (meson tfl_some) 
 apply (clarsimp simp: sep_disj_prod_def sep_disj_fun_def zero_fun_def sep_disj_option_def zero_option_def)
 apply (clarsimp simp: sep_disj_bool_def)
apply (clarsimp simp: plus_prod_def plus_bool_def)
  apply (rule ext)  
  apply (clarsimp)
  apply (safe)
  apply (clarsimp simp: plus_fun_def plus_option_def zero_option_def)
  using case_option_over_if(2) tfl_some apply auto[1]
apply (clarsimp simp: plus_fun_def plus_option_def)
done
 



end