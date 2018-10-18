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
 Unified Correctness reasoning in Separation Logic. Defines a
 concrete model of type (heap x bool) as an early extension
 of SL to deal with failure.
*)

theory Failure_Model
imports
  "Extended_Separation_Algebra"
  "Hoare_Sep_Tactics"
  "Sep_Forward"
  "Det_Monad"
begin

instantiation "nat" ::  cancellative_sep_algebra
begin
 definition "sep_disj_nat (x :: nat) (y :: nat) \<equiv> x = 0 \<or> y = 0"
instance
 apply (standard; clarsimp simp: sep_disj_nat_def )
  by linarith
end

instantiation "int" ::  cancellative_sep_algebra
begin
 definition "sep_disj_int (x :: int) (y :: int) \<equiv> x = 0 \<or> y = 0"
instance
 apply (standard; clarsimp simp: sep_disj_int_def )
  by linarith
end

instantiation "list" :: (type) cancellative_sep_algebra
begin
 definition "zero_list \<equiv> []"
 definition "plus_list x y \<equiv> x@y"
 definition "sep_disj_list (x :: 'a list) (y :: 'a list) \<equiv>  x = [] \<or> y = []" 
instance
   apply (intro_classes; clarsimp simp: sep_disj_list_def zero_list_def plus_list_def)  
   by auto
end


instantiation "prod" :: (cancellative_sep_algebra, cancellative_sep_algebra)
                         cancellative_sep_algebra
begin
instance
  apply (intro_classes; clarsimp simp: sep_disj_prod_def plus_prod_def zero_prod_def)
  apply (simp add: sep_disj_positive)
  by (simp add: sep_add_cancel)
end

instantiation "bool" :: cancellative_sep_algebra
begin
instance
  by (intro_classes) (auto simp: zero_bool_def plus_bool_def sep_disj_bool_def)
end

type_synonym ('a, 'b) abstract_heap = "('a \<Rightarrow> 'b option) "
type_synonym ('a, 'b) abstract_ext = "('a, 'b) abstract_heap \<times> ('a, 'b) abstract_heap  "

definition
  maps_to:: "'a \<Rightarrow> 'b \<Rightarrow> ('a, 'b) abstract_ext \<Rightarrow> bool" ("_ \<mapsto>u _" [56,51] 56)
where
  "x \<mapsto>u y \<equiv> \<lambda>h. h = ([x \<mapsto> y], 0) "

definition
  maps_to_ex :: "'a \<Rightarrow>  ('a, 'b) abstract_ext \<Rightarrow> bool" ("_ \<mapsto>u -" [56] 56)
where
  "x \<mapsto>u - \<equiv> (\<lambda>s. \<exists>y. (x \<mapsto>u y) s)"

instantiation option :: (type) minus begin
 definition "minus_option (x :: 'a option) (y :: 'a option) \<equiv> if y = 0 then x else 0"
 instance by standard 

 lemma minus_option_simp[simp]:  "(x :: 'a option) - 0 = x" 
  by (clarsimp simp: zero_option_def minus_option_def)

 lemma minus_option_simp'[simp]:  "0 - (x :: 'a option) = 0" 
  by (clarsimp simp: zero_option_def minus_option_def)
 
 lemma minus_some_simp: "Some x - y = 0 \<longleftrightarrow> y \<noteq> 0"
 by (clarsimp simp: minus_option_def zero_option_def)

 lemma minus_some_some_simp[simp]: "Some x - Some y = 0"
 by (clarsimp simp: minus_option_def zero_option_def)

 lemmas minus_option_none_simp[simp] = minus_option_simp[simplified zero_option_def]
                                       minus_option_simp'[simplified zero_option_def]

 lemma plus_option_simp[simp]: " x + None = x" 
   by (clarsimp simp: plus_option_def split: option.splits)

 lemma plus_option_simp'[simp]: " None + x = x" 
   by (clarsimp simp: plus_option_def split: option.splits)
 
end

definition "sep_minus x y = ((fst x - fst y) + (snd y - snd x),
                             (snd x - snd y) + (fst y - fst x))"

type_synonym ('a, 'b) abstract_ext' = "('a, 'b) abstract_heap \<times> ('a, 'b) abstract_heap  "

class compossible =
  fixes compossible :: "'a => 'a => bool" (infix "&&" 60)
  assumes compossible_commute: "x && y \<longleftrightarrow> y && x"
  assumes compossible_refl[simp]: "x && x"


instantiation option :: (type) compossible begin
 definition "compossible_option (x :: 'a option) y \<equiv> x \<preceq> y \<or> y \<preceq> x"
instance
 apply (standard; clarsimp simp: compossible_option_def)
 apply (rule iffI)
 apply (clarsimp)
 apply (clarsimp)
 apply (clarsimp simp: sep_substate_def, rule_tac x=0 in exI, clarsimp)
done
end

instantiation "fun" :: (type, compossible) compossible begin
 definition "compossible_fun (f :: 'a \<Rightarrow> 'b) g \<equiv> \<forall>v. f v && g v "
instance
 apply (standard; clarsimp simp: compossible_fun_def)
 by (rule iffI; fastforce simp: compossible_commute)
end

instantiation "prod" :: (compossible, compossible) compossible begin
 definition "compossible_prod s s' \<equiv>  fst s && fst s' \<and> snd s && snd s' "
instance
 apply (standard; clarsimp simp: compossible_prod_def)
 by (rule iffI; fastforce simp: compossible_commute)
end


(* definition "sdisj x y \<equiv> (\<forall>v. ordered ((fst x - fst y) v) ((snd y - snd x) v)) \<and>
                         (\<forall>v. ordered ((snd x - snd y) v) ((fst y - fst x) v))  "

*)

notation sep_minus (infix "-" 40)

definition "sept P Q \<equiv> \<lambda>s. \<exists>h h'. P h \<and> Q h' \<and>  h && h' \<and> s = sep_minus h' h"  

definition "snake P Q \<equiv> \<lambda>s. \<forall>h h'. P h \<longrightarrow> s && h \<longrightarrow> h' = sep_minus s h \<longrightarrow> Q h'"  

definition "star P Q \<equiv> not (snake P (not Q))"  

definition "wand P Q \<equiv> not (sept P (not Q))"  

lemma star_def': "star P Q = (\<lambda>s. \<exists>h. P h \<and> Q (s - h) \<and> s && h)"
 apply (clarsimp simp: star_def snake_def fun_Compl_def pred_neg_def)
 by metis

lemma wand_def': "wand P Q = (\<lambda>s. \<forall>h h'. P h \<longrightarrow>  h' && h \<longrightarrow> s = sep_minus h' h \<longrightarrow> Q h')"
 apply (clarsimp simp: pred_neg_def star_def wand_def sept_def snake_def fun_Compl_def)
 apply (rule ext, rule iffI; clarsimp)
 apply (erule allE, erule allE, drule (1) mp)
 apply (erule_tac x=ab in allE , erule_tac x=bb in allE, drule  mp)
  apply (metis compossible_commute)
 apply (erule disjE; metis)
  using compossible_commute by blast

notation snake (infix "\<leadsto>o" 24)

notation sept (infix "-o" 25)

notation wand (infix "\<longrightarrow>o" 24)

notation star (infix "\<circle>" 25)



lemma sept_snake_gal: "(\<And>s.  (P -o Q) s \<Longrightarrow> R s) \<Longrightarrow> Q s \<Longrightarrow>  (P \<leadsto>o R) s" 
  apply (unfold snake_def) 
  apply (safe)
  apply (atomize)
  apply (erule_tac x="fst (s - (a,b))" in allE)
  apply (erule_tac x="snd (s - (a,b))" in allE)
  apply (unfold sept_def)
  apply (safe)
  using compossible_commute prod.collapse apply blast
  by (metis prod.collapse)


lemma star_wand_gal: "(\<And>s. (P \<circle> Q) s \<Longrightarrow> R s) \<Longrightarrow> Q s \<Longrightarrow>  (P \<longrightarrow>o R) s" 
  apply (unfold  wand_def sept_def pred_neg_def) 
  apply (atomize)
  apply (clarify)
  apply (erule_tac x="(aa, ba)" in allE)
  apply (clarify)
  apply (clarsimp simp: star_def snake_def pred_neg_def)
  apply (erule_tac x="a" in allE)
  apply (erule_tac x="b" in allE)
  apply (clarsimp)
  using compossible_commute by blast


lemma snake_sept_gal: "(\<And>s. Q s \<Longrightarrow> (P \<leadsto>o R) s) \<Longrightarrow> (P -o Q) s \<Longrightarrow> R s" 
  apply (clarsimp simp:  sept_def) 
  apply (atomize)
  apply (erule_tac x="aa" in allE)
  apply (erule_tac x="ba" in allE)
  apply (clarsimp)
  apply (clarsimp simp: snake_def)
  apply (erule_tac x=a in allE)
  apply (erule_tac x=b in allE)
 apply (clarsimp)
  using compossible_commute by blast


lemma [simp]: "\<not>Some x ## Some y" by (clarsimp simp: sep_disj_option_def) 


lemma minus_eq_zero[simp]: "x - x = (0 :: 'a \<Rightarrow> 'b option)" 
 by (rule ext, clarsimp simp: fun_diff_def minus_option_def zero_fun_def)




definition "maps_to' p v \<equiv> \<lambda>s. s = ([p \<mapsto> v], 0)" 

lemma minus_zero[simp]: "x - 0 = (x :: ('a, 'b) abstract_heap)" 
 by (clarsimp simp: fun_diff_def zero_fun_def)

lemma zero_minus[simp]: "0 - x = (0 :: ('a, 'b) abstract_heap)" 
 by (clarsimp simp: fun_diff_def zero_fun_def)

lemma zero_le[simp]: "0 \<preceq> x"
  apply (clarsimp simp: sep_substate_def)
done

term "p \<mapsto>u v"

lemma septraction_maps_to_minus_heaplet: 
  " (p \<mapsto>u v -o (p \<mapsto>u v)) (s :: ('a, 'b) abstract_ext) \<Longrightarrow> \<box> s"
  apply (clarsimp simp: sept_def maps_to_def sep_minus_def zero_fun_def sep_empty_def)
  apply (clarsimp simp: prod_eq_iff) 
  apply (clarsimp simp: plus_fun_def zero_prod_def zero_fun_def)
done

lemma septraction_empty_minus: " (\<box> -o R) (s :: ('a, 'b) abstract_ext) \<Longrightarrow> R s"
  apply (clarsimp simp: sept_def maps_to_def sep_minus_def zero_fun_def sep_empty_def)
  apply (clarsimp simp: prod_eq_iff) 
  apply (clarsimp simp: plus_fun_def zero_prod_def zero_fun_def)
done

lemma septraction_maps_to_empty:" (maps_to p v -o \<box>) (s :: ('a, 'b) abstract_ext) 
    \<Longrightarrow> (maps_to p v) (snd s, fst s)"
  apply (clarsimp simp: sept_def maps_to_def sep_minus_def zero_fun_def sep_empty_def)
  apply (clarsimp simp: prod_eq_iff) 
  apply (clarsimp simp: plus_fun_def zero_prod_def zero_fun_def)
  apply (rule ext, clarsimp)
done

lemma " ( p \<mapsto>u v -o (\<lambda>s. s = ([p \<mapsto> v], [p \<mapsto> v]))) (s :: ('a, 'b) abstract_ext) 
    \<Longrightarrow> (p \<mapsto>u v) (snd s, fst s)" 
  apply (clarsimp simp: sept_def maps_to_def sep_minus_def zero_fun_def sep_empty_def)
  apply (clarsimp simp: prod_eq_iff) 
  apply (clarsimp simp: plus_fun_def zero_prod_def zero_fun_def)
  apply (rule ext, clarsimp)
done

lemma septraction_fail_maps_to:
        " (p \<mapsto>u v -o (\<lambda>s. s = (0, [p \<mapsto> v]))) (s :: ('a, 'b) abstract_ext) 
    \<Longrightarrow> (p \<mapsto>u v) (snd s, fst s)" 
  apply (clarsimp simp: sept_def maps_to_def)
  apply (clarsimp simp:  maps_to'_def sep_minus_def zero_fun_def sep_empty_def)
  apply (clarsimp simp: prod_eq_iff) 
  apply (clarsimp simp: plus_fun_def zero_prod_def zero_fun_def)
  apply (rule ext, clarsimp simp: plus_option_def)
done

definition
  "delete_ptr p = do {
    state_assert (\<lambda>s.  s p \<noteq> None);
    modify (\<lambda>s. (\<lambda>p'. if p = p' then None else s p'))
  }"

definition to_flag :: "('a \<times> ('a :: zero)) \<Rightarrow> ('a \<times> bool) \<Rightarrow> bool"
where
"to_flag h h' \<equiv> ( (fst h = fst h') \<and> snd h' = (snd h = 0))  " 

definition "project P \<equiv> \<lambda>s. \<exists>s'. P s' \<and> to_flag s' s"

notation project ("<_>")


lemma projectE: "project P s \<Longrightarrow> (\<And>s. P s \<Longrightarrow> Q s) \<Longrightarrow> project Q s"
 apply (clarsimp simp: project_def, fastforce)
done

lemma [simp]: "[p \<mapsto> x] \<noteq> 0"
  by (clarsimp simp: zero_fun_def zero_option_def)

lemma [simp]: " None \<preceq> x" 
 by (subst zero_option_def[symmetric], clarsimp )

lemma [simp]: "x \<preceq> x"
 by (clarsimp simp: sep_substate_def, rule_tac x=0 in exI, clarsimp)

lemma [simp]: "None = Some y - Some y"
  by (clarsimp simp: minus_option_def zero_option_def)

lemma [simp]:"Some y - Some x = None" 
  by (clarsimp simp: minus_option_def zero_option_def) 

lemma [simp]: "Some y + Some y = Some y" 
  by (clarsimp simp: plus_option_def)

lemma [simp]: "Some x && Some y \<longleftrightarrow> x = y"
 apply (clarsimp simp: compossible_option_def sep_substate_def, rule iffI)
 apply (elim disjE; clarsimp simp: plus_option_def)
 apply (clarsimp)
  using sep_disj_zero by fastforce

lemma [simp]: "x + y = 0 \<longleftrightarrow> x = 0 \<and> y = (0 :: ('a, 'b) abstract_heap)"
 apply (rule iffI, rule conjI)
 apply (rule ext, drule_tac x=xa in fun_cong)
 apply (clarsimp simp: zero_fun_def plus_fun_def zero_option_def 
  plus_option_def split: option.splits)
 apply (rule ext, drule_tac x=xa in fun_cong)
 apply (clarsimp simp: zero_fun_def plus_fun_def zero_option_def 
  plus_option_def split: option.splits)
 by (clarsimp)

lemma delete_ptr_spU:
  "\<lbrace><R>\<rbrace> delete_ptr p  \<lbrace>\<lambda>_. < ( p \<mapsto>u - -o R )> \<rbrace>u" 
  apply (clarsimp simp: delete_ptr_def)
  apply (rule hoare_seq_extU[rotated])
   apply (rule modify_wpU)
  apply (rule hoare_chainU[OF state_assert_wpU, rotated])
   apply (assumption)
  apply (clarsimp) 
  apply (clarsimp simp: project_def to_flag_def)
  apply (case_tac "a p = None"; case_tac "ba p = None" )
     apply (rule_tac x="ba + [p \<mapsto> undefined] " in exI)
     apply (intro conjI)
      apply (clarsimp simp: sept_def)
      apply (rule_tac x="[p \<mapsto> undefined]" in exI)
      apply (rule_tac x="0" in exI)
      apply (intro conjI)
       apply (clarsimp simp: maps_to_ex_def maps_to_def, fastforce)
      apply (rule exI, rule exI, intro conjI, assumption)
       apply (clarsimp simp:  zero_fun_def compossible_prod_def compossible_fun_def compossible_option_def)
      apply (clarsimp simp: sep_minus_def)
      apply (intro conjI ext; clarsimp?)
      apply (clarsimp simp: plus_fun_def)
     apply (rule iffI; clarsimp)
    apply (rule_tac x=ba in exI)
    apply (clarsimp simp: sept_def, intro conjI)
     apply (rule_tac x="[p \<mapsto> y]" in exI)
     apply (rule_tac x=0 in exI)
     apply (intro conjI; clarsimp?)
      apply (fastforce simp: maps_to_ex_def maps_to_def)
     apply (rule exI, rule exI, intro conjI, assumption)
      apply (clarsimp simp: zero_fun_def compossible_prod_def compossible_fun_def compossible_option_def)
     apply (clarsimp simp: sep_minus_def, intro conjI ext; clarsimp?)
     apply (clarsimp simp: plus_fun_def)
    apply (clarsimp simp: zero_fun_def zero_option_def)
   apply (clarsimp)
   apply (rule_tac x=ba in exI)
   apply (clarsimp simp: sept_def)
   apply (rule_tac x="[p \<mapsto> y]" in exI)
   apply (rule_tac x="0" in exI)
   apply (intro conjI, fastforce simp: maps_to_ex_def maps_to_def)
   apply (rule_tac x=a in exI)
   apply (rule_tac x=ba in exI)
   apply (clarsimp, intro conjI)
    apply (clarsimp simp: zero_fun_def compossible_prod_def compossible_fun_def compossible_option_def)
   apply (clarsimp simp: sep_minus_def, intro conjI ext; (clarsimp simp: zero_option_def)?)
   apply (clarsimp simp: plus_fun_def)
  apply (rule_tac x=ba in exI, simp)
  apply (clarsimp simp: sept_def)
  apply (rule_tac x="[p \<mapsto> y]" in exI)
  apply (rule_tac x=0 in exI)
  apply (intro conjI)
   apply (fastforce simp: maps_to_ex_def maps_to_def)
  apply (rule_tac x=a in exI, rule_tac x=ba in exI)
  apply (clarsimp)
  apply (intro conjI)
   apply (clarsimp simp: compossible_prod_def compossible_fun_def compossible_option_def)
   apply (clarsimp simp:  zero_fun_def)
  apply (clarsimp simp: sep_minus_def, intro conjI ext; (clarsimp simp: zero_option_def)?)
  apply (clarsimp simp: plus_fun_def)
  done

definition
  "set_ptr p v = do {
    state_assert (\<lambda>s.  s p \<noteq> None);
    modify (\<lambda>s. s(p \<mapsto> v))
  }"

lemma prod_exI: "P (fst x) (snd x) \<Longrightarrow> \<exists>a b. P a b"
  by (fastforce)


lemma [simp]: "None ## x" by (clarsimp simp: sep_disj_option_def)

lemma [simp]: "x ## None" by (clarsimp simp: sep_disj_option_def split: option.splits)



lemma set_ptr_spU:
  "\<lbrace><R>\<rbrace> set_ptr p v  \<lbrace>\<lambda>_. < ( p \<mapsto>u v \<and>* (p \<mapsto>u - -o R))> \<rbrace>u"
unfolding maps_to_ex_def
  apply (clarsimp simp: set_ptr_def) 
  apply (rule hoare_seq_extU[rotated])
   apply (rule modify_wpU)
  apply (rule hoare_chainU[OF state_assert_wpU, rotated])
   apply (assumption)
  apply (clarsimp) 
  apply (clarsimp simp: project_def to_flag_def)
  apply (case_tac "a p = None"; case_tac "ba p = None"; clarsimp?)
     apply (rule_tac x="ba + ([p \<mapsto> v])" in exI)
     apply (intro conjI)
      apply (clarsimp simp: sep_conj_def maps_to_def)
      apply (rule_tac x=a in exI)
      apply (rule_tac x="ba + ([p \<mapsto> v])" in exI)
      apply (intro conjI)
        apply (clarsimp simp: sep_disj_prod_def; clarsimp simp: sep_disj_fun_def sep_minus_def )
       apply (rule; intro ext, clarsimp simp: plus_prod_def zero_fun_def  plus_fun_def)
      apply (clarsimp simp: sept_def)
      apply (rule_tac x="[p \<mapsto> v]" in exI)
      apply (intro conjI; clarsimp?)
       apply (fastforce)
      apply (rule exI, rule exI, intro conjI, assumption)
       apply (clarsimp simp: compossible_prod_def compossible_fun_def
                             compossible_option_def zero_fun_def)
      apply (clarsimp simp: sep_minus_def, intro conjI ext; clarsimp?)
      apply (clarsimp simp: plus_fun_def)
     apply (clarsimp)
    apply (rule_tac x="ba" in exI)
    apply (intro conjI)
     apply (clarsimp simp: sep_conj_def maps_to_def)
     apply (rule_tac x=a in exI)
     apply (rule_tac x="ba + ([p \<mapsto> y])" in exI)
     apply (intro conjI)
       apply (clarsimp simp: sep_disj_prod_def; clarsimp simp: sep_disj_fun_def sep_minus_def )
      apply (rule; intro ext, clarsimp simp: plus_prod_def zero_fun_def  plus_fun_def)
     apply (clarsimp simp: sept_def)
     apply (rule_tac x="[p \<mapsto> y]" in exI)
     apply (intro conjI; clarsimp?)
      apply (fastforce)
     apply (rule exI, rule exI, intro conjI, assumption)
      apply (clarsimp simp: compossible_prod_def compossible_fun_def 
                            compossible_option_def  zero_fun_def)
     apply (clarsimp simp: sep_minus_def, intro conjI ext; clarsimp?)
     apply (clarsimp simp: plus_fun_def)
    apply (clarsimp simp: zero_fun_def zero_option_def)
   apply (rule_tac x="ba" in exI)
   apply (intro conjI)
    apply (clarsimp simp: sep_conj_def maps_to_def)
    apply (rule_tac x="a - [p \<mapsto> y]" in exI)
    apply (rule_tac x="ba" in exI)
    apply (intro conjI)
      apply (clarsimp simp: sep_disj_prod_def; clarsimp simp: sep_disj_fun_def sep_minus_def )
     apply (rule; intro ext, clarsimp simp: plus_prod_def zero_fun_def  plus_fun_def)
    apply (clarsimp simp: sept_def)
    apply (rule_tac x="[p \<mapsto> y]" in exI)
    apply (intro conjI; clarsimp?)
     apply (fastforce)
    apply (rule exI, rule exI, intro conjI, assumption)
     apply (clarsimp simp: compossible_prod_def compossible_fun_def
                           compossible_option_def zero_fun_def )
    apply (clarsimp simp: sep_minus_def, intro conjI ext; clarsimp?)
    apply (clarsimp simp: plus_fun_def)
   apply (clarsimp)
  apply (rule_tac x="ba" in exI)
  apply (intro conjI)
   apply (clarsimp simp: sep_conj_def maps_to_def)
   apply (rule_tac x="a - [p \<mapsto> y]" in exI)
   apply (rule_tac x="ba" in exI)
   apply (intro conjI)
     apply (clarsimp simp: sep_disj_prod_def; clarsimp simp: sep_disj_fun_def minus_option_def sep_minus_def )
    apply (rule; intro ext, clarsimp simp: plus_prod_def zero_fun_def  plus_fun_def)
   apply (clarsimp simp: sept_def)
   apply (rule_tac x="[p \<mapsto> y]" in exI)
   apply (intro conjI; clarsimp?)
    apply (fastforce)
   apply (rule exI, rule exI, intro conjI, assumption)
    apply (clarsimp simp: compossible_prod_def compossible_fun_def
                          compossible_option_def zero_fun_def )
   apply (clarsimp simp: sep_minus_def, intro conjI ext; clarsimp?)
   apply (clarsimp simp: plus_fun_def)
  apply (clarsimp)
  done

definition
  "get_ptr p = do {
    s <- get;
    assert (s p \<noteq> None);
    modify (\<lambda>s. s(p \<mapsto> the (s p)));
    return (the (s p ))
  }"

lemma "v \<noteq> v' \<Longrightarrow> sept (maps_to p v) (\<lambda>(x,y). maps_to p v' (y,x)) (0, [p \<mapsto> v'])" 
  apply (clarsimp simp: sept_def maps_to_def, intro conjI)
   apply (clarsimp simp: zero_fun_def compossible_prod_def compossible_fun_def compossible_option_def )
  apply (rule prod_eqI; clarsimp simp: zero_prod_def, rule ext)
   apply (clarsimp simp: zero_fun_def sep_minus_def plus_fun_def) 
  apply (clarsimp simp: zero_fun_def sep_minus_def plus_fun_def) 
  apply (clarsimp simp: plus_option_def)
  done

lemma get_ptr_spU:
  "\<lbrace><R>\<rbrace> get_ptr p  
   \<lbrace>\<lambda>rv s.  < (maps_to p rv \<and>* sept (maps_to p rv) R )> s \<rbrace>u"
  apply (clarsimp simp: get_ptr_def) 
  apply (rule hoare_seq_extU[rotated])
   apply (rule hoare_seq_extU[rotated])
    apply (rule hoare_seq_extU[rotated])
     apply (rule return_wpU)
    apply (rule modify_wpU)
   apply (rule assert_wpU)
  apply (rule hoare_chainU[OF get_wpU, rotated])
   apply (assumption)
  apply (clarsimp) 
  apply (clarsimp simp: project_def to_flag_def)
  apply (case_tac "ba = 0"; simp) 
   apply (case_tac "a p = None"; clarsimp?)
    apply (rule_tac x="([p \<mapsto> the (a p)])" in exI)
    apply (intro conjI)
     apply (clarsimp simp: sep_conj_def maps_to_def)
     apply (rule_tac x=a in exI)
     apply (rule_tac x="([p \<mapsto> the (a p)])" in exI)
     apply (intro conjI)
       apply (clarsimp simp: sep_disj_prod_def; clarsimp simp: sep_disj_fun_def sep_minus_def )
      apply (rule; intro ext, clarsimp simp: plus_prod_def zero_fun_def  plus_fun_def) 
     apply (clarsimp simp: sept_def)
     apply (rule_tac x="a" in exI, rule_tac x="0" in exI, clarsimp)
     apply (intro conjI; clarsimp?)
      apply (clarsimp simp: zero_fun_def compossible_prod_def compossible_fun_def compossible_option_def)
     apply (clarsimp simp: sep_minus_def, intro conjI ext; clarsimp?)
    apply (clarsimp simp: plus_fun_def)
   apply (clarsimp simp: sep_conj_def maps_to_def)
   apply (rule_tac x="a - [p \<mapsto> y]"  in exI)
   apply (rule_tac x="0" in exI)
   apply (intro conjI)
     apply (clarsimp simp: sep_disj_prod_def; clarsimp simp: sep_disj_fun_def sep_minus_def )
    apply (rule; intro ext, clarsimp simp: plus_prod_def zero_fun_def  plus_fun_def)
   apply (clarsimp simp: sept_def)
   apply (rule_tac x="a" in exI, rule_tac x="0" in exI, clarsimp)
   apply (intro conjI; clarsimp?)
    apply (clarsimp simp: zero_fun_def compossible_prod_def compossible_fun_def compossible_option_def)
   apply (clarsimp simp: sep_minus_def, intro conjI ext; clarsimp?)
   apply (clarsimp simp: zero_fun_def)
  apply (case_tac "a p = None"; case_tac "ba p";  clarsimp?)
     apply (rule_tac x="ba + [p \<mapsto> the (a p)]" in exI)
     apply (clarsimp simp: sep_conj_def maps_to_def)
     apply (rule_tac x=a in exI)
     apply (rule_tac x="ba + [p \<mapsto> the (a p)]" in exI)
     apply (intro conjI)
       apply (clarsimp simp: sep_disj_prod_def sep_disj_fun_def zero_fun_def)
      apply (rule prod_eqI; rule ext, clarsimp)
       apply (clarsimp simp: plus_prod_def plus_fun_def)
      apply (clarsimp simp: plus_prod_def plus_fun_def zero_fun_def)
     apply (clarsimp simp: sept_def)
     apply (rule_tac exI, rule_tac exI, intro conjI, fastforce)
      apply (clarsimp simp: zero_fun_def compossible_prod_def compossible_fun_def compossible_option_def)
     apply (rule prod_eqI; rule ext, clarsimp simp: sep_minus_def plus_fun_def zero_fun_def)
    apply (rule_tac x="ba" in exI)
    apply (clarsimp simp: sep_conj_def maps_to_def)
    apply (rule_tac x=a in exI)
    apply (rule_tac x="ba " in exI)
    apply (intro conjI)
      apply (clarsimp simp: sep_disj_prod_def sep_disj_fun_def zero_fun_def)
     apply (rule prod_eqI; rule ext, clarsimp)
      apply (clarsimp simp: plus_prod_def plus_fun_def)
     apply (clarsimp simp: plus_prod_def plus_fun_def zero_fun_def)
    apply (clarsimp simp: sept_def)
    apply (rule_tac exI, rule_tac exI, intro conjI, fastforce)
     apply (clarsimp simp: zero_fun_def compossible_prod_def compossible_fun_def compossible_option_def)
    apply (rule prod_eqI; rule ext, clarsimp simp: sep_minus_def plus_fun_def zero_fun_def)
    apply (clarsimp simp: plus_option_def)
   apply (rule_tac x="ba" in exI)
   apply (clarsimp simp: sep_conj_def maps_to_def)
   apply (rule_tac x="a - [p \<mapsto> the (a p)]" in exI)
   apply (rule_tac x="ba " in exI)
   apply (intro conjI)
     apply (clarsimp simp: sep_disj_prod_def sep_disj_fun_def zero_fun_def)
    apply (clarsimp simp: minus_option_def)
    apply (rule prod_eqI; rule ext, clarsimp)
     apply (clarsimp simp: plus_prod_def plus_fun_def)
    apply (clarsimp simp: plus_prod_def plus_fun_def zero_fun_def)
   apply (clarsimp simp: minus_option_def)
   apply (clarsimp simp: plus_prod_def plus_fun_def zero_fun_def)
   apply (clarsimp simp: sept_def)
   apply (rule_tac exI, rule_tac exI, intro conjI, fastforce)
    apply (clarsimp simp: zero_fun_def compossible_prod_def compossible_fun_def compossible_option_def)
   apply (rule prod_eqI; rule ext, clarsimp simp: sep_minus_def plus_fun_def zero_fun_def)
  apply (rule_tac x="ba" in exI)
  apply (clarsimp simp: sep_conj_def maps_to_def)
  apply (rule_tac x="a - [p \<mapsto> the (a p)]" in exI)
  apply (rule_tac x="ba " in exI)
  apply (intro conjI)
    apply (clarsimp simp: sep_disj_prod_def sep_disj_fun_def zero_fun_def minus_option_def)
   apply (rule prod_eqI; rule ext, clarsimp)
    apply (clarsimp simp: plus_prod_def plus_fun_def minus_option_def)
   apply (clarsimp simp: plus_prod_def plus_fun_def zero_fun_def)
  apply (clarsimp simp: sept_def)
  apply (rule_tac exI, rule_tac exI, intro conjI, fastforce)
   apply (clarsimp simp: zero_fun_def compossible_prod_def compossible_fun_def compossible_option_def)
  apply (rule prod_eqI; rule ext, clarsimp simp: sep_minus_def plus_fun_def zero_fun_def minus_option_def)
  done

lemma sept_cancel: 
   "sept P R s \<Longrightarrow> (\<And>s. P s \<Longrightarrow> P' s) \<Longrightarrow> (\<And>s. R s \<Longrightarrow> R' s)  \<Longrightarrow> sept P' R' s"
  apply (clarsimp simp: sept_def)
  apply (rule_tac x=a in exI)
  apply (rule_tac x=b in exI)
  apply (intro conjI, fastforce)
  apply (rule exI)+
  apply (intro conjI, fastforce)
   apply (clarsimp)
  apply (clarsimp)
  done

lemma sep_disj_fun_def'[dest]: "x ## y \<Longrightarrow> x v ## y v" 
 by (fastforce simp: sep_disj_fun_def)  

lemma sep_disj_some_eq[simp]: "Some x ## y \<longleftrightarrow> y = None" 
 by (auto simp: sep_disj_option_def)  

lemma sep_minus_disj_plus[simp]: 
  "x ## y \<Longrightarrow> sep_minus (x + y) y = (x :: ('a, 'b) abstract_ext')" 
  apply (auto simp: prod_eq_iff sep_disj_prod_def plus_prod_def sep_minus_def; rule ext)[1]
   apply (clarsimp simp: plus_fun_def fun_diff_def)
   apply (smt minus_option_def option.case_eq_if plus_option_def 
      sep_disj_fun_def sep_disj_option_def zero_option_def)
  apply (clarsimp simp: plus_fun_def fun_diff_def)
  apply (smt minus_option_def option.case_eq_if plus_option_def 
      sep_disj_fun_def sep_disj_option_def zero_option_def)
  done

lemma sep_minus_disj_plus'[simp]:"y ## x \<Longrightarrow> sep_minus (x + y) y = (x :: ('a, 'b) abstract_ext')" 
  by (clarsimp simp: sep_disj_commute)

lemma sep_minus_disj_plus''[simp]: "x ## y \<Longrightarrow> sep_minus (x + y) x = (y :: ('a, 'b) abstract_ext')" 
  using sep_add_commute by fastforce

lemma sep_minus_disj_plus'''[simp]: "y ## x \<Longrightarrow> sep_minus (x + y) x = (y :: ('a, 'b) abstract_ext')" 
  using sep_disj_commuteI sep_minus_disj_plus'' by blast


lemma sep_add_minus_eq: "x ## y \<Longrightarrow> y \<preceq> z \<Longrightarrow> x + y = z \<longleftrightarrow> x = sep_minus z (y :: ('a, 'b) abstract_ext')" 
  apply (rule iffI) 
  apply (clarsimp)
  by (clarsimp simp: sep_substate_def sep_add_commute)


lemma sep_disj_minus_pair: "y && x \<Longrightarrow> 
    snd x ## fst x \<Longrightarrow> 
    x ##  sep_minus y  (x :: ('a, 'b) abstract_ext')" 
  apply (clarsimp simp: sep_disj_prod_def, intro conjI)
  apply (clarsimp simp: sep_minus_def)
  apply (unfold sep_disj_fun_def,
         clarsimp simp: fun_diff_def plus_fun_def zero_fun_def compossible_prod_def 
                        compossible_fun_def compossible_option_def)
  apply (erule_tac x=xa in allE)
  apply (smt case_optionE compossible_fun_def disjoint_zero_sym minus_option_def
          sep_add_zero sep_disj_option_def sep_disj_zero sep_substate_def)
    apply (clarsimp simp: sep_minus_def)
  apply ( clarsimp simp: fun_diff_def plus_fun_def)
   apply ( clarsimp simp: fun_diff_def plus_fun_def 
       zero_fun_def compossible_prod_def compossible_fun_def compossible_option_def)
    apply (erule_tac x=xa in allE)
apply (smt case_optionE compossible_fun_def disjoint_zero_sym minus_option_def
          sep_add_zero sep_disj_option_def sep_disj_zero sep_substate_def)
done

definition
  "move_ptr p p' = do {
    x <- get_ptr p;
    set_ptr p' x
  }"

definition "maps_to'_ex p \<equiv> \<lambda>s. \<exists> v. maps_to' p v s"

lemma sept_cancel1: " (\<And>s. R s \<Longrightarrow> R' s) \<Longrightarrow> sept P R s \<Longrightarrow> sept P R' s"
   by (erule (1) sept_cancel)

lemma move_ptr_spU:
  "\<lbrace><R>\<rbrace> move_ptr p p' 
   \<lbrace>\<lambda>_.  
    <EXS v. (maps_to p' v \<and>* (sept (maps_to_ex p') (maps_to p v \<and>* sept (maps_to p v) R) ))> \<rbrace>u"
 apply (clarsimp simp: move_ptr_def)
   apply (rule hoare_seq_extU)
   apply (rule get_ptr_spU)
   apply (rule hoare_chainU[rotated 3])
    apply (rule set_ptr_spU, assumption)
apply (erule projectE)
  apply (rule_tac x=x in exI)
 apply (sep_cancel)
done

lemma sept_maps_to: "sept (maps_to p x) (maps_to p y \<and>* R) h \<Longrightarrow> R h \<and>  x = y"
 apply (clarsimp simp: sept_def maps_to_def sep_conj_def)
 apply (intro conjI)
 apply (erule back_subst[where P=R])
 apply (rule prod_eqI; rule ext; clarsimp simp: sep_minus_def plus_prod_def)
 apply (clarsimp simp: zero_fun_def compossible_prod_def compossible_fun_def 
 plus_fun_def minus_option_def plus_option_def zero_option_def )
  apply (smt fun_upd_same minus_option_def 
    minus_some_simp option.case_eq_if option.distinct(1) compossible_fun_def 
 prod.sel(1) sep_disj_fun_def' sep_disj_prod_def sep_disj_some_eq zero_option_def)
apply (clarsimp simp: compossible_prod_def compossible_fun_def 
 plus_fun_def minus_option_def plus_option_def zero_option_def zero_fun_def)
  apply (smt fun_upd_same minus_option_def 
    minus_some_simp option.case_eq_if option.distinct(1) compossible_option_def 
 prod.sel(1) sep_disj_fun_def' sep_disj_prod_def sep_disj_some_eq zero_option_def)
apply (clarsimp simp: compossible_prod_def compossible_fun_def 
 plus_fun_def minus_option_def plus_option_def zero_option_def zero_fun_def)
apply (clarsimp simp: plus_prod_def sep_minus_def plus_fun_def minus_option_def split: prod.splits)
apply (erule_tac x=p in allE)
apply (clarsimp simp: compossible_option_def)
apply (elim disjE; clarsimp simp: plus_option_def )
  apply (simp add: option.case_eq_if sep_substate_def)
  apply (simp add: option.case_eq_if sep_substate_def)
done

lemma [simp]: "Some x \<preceq> Some y \<longleftrightarrow> (x = y) " 
 by (clarsimp simp: sep_substate_def)

lemma [simp]: "Some x - y = None \<longleftrightarrow> y \<noteq> None" 
by (clarsimp simp: zero_option_def minus_option_def)


lemma sept_maps_to_snake: " 
                  (maps_to p y \<and>* R) s \<Longrightarrow> (\<And>s. R s \<Longrightarrow> y = x \<Longrightarrow>  R'  s)  \<Longrightarrow> 
                  snake (maps_to p x)  R' s"
 apply (clarsimp simp: snake_def maps_to_def sep_conj_def)
 apply (atomize, erule_tac x=a in allE, erule_tac x=b in allE, clarsimp)
 apply (erule impE)
 apply (clarsimp simp:  compossible_prod_def compossible_fun_def  
 plus_fun_def minus_option_def plus_option_def zero_option_def zero_fun_def)
 apply (erule_tac x=p in allE) 
 apply (erule_tac x=p in allE)
 apply (clarsimp simp: plus_prod_def prod_eq_iff)
 thm prod_eqI
 apply (drule_tac x=p in fun_cong)
  apply (drule_tac x=p in fun_cong)
 apply (clarsimp simp: plus_fun_def sep_disj_fun_def sep_disj_prod_def)
 apply (erule_tac x=p in allE)
 apply (clarsimp simp: compossible_option_def)
 apply (erule back_subst[where P=R'])
 apply (clarsimp simp: plus_prod_def prod_eq_iff, intro conjI ext; 
       clarsimp simp: sep_minus_def plus_fun_def zero_option_def zero_fun_def)
  apply (smt fun_upd_same minus_option_def 
    minus_some_simp option.case_eq_if option.distinct(1) compossible_option_def 
 prod.sel(1) sep_disj_fun_def' sep_disj_prod_def sep_disj_some_eq zero_option_def)
  by (simp add: option.case_eq_if plus_option_def zero_option_def)

lemma sept_maps_to_ex: "sept (maps_to_ex p) (maps_to p y \<and>* R) h \<Longrightarrow> R h"
 apply (clarsimp simp: sept_def maps_to_def maps_to_ex_def sep_conj_def)
 apply (erule back_subst[where P=R])
 apply (rule prod_eqI; rule ext; clarsimp simp: sep_minus_def plus_prod_def)
 apply (clarsimp simp: compossible_prod_def compossible_fun_def 
 plus_fun_def minus_option_def plus_option_def zero_option_def zero_fun_def)
  apply (smt fun_upd_same minus_option_def 
    minus_some_simp option.case_eq_if option.distinct(1) compossible_fun_def 
 prod.sel(1) sep_disj_fun_def' sep_disj_prod_def sep_disj_some_eq zero_option_def)
 apply (clarsimp simp: compossible_prod_def compossible_fun_def 
 plus_fun_def minus_option_def plus_option_def zero_option_def zero_fun_def)
  apply (smt fun_upd_same minus_option_def 
    minus_some_simp option.case_eq_if option.distinct(1) compossible_fun_def 
 prod.sel(1) sep_disj_fun_def' sep_disj_prod_def sep_disj_some_eq zero_option_def)
done

lemma sept_maps_to_ex': "sept (maps_to_ex p) (maps_to_ex p  \<and>* R) h \<Longrightarrow> R h"
 apply (clarsimp simp: sept_def maps_to_def maps_to_ex_def sep_conj_def)
 apply (erule back_subst[where P=R])
 apply (rule prod_eqI; rule ext; clarsimp simp: sep_minus_def plus_prod_def)
 apply (clarsimp simp: compossible_prod_def compossible_fun_def 
 plus_fun_def minus_option_def plus_option_def zero_option_def zero_fun_def)
  apply (smt fun_upd_same minus_option_def 
    minus_some_simp option.case_eq_if option.distinct(1) compossible_fun_def 
 prod.sel(1) sep_disj_fun_def' sep_disj_prod_def sep_disj_some_eq zero_option_def)
 apply (clarsimp simp: compossible_prod_def compossible_fun_def 
 plus_fun_def minus_option_def plus_option_def zero_option_def zero_fun_def)
  apply (smt fun_upd_same minus_option_def 
    minus_some_simp option.case_eq_if option.distinct(1) compossible_fun_def 
 prod.sel(1) sep_disj_fun_def' sep_disj_prod_def sep_disj_some_eq zero_option_def)
done

lemma pred_conjI:"P s \<Longrightarrow> Q s \<Longrightarrow> (P and Q) s" by (clarsimp simp: pred_conj_def)


lemma sep_plus_minus: "x ## y \<Longrightarrow> x + y - y = (x :: 'a option)"
 by (clarsimp simp: plus_option_def minus_option_def zero_option_def split: option.splits)

lemma sep_plus_minus_eq:"(x ## y \<and> x + y = z) \<longleftrightarrow> (z - y = (x :: 'a \<Rightarrow> 'b option) \<and> y \<preceq> z)" 
 apply (rule iffI; clarsimp; intro conjI)
 apply (rule ext, clarsimp simp: plus_fun_def fun_diff_def sep_disj_fun_def' sep_plus_minus)
 apply (clarsimp simp:  sep_substate_def)
 apply (rule_tac x=x in exI; clarsimp simp: sep_disj_commute sep_add_commute)
 apply (clarsimp simp: sep_substate_def)
 apply (clarsimp simp: sep_disj_fun_def)
 apply ( clarsimp simp: plus_fun_def fun_diff_def sep_disj_fun_def' sep_plus_minus)
 apply (simp add: sep_add_commute sep_disj_commuteI sep_plus_minus)
 apply (clarsimp simp: sep_substate_def)
 apply (rule ext, clarsimp simp: plus_fun_def fun_diff_def)
 by (simp add: sep_add_commute sep_disj_commuteI sep_disj_fun_def sep_plus_minus)



lemma sep_plus_minus_eq':" z && y \<Longrightarrow> x ## y \<Longrightarrow>
 (z - y \<preceq> x) \<longleftrightarrow> (z \<preceq> x + (y :: 'a \<Rightarrow> 'b option))" 
 apply (rule iffI)
 apply (clarsimp simp: sep_substate_def)
 apply (rule_tac x="(za + y) - z " in exI)
 apply (intro conjI)
 apply (clarsimp simp: sep_disj_fun_def, (erule_tac x=xa in allE)+)
 apply (drule_tac x=xa in fun_cong)
 apply (clarsimp simp: compossible_fun_def, erule_tac x=xa in allE)
 apply (clarsimp simp: plus_fun_def fun_diff_def compossible_option_def)
 apply (clarsimp simp: sep_disj_option_def split: option.splits)

 apply (rule ext)
 apply (clarsimp simp: plus_fun_def)
apply (clarsimp simp: sep_disj_fun_def, (erule_tac x=xa in allE)+)
 apply (drule_tac x=xa in fun_cong)
 apply (clarsimp simp: compossible_fun_def, erule_tac x=xa in allE)
 apply (clarsimp simp: plus_fun_def fun_diff_def compossible_option_def)
 apply (clarsimp simp: sep_disj_option_def split: option.splits)
 apply (clarsimp simp: plus_option_def)
 apply (clarsimp simp: minus_option_def zero_option_def split: if_splits option.splits)
 apply (clarsimp simp: sep_substate_def)
 apply (rule_tac x="za - y"  in exI)
 apply (intro conjI)
 apply (clarsimp simp: sep_disj_fun_def, (erule_tac x=xa in allE)+)
 apply (drule_tac x=xa in fun_cong)
 apply (clarsimp simp: compossible_fun_def, erule_tac x=xa in allE)
 apply (clarsimp simp: plus_fun_def fun_diff_def compossible_option_def)
 apply (clarsimp simp: sep_disj_option_def split: option.splits)
 apply (rule ext)
 apply (clarsimp simp: plus_fun_def)
apply (clarsimp simp: sep_disj_fun_def, (erule_tac x=xa in allE)+)
 apply (drule_tac x=xa in fun_cong)
 apply (clarsimp simp: compossible_fun_def, erule_tac x=xa in allE)
 apply (clarsimp simp: plus_fun_def fun_diff_def compossible_option_def)
 apply (clarsimp simp: sep_disj_option_def split: option.splits)
 apply (clarsimp simp: minus_option_def zero_option_def split: if_splits option.splits) 
 apply (clarsimp simp: minus_option_def zero_option_def split: if_splits option.splits) 
done




lemma sep_disj_minus_pair': " h && h' \<Longrightarrow> fst h ## snd h \<Longrightarrow> 
h ## sep_minus h' (h :: ('a, 'b) abstract_ext')"
  using compossible_commute sep_disj_commuteI sep_disj_minus_pair by blast

lemma sep_disj_minus_pair': 
 "h && h'  \<Longrightarrow> h ## sep_minus h' (h :: ('a, 'b) abstract_ext')" oops




lemma wand_star_gal: " (\<And>s. Q s \<Longrightarrow> (wand P R) s) \<Longrightarrow>  ((star P Q) s \<Longrightarrow> R s)" 
   apply (clarsimp simp: wand_def star_def pred_neg_def)
  apply (atomize)
  apply (clarsimp simp: snake_def)
  apply (erule_tac x="fst (s - (a, b))" in allE )
  apply (erule_tac x="snd (s - (a, b))" in allE )
  apply (clarsimp simp: sept_def)
  apply (erule allE, erule allE, drule (1) mp)
  apply (erule_tac x="fst s" in allE)
  apply (erule_tac x="snd s" in allE)
  apply (clarsimp)
  apply (metis compossible_commute)
done

lemma sep_disj_comp_add: "x ## (y :: ('a,'b) abstract_ext') \<Longrightarrow> x && (x + y)"
 apply (clarsimp simp: compossible_prod_def plus_prod_def 
       compossible_fun_def plus_fun_def compossible_option_def)
  by (simp add: sep_disj_fun_def' sep_disj_prod_def sep_substate_disj_add)


lemma sep_snake_coimpl:"(P \<leadsto>o R) s \<Longrightarrow> (P \<leadsto>* R) (s :: ('a,'b) abstract_ext')"
 apply (clarsimp simp: sep_coimpl_def snake_def sep_conj_def)
 apply (erule_tac x=a in allE, erule_tac x=b in allE)
 apply (clarsimp simp: pred_neg_def)
 by (metis compossible_commute sep_disj_comp_add)

lemma sep_wand_impl:"(P \<longrightarrow>o R) s \<Longrightarrow> (P \<longrightarrow>* R) (s :: ('a,'b) abstract_ext')"
 apply (clarsimp simp: sep_impl_def wand_def sept_def sep_conj_def pred_neg_def)
 apply (erule_tac x=a in allE, erule_tac x=b in allE)
 apply (clarsimp simp: pred_neg_def)
 apply (erule_tac x="fst (s + (a, b))" in allE, erule_tac x="snd (s + (a, b))" in allE)
 apply (clarsimp)
  by (metis sep_add_commute sep_disj_commuteI sep_disj_comp_add)

lemma sep_star_conj:"(P \<and>* R) s \<Longrightarrow> (P \<circle> R) (s :: ('a,'b) abstract_ext')"
 apply (clarsimp simp: sep_coimpl_def snake_def sep_conj_def pred_neg_def star_def)
 apply (rule_tac x="a" in exI)
 apply (rule_tac x="b" in exI)
 apply (clarsimp)
  using sep_disj_comp_add compossible_commute by blast

lemma sep_sept_septraction:"(P -* R) s \<Longrightarrow> (P -o R) (s :: ('a,'b) abstract_ext')"
 apply (clarsimp simp: sept_def septraction_def sep_conj_def sep_impl_def pred_neg_def)
 apply (rule_tac x=a in exI, rule_tac x=b in exI, clarsimp)
 apply (rule_tac x="fst (s + (a, b))" in exI)
  apply (rule_tac x="snd (s + (a, b))" in exI)
 apply (clarsimp)
  by (metis sep_add_commute sep_disj_commuteI sep_disj_comp_add)


lemma sep_minus_compos_simp[simp]: "compossible x  y \<Longrightarrow> x + y - x = y - (x :: 'a \<Rightarrow> 'b option)"
 apply (rule ext, clarsimp simp: plus_fun_def fun_diff_def)
 by (clarsimp simp: plus_option_def minus_option_def zero_option_def split: option.splits)


lemma sep_minus_compos_simp'[simp]: "compossible x  y \<Longrightarrow> x - (y + x) = (0 :: 'a \<Rightarrow> 'b option)"
 apply (rule ext, clarsimp simp: plus_fun_def fun_diff_def)
 by  (clarsimp simp: plus_option_def minus_option_def zero_fun_def zero_option_def split: option.splits)


lemma sep_minus_compos_simp_o[simp]: " x &&  y \<Longrightarrow> 
     x + y - x = y - (x :: 'b option)"
 by (clarsimp simp: plus_option_def minus_option_def compossible_option_def
     zero_option_def split: option.splits)

lemma sep_minus_compos_simp_o'[simp]: " x && y \<Longrightarrow> x - (y + x) = (0 :: 'b option)"
 by (clarsimp simp: plus_option_def minus_option_def zero_fun_def
     compossible_option_def zero_option_def split: option.splits)

lemma sep_minus_compos_simp_o''[simp]: " x && y \<Longrightarrow> x - (x + y) = (0 :: 'b option)"
 by (clarsimp simp: plus_option_def minus_option_def zero_fun_def 
     compossible_option_def zero_option_def split: option.splits)


lemma sep_comp_add_assoc:  " x && y \<Longrightarrow>  y && z \<Longrightarrow>  x && (z :: 'b option) \<Longrightarrow>
    x + y + z = x + (y + z)"
  apply (clarsimp simp: plus_option_def split: option.splits)
done

lemma sep_option_compos_add: " x && (y :: 'b option) \<Longrightarrow>  x && (x + y)"
 apply (clarsimp simp: compossible_option_def) 
 apply (erule disjE)
 apply (clarsimp simp: sep_substate_def)
 apply (rule_tac x=z in exI)
 apply (clarsimp)
 apply (clarsimp simp: plus_option_def split: option.splits)
 apply (clarsimp simp: sep_substate_def)
 apply (rule_tac x=0 in exI)
 apply (clarsimp)
 apply (clarsimp simp: plus_option_def split: option.splits)
done

lemma sep_add_compos: " y && (z :: 'a option) \<Longrightarrow> 
                   x && (y + z) \<Longrightarrow>  x && y \<and>  x && z" 
 apply (intro conjI; clarsimp simp: compossible_option_def; elim disjE; clarsimp simp: sep_substate_def)

  apply (metis minus_option_def compossible_option_def sep_disj_zero
 sep_option_compos_add sep_plus_minus sep_substate_def)
  apply (metis minus_option_def compossible_option_def sep_minus_compos_simp_o'' 
sep_option_compos_add sep_plus_minus sep_substate_def)
apply (metis minus_option_def compossible_option_def sep_add_commute sep_disj_commuteI
 sep_option_compos_add sep_plus_minus sep_substate_def)
  apply (metis minus_option_def compossible_option_def sep_add_disjD sep_minus_compos_simp_o'' 
sep_option_compos_add sep_plus_minus sep_substate_def)
  apply (metis (no_types, lifting) minus_option_def 
compossible_option_def sep_disj_commuteI sep_option_compos_add 
sep_plus_minus sep_substate_def sep_substate_disj_add')

  apply (metis (no_types, lifting) minus_option_def compossible_option_def
  sep_add_disj_eq sep_disj_commuteI sep_minus_compos_simp_o sep_minus_compos_simp_o'' 
 sep_option_compos_add sep_plus_minus sep_substate_def)

  apply (metis minus_option_def compossible_option_def
 sep_disj_zero sep_option_compos_add sep_plus_minus sep_substate_def)
  by (metis minus_option_def compossible_option_def sep_minus_compos_simp_o''
 sep_option_compos_add sep_plus_minus sep_substate_def)


lemma sep_add_minus_comp_o[simp]: "x && y \<Longrightarrow> x + (y - x) = (x + y :: 'a option)"
 by (clarsimp simp: plus_option_def minus_option_def zero_option_def split: option.splits)


lemma sep_disj_minus_comp_o[simp]: " x ## y - (x :: 'a option)"
 apply (clarsimp simp: sep_disj_option_def minus_option_def)
 by (clarsimp simp: zero_option_def)


lemma sep_comp_substate: " (x :: ('a,'b) abstract_ext') && (y + z) \<Longrightarrow>
                          y ## z \<Longrightarrow> x \<preceq> x + y + z" 
 apply (clarsimp simp: sep_substate_def)
 apply (rule_tac x="fst ((x + y + z) - x)" in exI) 
 apply (rule_tac x="snd ((x + y + z) - x)" in exI) 
 apply (clarsimp, intro conjI)
 apply (clarsimp simp: sep_disj_prod_def sep_disj_fun_def, 
       intro conjI allI; erule_tac x=xa in allE, erule_tac x=xa in allE,
       clarsimp simp: plus_prod_def plus_fun_def sep_minus_def fun_diff_def)
apply (clarsimp simp: compossible_prod_def compossible_fun_def)
  apply (smt option.case_eq_if option.collapse
 plus_option_def sep_disj_minus_comp_o sep_disj_option_def sep_plus_minus)
apply (clarsimp simp: compossible_prod_def compossible_fun_def)
  apply (smt option.case_eq_if option.collapse
 plus_option_def sep_disj_minus_comp_o sep_disj_option_def sep_plus_minus)

apply (clarsimp simp: plus_prod_def sep_minus_def, intro conjI ext)
apply (clarsimp simp: plus_fun_def fun_diff_def)
apply (clarsimp simp: sep_disj_prod_def sep_disj_fun_def, erule_tac x=xa in allE, 
      erule_tac x=xa in allE)
apply (clarsimp simp: compossible_prod_def compossible_fun_def )
 apply (smt option.case_eq_if option.collapse
 plus_option_def sep_disj_minus_comp_o sep_disj_option_def sep_plus_minus)
apply (clarsimp simp: compossible_prod_def compossible_fun_def )
apply (clarsimp simp: plus_fun_def )

 apply (smt option.case_eq_if option.collapse
 plus_option_def sep_disj_minus_comp_o sep_disj_option_def sep_plus_minus)
done



lemma sep_comp_substate':  "(x :: ('a,'b) abstract_ext') && (y + z) \<Longrightarrow> y ## z \<Longrightarrow>
 y \<preceq> x + y + z"
 apply (clarsimp simp: sep_substate_def)
 apply (rule_tac x="fst ((x + y + z) - y)" in exI) 
 apply (rule_tac x="snd ((x + y + z) - y)" in exI) 
 apply (clarsimp, intro conjI)
 apply (clarsimp simp: sep_disj_prod_def sep_disj_fun_def, 
       intro conjI allI; erule_tac x=xa in allE, erule_tac x=xa in allE,
       clarsimp simp: plus_prod_def plus_fun_def sep_minus_def fun_diff_def)
 apply (clarsimp simp: minus_option_def)
  apply (metis (no_types, lifting) option.case_eq_if 
         plus_option_def sep_disj_zero zero_option_def)
 apply (clarsimp simp: minus_option_def)
   apply (metis (no_types, lifting) option.case_eq_if 
         plus_option_def sep_disj_zero zero_option_def)
  apply (clarsimp simp: prod_eq_iff, intro conjI ext; 
         clarsimp simp: sep_disj_prod_def sep_disj_fun_def, erule_tac x=xa in allE, erule_tac x=xa in allE)
apply (clarsimp simp: plus_prod_def sep_minus_def plus_fun_def fun_diff_def)
apply (clarsimp simp: compossible_prod_def compossible_fun_def, erule_tac x=xa in allE)
 apply (clarsimp simp: minus_option_def, intro conjI impI)
  apply (smt option.case_eq_if option.distinct(1) 
   plus_option_def zero_option_def)
  apply (metis (no_types, lifting) option.case_eq_if option.collapse compossible_option_def 
plus_option_def sep_add_zero sep_disj_some_eq sep_substate_def)
 apply (clarsimp simp: compossible_option_def; elim disjE)
  apply (smt minus_option_def compossible_option_def sep_add_commute 
sep_add_minus_comp_o sep_plus_minus sep_substate_def)
 apply (smt minus_option_def compossible_option_def sep_add_commute 
sep_add_minus_comp_o sep_plus_minus sep_substate_def)
apply (clarsimp simp: plus_prod_def sep_minus_def plus_fun_def fun_diff_def)
apply (clarsimp simp: compossible_prod_def compossible_fun_def, erule_tac x=xa in allE, erule_tac x=xa in allE)
 apply (clarsimp simp: minus_option_def, intro conjI impI)
  apply (smt minus_option_def sep_add_commute sep_disj_zero 
sep_minus_compos_simp_o sep_minus_compos_simp_o'' sep_plus_minus)
  apply (smt minus_option_def compossible_option_def sep_add_commute
 sep_add_minus_comp_o sep_plus_minus sep_substate_def)
  apply (smt minus_option_def compossible_option_def sep_add_commute
 sep_add_minus_comp_o sep_plus_minus sep_substate_def)
done


lemma septraction_maps_to_minus_heaplet_precise_conj: 
 "precise P \<Longrightarrow> (sept P (P \<and>* R)) s \<Longrightarrow> R (s :: ('a,'b) abstract_ext')" 
apply (erule snake_sept_gal[rotated]; clarsimp)
apply (clarsimp simp: snake_def sep_conj_def)
apply (erule_tac back_subst[where P=R])
apply (subgoal_tac "(aa, ba) = (ac, bc)", clarsimp) 
apply (unfold precise_def)
apply (erule_tac x="(ac, bc) + (aa, ba) + (ab, bb)" in allE)
apply (erule_tac x="(aa, ba)" in allE)
apply (erule_tac x="(ac, bc)" in allE)
apply (clarsimp)
by (simp add: compossible_commute sep_comp_substate sep_comp_substate')



definition "free \<equiv> \<lambda>s. \<exists>p. p \<noteq> 0 \<and> s p = None"

definition "select \<equiv> \<lambda>s. (SOME p. p \<noteq> 0 \<and> s p = None)"


definition
  "new_ptr = do {
    s <- get;
    if free s then 
    do {
        modify (\<lambda>s. s (select s \<mapsto> 0));
        return (select s)
     } else
    return 0
  }"

lemma "\<lbrace>R\<rbrace> new_ptr 
       \<lbrace>\<lambda>rv s. if rv \<noteq> 0 then (maps_to'_ex rv \<and>* R) s else R s\<rbrace>u"
 apply (clarsimp simp: new_ptr_def)
 apply (clarsimp simp: validU_def bind_def get_def modify_def put_def return_def)
 apply (intro conjI impI; clarsimp simp: free_def select_def )
 apply (clarsimp simp: sep_conj_def maps_to'_ex_def maps_to'_def)
 apply (rule_tac x="[SOME p. p \<noteq> 0 \<and> s p = None \<mapsto> 0]" in exI)
 apply (rule_tac x=s in exI, rule_tac x=f in exI)
 apply (clarsimp; intro conjI)
 apply (clarsimp simp: sep_disj_prod_def sep_disj_fun_def)
  apply (metis (mono_tags, lifting) someI)
 apply (rule prod_eqI; clarsimp simp: plus_prod_def plus_fun_def)
 apply (rule ext, clarsimp simp: plus_option_def split: option.splits)
 apply (fastforce)
  apply (smt tfl_some)
done        

           
term project
lemma new_ptr_spU:"\<lbrace>project R\<rbrace> 
       new_ptr 
       \<lbrace>\<lambda>rv. project (\<lambda>s. if rv \<noteq> 0 then (maps_to_ex rv \<and>* R) s else 
               (R s \<and>  (\<forall>p. p \<noteq> 0 \<longrightarrow> (maps_to_ex p \<and>* sep_true) s))) \<rbrace>u"
 apply (clarsimp simp: new_ptr_def)
 apply (clarsimp simp: validU_def bind_def get_def modify_def put_def return_def)
 apply (intro conjI impI allI )
 apply (clarsimp simp: project_def)
 apply (clarsimp simp: to_flag_def)
 apply (rule_tac x=b in exI)
 apply (clarsimp, intro conjI impI)
 apply (clarsimp simp: sep_conj_def maps_to_ex_def maps_to_def project_def to_flag_def)
 apply (rule_tac x="[select s \<mapsto> 0]" in exI)
 apply (rule_tac x=s in exI, rule_tac x=b in exI)
 apply (clarsimp; intro conjI)
 apply (clarsimp simp: sep_disj_prod_def sep_disj_fun_def select_def free_def zero_fun_def)
  apply (metis (mono_tags, lifting) someI)
 apply (rule prod_eqI; clarsimp simp: plus_prod_def plus_fun_def)
 apply (rule ext, clarsimp simp: plus_option_def split: option.splits)
 apply (clarsimp simp: zero_fun_def)
 apply (fastforce)
 apply (clarsimp simp: free_def select_def)
 apply (smt tfl_some)
 apply (clarsimp simp: free_def select_def)
 apply (smt tfl_some)
 apply (clarsimp simp: project_def to_flag_def)
 apply (rule_tac x=b in exI)
 apply (clarsimp simp: free_def select_def)
 apply (erule_tac x=p in allE)
 apply (clarsimp)
 apply (clarsimp simp: sep_conj_def maps_to_ex_def maps_to_def)
 apply (rule_tac x="[p \<mapsto> y]" in exI)
 apply (rule_tac x="s - [p \<mapsto> y] " in exI)
 apply (rule_tac x="b" in exI)
 apply (clarsimp simp: zero_fun_def sep_disj_prod_def sep_disj_fun_def plus_prod_def plus_fun_def)
 apply (intro conjI)
by auto
 
definition "swap_ptr p q = do {
                x <- get_ptr p;
                y <- get_ptr q;
                set_ptr q x;
                set_ptr p y
}"

lemma sep_conj_sep_impl_spec: "\<lbrakk>((Q -o R) \<and>* P) h; \<And>h. (Q -o R) h \<Longrightarrow> (P \<longrightarrow>* R') h\<rbrakk> \<Longrightarrow> R' h"
  by (metis (full_types)  sep_conj_sep_impl2)

method sep_invert = ((erule snake_sept_gal[rotated] | sep_erule (direct) sep_conj_sep_impl_spec),
                      sep_flatten?; sep_invert?)

method sep_lift_snake = match conclusion in "(_ \<leadsto>o _) s" for s :: "_ :: sep_algebra" \<Rightarrow> 
                  \<open>((match premises in I[thin]: "P s" for P \<Rightarrow>
                      \<open>abs_used P, rule sept_snake_gal[rotated,where s=s and Q=P, OF I]\<close>))\<close>

lemma sept_maps_to_ex_snake: 
 "(maps_to p y \<and>* R) h \<Longrightarrow> (\<And>s. R s \<Longrightarrow> R' s) \<Longrightarrow> (maps_to_ex p \<leadsto>o R') h"
 apply (drule sep_conj_impl[where Q'=R'], assumption, clarsimp)
 apply (sep_lift_snake)
 apply (erule sept_maps_to_ex)
done

lemma sept_maps_to_ex_snake': 
 "(maps_to_ex p  \<and>* R) h \<Longrightarrow> (\<And>s. R s \<Longrightarrow> R' s) \<Longrightarrow> (maps_to_ex p \<leadsto>o R') h"
 apply (drule sep_conj_impl[where Q'=R'], assumption, clarsimp)
 apply (sep_lift_snake)
 apply (erule sept_maps_to_ex')
done

lemma swap_ptr_validU: 
"\<lbrace><(maps_to p i \<and>* maps_to q j \<and>* R)>\<rbrace> swap_ptr p q 
 \<lbrace>\<lambda>_. < (maps_to p j \<and>* maps_to q i \<and>* R)>\<rbrace>u"
 apply (clarsimp simp: swap_ptr_def)
 apply (rule hoare_seq_extU | rule get_ptr_spU set_ptr_spU)+
 apply (rule hoare_chainU[OF set_ptr_spU], assumption)
 apply (erule projectE)
 apply (clarsimp)
 apply (sep_invert)
 by (sep_erule (direct) sept_maps_to_snake sept_maps_to_ex_snake | sep_lift |
        clarsimp simp: sep_conj_ac)+

definition "swap_ptr_heap_alloc p q = do {
                tmp <- new_ptr;
                move_ptr p tmp;
                move_ptr q p;
                move_ptr tmp q;
                delete_ptr tmp
}"

lemma swap_ptr_heap_alloc:
  "\<lbrace><(maps_to (p :: nat) v \<and>* maps_to q v')>\<rbrace> swap_ptr_heap_alloc p q 
   \<lbrace>\<lambda>_ . <(maps_to p v' \<and>* maps_to q v)> \<rbrace>u"
  apply (clarsimp simp: swap_ptr_heap_alloc_def )
  apply (sp sp: new_ptr_spU move_ptr_spU delete_ptr_spU)
  apply (erule projectE)
  apply (clarsimp)
  apply (sep_invert | clarsimp)+
  apply (case_tac "x=0"; simp)
   defer
   apply  ((sep_erule (direct) sept_maps_to_ex_snake' sept_maps_to_snake sept_maps_to_ex_snake | sep_lift |
        clarsimp simp: sep_conj_ac)+)[1]
  apply (subgoal_tac "\<exists>ptr. ptr \<noteq> p \<and> ptr \<noteq> q \<and> ptr \<noteq> 0")
   apply (clarsimp)
   apply (erule_tac x=ptr in allE)
   apply (clarsimp)
   apply (clarsimp simp: sep_conj_def maps_to_def maps_to_ex_def)
   apply (clarsimp simp: plus_prod_def)
   apply (drule_tac x=ptr in fun_cong)
   apply (clarsimp simp: plus_fun_def)
   apply (metis option.case_eq_if option.simps(3) plus_option_def)
  apply (rule_tac x="p + q + 1" in exI)
  apply (clarsimp)
  done

lemma move_ptr_validU:
  "\<lbrace>< (maps_to p v \<and>* maps_to p' v' \<and>* R)>\<rbrace> move_ptr p p' 
   \<lbrace>\<lambda>_ . <(maps_to p v \<and>* maps_to p' v \<and>* R)> \<rbrace>u"
 apply (rule hoare_chainU)
 apply (rule move_ptr_spU, assumption)
 apply (clarsimp)
 apply (erule projectE, clarsimp)
 apply (sep_invert)
 by (sep_erule (direct) sept_maps_to_snake sept_maps_to_ex_snake | sep_lift |
        clarsimp simp: sep_conj_ac)+

lemma sep_positive_nonerasure:
"(\<And>s s'. P s \<Longrightarrow> R (snd s') \<Longrightarrow> 
   snd s = 0 \<and> (\<forall>v. fst s v \<noteq> None \<longrightarrow>  snd s' v \<noteq> None)   ) \<Longrightarrow> 
   sept P (R o snd) s \<Longrightarrow> R (snd (s :: ('a,'b) abstract_ext'))" 
 apply (clarsimp simp: sept_def) 
 apply (atomize, erule_tac x="a" in allE, erule_tac x="b" in allE, erule allE, clarsimp)
 apply (drule mp, fastforce)
 apply (erule back_subst[where P=R], clarsimp)
 apply (clarsimp simp: sep_minus_def)
 apply (rule ext)
 apply (clarsimp simp: plus_fun_def)
 apply (clarsimp simp: plus_option_def minus_option_def zero_option_def split: option.splits)
  by (metis not_Some_eq)


end
