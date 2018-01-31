(*
 * Copyright 2014, General Dynamics C4 Systems
 *
 * This software may be distributed and modified according to the terms of
 * the GNU General Public License version 2. Note that NO WARRANTY is provided.
 * See "LICENSE_GPLv2.txt" for details.
 *
 * @TAG(GD_GPL)
 *)

theory TcbAcc_C
imports "../../lib/clib/Ctac"
begin

context kernel
begin

lemma ccorres_pre_threadGet:
  assumes cc: "\<And>rv. ccorres r xf (P rv) (P' rv) hs (g rv) c"
  shows   "ccorres r xf 
           (\<lambda>s. \<forall>tcb. ko_at' tcb p s \<longrightarrow> P (f tcb) s)
           ({s'. \<forall>tcb ctcb. cslift s' (tcb_ptr_to_ctcb_ptr p) = Some ctcb \<and> ctcb_relation tcb ctcb \<longrightarrow> s' \<in> P' (f tcb)})
           hs (threadGet f p >>= (\<lambda>rv. g rv)) c"
  apply (rule ccorres_guard_imp)
    apply (rule ccorres_symb_exec_l)
       defer
       apply wp[1]
      apply (rule tg_sp')
     apply simp
    apply assumption
   defer
   apply (rule ccorres_guard_imp)
     apply (rule cc)
    apply clarsimp
    apply (frule obj_at_ko_at')
    apply clarsimp
  apply assumption
  apply clarsimp
  apply (frule (1) obj_at_cslift_tcb)
  apply clarsimp
  done

lemma threadGet_eq:
  "ko_at' tcb thread s \<Longrightarrow> (f tcb, s) \<in> fst (threadGet f thread s)"
  unfolding threadGet_def
  apply (simp add: liftM_def in_monad)
  apply (rule exI [where x = tcb])
  apply simp
  apply (subst getObject_eq)
     apply simp
    apply (simp add: objBits_simps)
   apply assumption
  apply simp
  done

lemma get_tsType_ccorres [corres]:
  "ccorres (\<lambda>r r'. r' = thread_state_to_tsType r) ret__unsigned_' (tcb_at' thread)
           (UNIV \<inter> {s. thread_state_ptr_' s = Ptr &(tcb_ptr_to_ctcb_ptr thread\<rightarrow>[''tcbState_C''])}) []
  (getThreadState thread) (Call thread_state_ptr_get_tsType_'proc)"
  unfolding getThreadState_def 
  apply (rule ccorres_from_spec_modifies)
      apply (rule thread_state_ptr_get_tsType_spec)
     apply (rule thread_state_ptr_get_tsType_modifies)
    apply simp    
   apply (frule (1) obj_at_cslift_tcb)
   apply (clarsimp simp: typ_heap_simps)
  apply (frule (1) obj_at_cslift_tcb)
  apply (clarsimp simp: typ_heap_simps)
  apply (rule bexI [rotated, OF threadGet_eq], assumption)
  apply simp
  apply (erule ctcb_relation_thread_state_to_tsType)
  done

lemma threadGet_obj_at2:
  "\<lbrace>\<top>\<rbrace> threadGet f thread \<lbrace>\<lambda>v. obj_at' (\<lambda>t. f t = v) thread\<rbrace>"
  apply (rule hoare_post_imp)
   prefer 2
   apply (rule tg_sp')
  apply simp
  done
  
lemma register_from_H_less:
  "register_from_H hr < 19"
  by (cases hr, simp_all add: "StrictC'_register_defs")

lemma register_from_H_sless:
  "register_from_H hr <s 19"
  by (cases hr, simp_all add: "StrictC'_register_defs" word_sless_def word_sle_def)

lemma register_from_H_0_sle[simp]:
  "0 <=s register_from_H hr"
  using word_0_sle_from_less[OF order_less_le_trans] register_from_H_less
  by fastforce

lemma getRegister_ccorres [corres]:
  "ccorres (op =) ret__unsigned_long_' \<top>
             ({s. thread_' s = tcb_ptr_to_ctcb_ptr thread} \<inter> {s. reg_' s = register_from_H reg}) []
             (asUser thread (getRegister reg)) (Call getRegister_'proc)"  
  apply (unfold asUser_def)
  apply (rule ccorres_guard_imp)
    apply (rule ccorres_symb_exec_l [where Q="\<lambda>u. obj_at' (\<lambda>t. (atcbContextGet o tcbArch) t = u) thread" and
      Q'="\<lambda>rv. {s. thread_' s = tcb_ptr_to_ctcb_ptr thread} \<inter> {s. reg_' s = register_from_H reg}"])
       apply (rule ccorres_from_vcg)
       apply (rule allI, rule conseqPre)
        apply vcg
       apply clarsimp
       apply (drule (1) obj_at_cslift_tcb)
       apply (clarsimp simp: typ_heap_simps register_from_H_less register_from_H_sless)
       apply (clarsimp simp: getRegister_def typ_heap_simps)
       apply (rule_tac x = "((atcbContextGet o tcbArch) ko reg, \<sigma>)" in bexI [rotated])
        apply (simp add: in_monad' asUser_def select_f_def split_def)
        apply (subst arg_cong2 [where f = "op \<in>"])
          defer
          apply (rule refl)
         apply (erule threadSet_eq)
        apply (clarsimp simp: ctcb_relation_def ccontext_relation_def carch_tcb_relation_def)
       apply (wp threadGet_obj_at2)+
   apply simp
  apply simp
  apply (erule obj_atE')
  apply (clarsimp simp: projectKOs )
  apply (subst fun_upd_idem)
   apply (case_tac ko)
   apply clarsimp
  apply simp   
  done

lemma getRestartPC_ccorres [corres]:
  "ccorres (op =) ret__unsigned_long_' \<top> \<lbrace>\<acute>thread = tcb_ptr_to_ctcb_ptr thread\<rbrace> []
           (asUser thread getRestartPC) (Call getRestartPC_'proc)"
  unfolding getRestartPC_def
  apply (cinit')
   apply (rule ccorres_add_return2, ctac)
     apply (rule ccorres_return_C, simp+)[1]
    apply wp
   apply vcg
  apply (simp add: scast_id)
  done

lemma threadSet_corres_lemma:
  assumes spec: "\<forall>s. \<Gamma>\<turnstile> \<lbrace>s. P s\<rbrace> Call f {t. Q s t}"
  and      mod: "modifies_heap_spec f"
  and  rl: "\<And>\<sigma> x t ko. \<lbrakk>(\<sigma>, x) \<in> rf_sr; Q x t; x \<in> P'; ko_at' ko thread \<sigma>\<rbrakk>
             \<Longrightarrow> (\<sigma>\<lparr>ksPSpace := ksPSpace \<sigma>(thread \<mapsto> KOTCB (g ko))\<rparr>,
                  t\<lparr>globals := globals x\<lparr>t_hrs_' := t_hrs_' (globals t)\<rparr>\<rparr>) \<in> rf_sr"
  and  g:  "\<And>s x. \<lbrakk>tcb_at' thread s; x \<in> P'; (s, x) \<in> rf_sr\<rbrakk> \<Longrightarrow> P x"
  shows "ccorres dc xfdc (tcb_at' thread) P' [] (threadSet g thread) (Call f)"
  apply (rule ccorres_Call_call_for_vcg)
   apply (rule ccorres_from_vcg)
   apply (rule allI, rule conseqPre)   
   apply (rule HoarePartial.ProcModifyReturnNoAbr [where return' = "\<lambda>s t. t\<lparr> globals := globals s\<lparr>t_hrs_' := t_hrs_' (globals t) \<rparr>\<rparr>"])
     apply (rule HoarePartial.ProcSpecNoAbrupt [OF _ _ spec])
      apply (rule subset_refl)
     apply vcg
    prefer 2
    apply (rule mod)
   apply (clarsimp simp: mex_def meq_def)
  apply clarsimp
  apply (rule conjI)   
   apply (erule (2) g)
  apply clarsimp
   apply (frule obj_at_ko_at')
   apply clarsimp
   apply (rule bexI [rotated])
   apply (erule threadSet_eq)
   apply simp
  apply (rule_tac x1 = "t\<lparr>globals := globals x\<lparr>t_hrs_' := t_hrs_' (globals t)\<rparr>\<rparr>" in iffD1 [OF rf_sr_upd], simp_all)[1]
  apply (erule (3) rl)
  done


lemma threadSet_ccorres_lemma4:
  "\<lbrakk> \<And>s tcb. \<Gamma> \<turnstile> (Q s tcb) c {s'. (s \<lparr>ksPSpace := ksPSpace s(thread \<mapsto> injectKOS (F tcb))\<rparr>, s') \<in> rf_sr};
          \<And>s s' tcb tcb'. \<lbrakk> (s, s') \<in> rf_sr; P tcb; ko_at' tcb thread s;
                             cslift s' (tcb_ptr_to_ctcb_ptr thread) = Some tcb';
                             ctcb_relation tcb tcb'; P' s ; s' \<in> R\<rbrakk> \<Longrightarrow> s' \<in> Q s tcb \<rbrakk>
         \<Longrightarrow> ccorres dc xfdc (obj_at' (P :: tcb \<Rightarrow> bool) thread and P') R hs (threadSet F thread) c"
  apply (rule ccorres_from_vcg)
  apply (rule allI)
  apply (case_tac "obj_at' P thread \<sigma>")
   apply (drule obj_at_ko_at', clarsimp)
   apply (rule conseqPre, rule conseqPost)
      apply assumption
     apply clarsimp
     apply (rule rev_bexI, rule threadSet_eq)
      apply assumption
     apply simp
    apply simp
   apply clarsimp
   apply (drule(1) obj_at_cslift_tcb, clarsimp)
  apply simp
  apply (rule hoare_complete')
  apply (simp add: cnvalid_def nvalid_def) (* pretty *)
  done

lemmas threadSet_ccorres_lemma3 = threadSet_ccorres_lemma4[where R=UNIV]

lemmas threadSet_ccorres_lemma2
    = threadSet_ccorres_lemma3[where P'=\<top>]

lemma is_aligned_tcb_ptr_to_ctcb_ptr:
  "obj_at' (P :: tcb \<Rightarrow> bool) p s
     \<Longrightarrow> is_aligned (ptr_val (tcb_ptr_to_ctcb_ptr p)) 8"
  apply (clarsimp simp: obj_at'_def objBits_simps projectKOs
                        tcb_ptr_to_ctcb_ptr_def ctcb_offset_def)
  apply (erule aligned_add_aligned, simp_all add: word_bits_conv)
  apply (simp add: is_aligned_def)
  done

lemma sanitiseRegister_spec:
  "\<forall>s t v r. \<Gamma> \<turnstile> ({s} \<inter> \<lbrace>\<acute>v___unsigned_long = v\<rbrace> \<inter> \<lbrace>\<acute>reg = register_from_H r\<rbrace>)
                   Call sanitiseRegister_'proc
                 \<lbrace>\<acute>ret__unsigned_long = sanitiseRegister t r v\<rbrace>"
  apply vcg
  apply (auto simp: C_register_defs sanitiseRegister_def word_0_sle_from_less
             split: register.split)
  done

end

end
