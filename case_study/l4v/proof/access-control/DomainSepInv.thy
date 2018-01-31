(*
 * Copyright 2014, NICTA
 *
 * This software may be distributed and modified according to the terms of
 * the GNU General Public License version 2. Note that NO WARRANTY is provided.
 * See "LICENSE_GPLv2.txt" for details.
 *
 * @TAG(NICTA_GPL)
 *)

theory DomainSepInv
imports
  "Ipc_AC" (* for transfer_caps_loop_pres_dest lec_valid_cap' set_endpoint_get_tcb thread_set_tcb_fault_update_valid_mdb *)
  "../../lib/Monad_WP/wp/WPBang"
begin

context begin interpretation Arch . (*FIXME: arch_split*)

text {*
  We define and prove an invariant that is necessary to achieve domain
  separation on seL4. In its strongest form, we require that all IRQs, other than
  those for the timer, are inactive, and that no IRQControl or
  IRQHandler caps are present (to prevent any inactive IRQs from becoming
  active in the future).

  It always requires that there are no domain caps.
*}

text {* 
  When @{term irqs} is @{term False} we require that non-timer IRQs are off permanently.
*}
definition domain_sep_inv where
  "domain_sep_inv irqs st s \<equiv> 
    (\<forall> slot. \<not> cte_wp_at (op = DomainCap) slot s) \<and>
    (irqs \<or> (\<forall> irq slot. \<not> cte_wp_at (op = IRQControlCap) slot s
      \<and> \<not> cte_wp_at (op = (IRQHandlerCap irq)) slot s
      \<and> interrupt_states s irq \<noteq> IRQSignal
      \<and> interrupt_states s irq \<noteq> IRQReserved
      \<and> interrupt_states s = interrupt_states st))"

definition domain_sep_inv_cap where
  "domain_sep_inv_cap irqs cap \<equiv> case cap of
    IRQControlCap \<Rightarrow> irqs
  | IRQHandlerCap irq \<Rightarrow> irqs
  | DomainCap \<Rightarrow> False
  | _ \<Rightarrow> True"


lemma cte_wp_at_not_domain_sep_inv_cap:
  "cte_wp_at (not domain_sep_inv_cap irqs) slot s \<longleftrightarrow>
   ((irqs \<longrightarrow> False) \<and>
    (\<not> irqs \<longrightarrow> (cte_wp_at (op = IRQControlCap) slot s \<or>
                    (\<exists> irq. cte_wp_at (op = (IRQHandlerCap irq)) slot s)))
   )
   \<or> cte_wp_at (op = DomainCap) slot s"
  apply(rule iffI)
   apply(drule cte_wp_at_eqD)
   apply clarsimp
   apply(case_tac c, simp_all add: domain_sep_inv_cap_def pred_neg_def)
   apply(auto elim: cte_wp_at_weakenE split: if_splits)
  done

lemma domain_sep_inv_def2:
  "domain_sep_inv irqs st s =
    ((\<forall> slot. \<not> cte_wp_at (op = DomainCap) slot s) \<and>
    (irqs \<or> (\<forall> irq slot. \<not> cte_wp_at (op = IRQControlCap) slot s
                            \<and> \<not> cte_wp_at (op = (IRQHandlerCap irq)) slot s)) \<and>
    (irqs \<or> (\<forall> irq.
        interrupt_states s irq \<noteq> IRQSignal
        \<and> interrupt_states s irq \<noteq> IRQReserved
        \<and> interrupt_states s = interrupt_states st)))"
  apply(fastforce simp: domain_sep_inv_def)
  done

lemma domain_sep_inv_wp:
  assumes nctrl: "\<And>slot. \<lbrace>(\<lambda>s. \<not> cte_wp_at (not domain_sep_inv_cap irqs) slot s) and P\<rbrace> f \<lbrace>\<lambda>_ s. \<not> cte_wp_at (not domain_sep_inv_cap irqs) slot s\<rbrace>"
  assumes irq_pres: "\<And>P. \<not> irqs \<Longrightarrow> \<lbrace>(\<lambda>s. P (interrupt_states s)) and R\<rbrace> f \<lbrace>\<lambda>_ s. P (interrupt_states s)\<rbrace>"
  shows "\<lbrace>domain_sep_inv irqs st and P and (\<lambda>s. irqs \<or> R s)\<rbrace> f \<lbrace>\<lambda>_. domain_sep_inv irqs st\<rbrace>"
  apply (clarsimp simp: domain_sep_inv_def2 valid_def)
  apply (subst conj_assoc[symmetric])
  apply (rule conjI)
   apply (rule conjI)
    apply(intro allI)
    apply(erule use_valid[OF _ hoare_strengthen_post[OF nctrl]])
     apply(fastforce simp: cte_wp_at_not_domain_sep_inv_cap)
    apply(fastforce simp: cte_wp_at_not_domain_sep_inv_cap)
   apply(fastforce elim!: use_valid[OF _ hoare_strengthen_post[OF nctrl]] simp: cte_wp_at_not_domain_sep_inv_cap)
  apply(case_tac "irqs")
   apply blast
  apply(rule disjI2)
  apply simp
  apply(intro allI conjI)
    apply(erule_tac P1="\<lambda>x. x irq \<noteq> IRQSignal" in use_valid[OF _ irq_pres], assumption)
    apply blast
   apply(erule use_valid[OF _ irq_pres], assumption)
   apply blast
  apply(erule use_valid[OF _ irq_pres], assumption)
  apply blast
  done

lemma domain_sep_inv_triv:
  assumes cte_pres: "\<And>P slot. \<lbrace>\<lambda>s. \<not> cte_wp_at P slot s\<rbrace> f \<lbrace>\<lambda>_ s. \<not> cte_wp_at P slot s\<rbrace>"
  assumes irq_pres: "\<And>P. \<lbrace>\<lambda>s. P (interrupt_states s)\<rbrace> f \<lbrace>\<lambda>_ s. P (interrupt_states s)\<rbrace>"
  shows
  "\<lbrace>domain_sep_inv irqs st\<rbrace> f \<lbrace>\<lambda>_. domain_sep_inv irqs st\<rbrace>"
  apply(rule domain_sep_inv_wp[where P="\<top>" and R="\<top>", simplified])
  apply(rule cte_pres, rule irq_pres)
  done

(* FIXME: clagged from FinalCaps *)
lemma set_object_wp:
  "\<lbrace> \<lambda> s. P (s\<lparr>kheap := kheap s(ptr \<mapsto> obj)\<rparr>) \<rbrace>
   set_object ptr obj
   \<lbrace> \<lambda>_. P \<rbrace>"
  unfolding set_object_def
  apply (wp)
  done

(* FIXME: following 3 lemmas clagged from FinalCaps *)
lemma set_cap_neg_cte_wp_at_other_helper':
  "\<lbrakk>oslot \<noteq> slot;
    ko_at (TCB x) (fst oslot) s;
    tcb_cap_cases (snd oslot) = Some (ogetF, osetF, orestr);
        kheap
         (s\<lparr>kheap := kheap s(fst oslot \<mapsto>
              TCB (osetF (\<lambda> x. cap) x))\<rparr>)
         (fst slot) =
        Some (TCB tcb);
        tcb_cap_cases (snd slot) = Some (getF, setF, restr);
        P (getF tcb)\<rbrakk> \<Longrightarrow>
   cte_wp_at P slot s"
  apply(case_tac "fst oslot = fst slot")
   apply(rule cte_wp_at_tcbI)
     apply(fastforce split: if_splits simp: obj_at_def)
    apply assumption
   apply(fastforce split: if_splits simp: tcb_cap_cases_def dest: prod_eqI)
  apply(rule cte_wp_at_tcbI)
    apply(fastforce split: if_splits simp: obj_at_def)
   apply assumption
  apply assumption
  done

lemma set_cap_neg_cte_wp_at_other_helper:
  "\<lbrakk>\<not> cte_wp_at P slot s; oslot \<noteq> slot; ko_at (TCB x) (fst oslot) s;
     tcb_cap_cases (snd oslot) = Some (getF, setF, restr)\<rbrakk>  \<Longrightarrow>
   \<not> cte_wp_at P slot (s\<lparr>kheap := kheap s(fst oslot \<mapsto> TCB (setF (\<lambda> x. cap) x))\<rparr>)"
  apply(rule notI)
  apply(erule cte_wp_atE)
   apply(fastforce elim: notE intro: cte_wp_at_cteI split: if_splits)
  apply(fastforce elim: notE intro: set_cap_neg_cte_wp_at_other_helper')
  done


lemma set_cap_neg_cte_wp_at_other:
  "oslot \<noteq> slot \<Longrightarrow> \<lbrace> \<lambda> s. \<not> (cte_wp_at P slot s)\<rbrace> set_cap cap oslot \<lbrace> \<lambda>rv s. \<not>  (cte_wp_at P slot s) \<rbrace>"
  apply(rule hoare_pre)
  unfolding set_cap_def
  apply(wp set_object_wp get_object_wp | wpc | simp add: split_def)+
  apply(intro allI impI conjI)
       apply(rule notI)
       apply(erule cte_wp_atE)
        apply (fastforce split: if_splits dest: prod_eqI elim: notE intro: cte_wp_at_cteI simp: obj_at_def)
       apply(fastforce split: if_splits elim: notE intro: cte_wp_at_tcbI)
      apply(auto dest: set_cap_neg_cte_wp_at_other_helper)
  done

lemma set_cap_neg_cte_wp_at:
  "\<lbrace>(\<lambda>s. \<not> cte_wp_at P slot s) and K (\<not> P capa)\<rbrace>
   set_cap capa slota
    \<lbrace>\<lambda>_ s. \<not> cte_wp_at P slot s\<rbrace>"
  apply(case_tac "slot = slota")
   apply simp
   apply(simp add: set_cap_def set_object_def)
   apply(rule hoare_pre)
    apply(wp get_object_wp | wpc)+
   apply(fastforce elim: cte_wp_atE intro: cte_wp_at_cteI cte_wp_at_tcbI)
  apply(rule hoare_pre)
   apply(rule set_cap_neg_cte_wp_at_other, simp+)
  done

lemma domain_sep_inv_cap_IRQControlCap:
  "\<lbrakk>domain_sep_inv_cap irqs cap; \<not> irqs\<rbrakk> \<Longrightarrow> cap \<noteq> IRQControlCap"
  apply(auto simp: domain_sep_inv_cap_def)
  done

lemma domain_sep_inv_cap_IRQHandlerCap:
  "\<lbrakk>domain_sep_inv_cap irqs cap; \<not> irqs\<rbrakk> \<Longrightarrow> cap \<noteq> IRQHandlerCap irq"
  apply(auto simp: domain_sep_inv_cap_def)
  done

lemma set_cap_domain_sep_inv:
  "\<lbrace>domain_sep_inv irqs st and K (domain_sep_inv_cap irqs cap)\<rbrace>
   set_cap cap slot
   \<lbrace>\<lambda>_. domain_sep_inv irqs st\<rbrace>"
  apply(rule hoare_gen_asm)
  apply(rule hoare_pre)
   apply(rule domain_sep_inv_wp)
   apply(wp set_cap_neg_cte_wp_at | simp add: pred_neg_def | blast)+
  done

lemma cte_wp_at_domain_sep_inv_cap:
  "\<lbrakk>domain_sep_inv irqs st s; cte_wp_at (op = cap) slot s\<rbrakk> \<Longrightarrow> domain_sep_inv_cap irqs cap"
  apply(case_tac slot)
  apply(auto simp: domain_sep_inv_def domain_sep_inv_cap_def split: cap.splits)
  done

lemma weak_derived_irq_handler:
  "weak_derived (IRQHandlerCap irq) cap \<Longrightarrow> cap = (IRQHandlerCap irq)"
  apply(auto simp: weak_derived_def copy_of_def same_object_as_def split: cap.splits if_splits arch_cap.splits)
  done

(* FIXME: move to CSpace_AI *)
lemma weak_derived_DomainCap:
  "weak_derived c' c \<Longrightarrow> (c' = cap.DomainCap) = (c = cap.DomainCap)"
  apply (clarsimp simp: weak_derived_def)
  apply (erule disjE)
   apply (clarsimp simp: copy_of_def split: if_split_asm)
   apply (auto simp: is_cap_simps same_object_as_def
              split: cap.splits arch_cap.splits)[1]
  apply simp
  done

lemma cte_wp_at_weak_derived_domain_sep_inv_cap:
  "\<lbrakk>domain_sep_inv irqs st s; cte_wp_at (weak_derived cap) slot s\<rbrakk> \<Longrightarrow> domain_sep_inv_cap irqs cap"
  apply (cases slot)
  apply (force simp: domain_sep_inv_def domain_sep_inv_cap_def
              split: cap.splits
               dest: cte_wp_at_eqD weak_derived_irq_handler weak_derived_DomainCap)
  done

lemma is_derived_IRQHandlerCap:
  "is_derived m src (IRQHandlerCap irq) cap \<Longrightarrow> (cap = IRQHandlerCap irq)"
  apply(clarsimp simp: is_derived_def)
  apply(case_tac cap, simp_all add: is_cap_simps cap_master_cap_def)
  done

(* FIXME: move to CSpace_AI *)
lemma DomainCap_is_derived:
  "is_derived m src cap.DomainCap cap \<Longrightarrow> cap = DomainCap"
by (auto simp: is_derived_def is_reply_cap_def is_pg_cap_def is_master_reply_cap_def cap_master_cap_def split: cap.splits)

lemma cte_wp_at_is_derived_domain_sep_inv_cap:
  "\<lbrakk>domain_sep_inv irqs st s; cte_wp_at (is_derived (cdt s) slot cap) slot s\<rbrakk> \<Longrightarrow> domain_sep_inv_cap irqs cap"
apply (cases slot)
apply (fastforce simp: domain_sep_inv_def domain_sep_inv_cap_def
                split: cap.splits
                 dest: cte_wp_at_eqD DomainCap_is_derived is_derived_IRQHandlerCap)
done

lemma domain_sep_inv_exst_update[simp]:
  "domain_sep_inv irqs st (trans_state f s) = domain_sep_inv irqs st s"
  apply(simp add: domain_sep_inv_def)
  done

lemma domain_sep_inv_is_original_cap_update[simp]:
  "domain_sep_inv irqs st (s\<lparr>is_original_cap := X\<rparr>) = domain_sep_inv irqs st s"
  apply(simp add: domain_sep_inv_def)
  done

lemma domain_sep_inv_cdt_update[simp]:
  "domain_sep_inv irqs st (s\<lparr>cdt := X\<rparr>) = domain_sep_inv irqs st s"
  apply(simp add: domain_sep_inv_def)
  done

crunch domain_sep_inv[wp]: update_cdt "domain_sep_inv irqs st"

lemma set_untyped_cap_as_full_domain_sep_inv[wp]:
  "\<lbrace>domain_sep_inv irqs st\<rbrace> set_untyped_cap_as_full a b c \<lbrace>\<lambda>_. domain_sep_inv irqs st\<rbrace>"
  apply(clarsimp simp: set_untyped_cap_as_full_def)
  apply(rule hoare_pre)
   apply(rule set_cap_domain_sep_inv)
  apply(case_tac a, simp_all add: domain_sep_inv_cap_def)
  done

lemma cap_insert_domain_sep_inv:
  "\<lbrace> domain_sep_inv irqs st and (\<lambda>s. cte_wp_at (is_derived (cdt s) slot cap) slot s) \<rbrace>
  cap_insert cap slot dest_slot
   \<lbrace> \<lambda>_. domain_sep_inv irqs st \<rbrace>"
  apply(simp add: cap_insert_def)
  apply(wp set_cap_domain_sep_inv get_cap_wp set_original_wp dxo_wp_weak | simp split del: if_split)+
  apply(blast dest: cte_wp_at_is_derived_domain_sep_inv_cap)
  done

lemma domain_sep_inv_cap_NullCap[simp]:
  "domain_sep_inv_cap irqs NullCap"
  apply(simp add: domain_sep_inv_cap_def)
  done

lemma cap_move_domain_sep_inv:
  "\<lbrace> domain_sep_inv irqs st and (\<lambda>s. cte_wp_at (weak_derived cap) slot s) \<rbrace>
  cap_move cap slot dest_slot
   \<lbrace> \<lambda>_. domain_sep_inv irqs st \<rbrace>"
  apply(simp add: cap_move_def)
  apply(wp set_cap_domain_sep_inv get_cap_wp set_original_wp dxo_wp_weak | simp split del: if_split | blast dest: cte_wp_at_weak_derived_domain_sep_inv_cap)+
  done

lemma domain_sep_inv_machine_state_update[simp]:
  "domain_sep_inv irqs st (s\<lparr>machine_state := X\<rparr>) = domain_sep_inv irqs st s"
  apply(simp add: domain_sep_inv_def)
  done

lemma set_irq_state_domain_sep_inv:
  "\<lbrace>domain_sep_inv irqs st and (\<lambda>s. stt = interrupt_states s irq)\<rbrace>
   set_irq_state stt irq
   \<lbrace>\<lambda>_. domain_sep_inv irqs st\<rbrace>"
  apply(simp add: set_irq_state_def)
  apply(wp | simp add: do_machine_op_def | wpc)+
  done

lemma deleted_irq_handler_domain_sep_inv:
  "\<lbrace>domain_sep_inv irqs st and K irqs\<rbrace> deleted_irq_handler a \<lbrace>\<lambda>_. domain_sep_inv irqs st\<rbrace>"
  apply(rule hoare_gen_asm)
  apply(simp add: deleted_irq_handler_def)
  apply(simp add: set_irq_state_def)
  apply wp
    apply(rule domain_sep_inv_triv, wp+)
  apply(simp add: domain_sep_inv_def)
  done

lemma empty_slot_domain_sep_inv:
  "\<lbrace>\<lambda>s. domain_sep_inv irqs st s \<and> (\<not> irqs \<longrightarrow> b = None)\<rbrace>
   empty_slot a b
   \<lbrace>\<lambda>_ s. domain_sep_inv irqs st s\<rbrace>"
  unfolding empty_slot_def
  by (wpsimp wp: get_cap_wp set_cap_domain_sep_inv set_original_wp dxo_wp_weak static_imp_wp
                 deleted_irq_handler_domain_sep_inv)

lemma set_endpoint_neg_cte_wp_at[wp]:
  "\<lbrace>\<lambda>s. \<not> cte_wp_at P slot s\<rbrace> set_endpoint a b \<lbrace>\<lambda>_ s. \<not> cte_wp_at P slot s\<rbrace>"
  apply(simp add: set_endpoint_def)
  apply(wp set_object_wp get_object_wp | simp)+
  apply(case_tac "a = fst slot")
   apply(clarsimp split: kernel_object.splits)
   apply(fastforce elim: cte_wp_atE simp: obj_at_def)
  apply(fastforce elim: cte_wp_atE intro: cte_wp_at_cteI cte_wp_at_tcbI)
  done

lemma set_notification_neg_cte_wp_at[wp]:
  "\<lbrace>\<lambda>s. \<not> cte_wp_at P slot s\<rbrace> set_notification a b \<lbrace>\<lambda>_ s. \<not> cte_wp_at P slot s\<rbrace>"
  apply(simp add: set_notification_def)
  apply(wp set_object_wp get_object_wp | simp)+
  apply(case_tac "a = fst slot")
   apply(clarsimp split: kernel_object.splits)
   apply(fastforce elim: cte_wp_atE simp: obj_at_def)
  apply(fastforce elim: cte_wp_atE intro: cte_wp_at_cteI cte_wp_at_tcbI)
  done

crunch domain_sep_inv[wp]: set_endpoint "domain_sep_inv irqs st"
  (wp: domain_sep_inv_triv)

crunch domain_sep_inv[wp]: set_notification "domain_sep_inv irqs st"
  (wp: domain_sep_inv_triv)

lemma set_thread_state_neg_cte_wp_at[wp]:
  "\<lbrace>\<lambda>s. \<not> cte_wp_at P slot s\<rbrace> set_thread_state a b \<lbrace>\<lambda>_ s. \<not> cte_wp_at P slot s\<rbrace>"
  apply(simp add: set_thread_state_def)
  apply(wp set_object_wp get_object_wp dxo_wp_weak| simp)+
  apply(case_tac "a = fst slot")
   apply(clarsimp split: kernel_object.splits)
   apply(erule notE)
   apply(erule cte_wp_atE)
    apply(fastforce simp: obj_at_def)
   apply(drule get_tcb_SomeD)
   apply(rule cte_wp_at_tcbI)
     apply(simp)
    apply assumption
   apply (fastforce simp: tcb_cap_cases_def split: if_splits)
  apply(fastforce elim: cte_wp_atE intro: cte_wp_at_cteI cte_wp_at_tcbI)
  done

lemma set_bound_notification_neg_cte_wp_at[wp]:
  "\<lbrace>\<lambda>s. \<not> cte_wp_at P slot s\<rbrace> set_bound_notification a b \<lbrace>\<lambda>_ s. \<not> cte_wp_at P slot s\<rbrace>"
  apply(simp add: set_bound_notification_def)
  apply(wp set_object_wp get_object_wp dxo_wp_weak| simp)+
  apply(case_tac "a = fst slot")
   apply(clarsimp split: kernel_object.splits)
   apply(erule notE)
   apply(erule cte_wp_atE)
    apply(fastforce simp: obj_at_def)
   apply(drule get_tcb_SomeD)
   apply(rule cte_wp_at_tcbI)
     apply(simp)
    apply assumption
   apply (fastforce simp: tcb_cap_cases_def split: if_splits)
  apply(fastforce elim: cte_wp_atE intro: cte_wp_at_cteI cte_wp_at_tcbI)
  done

crunch domain_sep_inv[wp]: set_thread_state, set_bound_notification, get_bound_notification "domain_sep_inv irqs st"
  (wp: domain_sep_inv_triv)

lemma thread_set_tcb_fault_update_neg_cte_wp_at[wp]:
  "\<lbrace>\<lambda>s. \<not> cte_wp_at P slot s\<rbrace>
   thread_set (tcb_fault_update blah) param_a
   \<lbrace>\<lambda>_ s. \<not> cte_wp_at P slot s\<rbrace>"
  apply(simp add: thread_set_def)
  apply(wp set_object_wp get_object_wp | simp)+
  apply(case_tac "param_a = fst slot")
   apply(clarsimp split: kernel_object.splits)
   apply(erule notE)
   apply(erule cte_wp_atE)
    apply(fastforce simp: obj_at_def)
   apply(drule get_tcb_SomeD)
   apply(rule cte_wp_at_tcbI)
     apply(simp)
    apply assumption
   apply (fastforce simp: tcb_cap_cases_def split: if_splits)
  apply(fastforce elim: cte_wp_atE intro: cte_wp_at_cteI cte_wp_at_tcbI)
  done

lemma thread_set_tcb_fault_update_domain_sep_inv[wp]:
  "\<lbrace>domain_sep_inv irqs st\<rbrace>
   thread_set (tcb_fault_update blah) param_a
   \<lbrace>\<lambda>_. domain_sep_inv irqs st\<rbrace>"
  apply(wp domain_sep_inv_triv)
  done

crunch domain_sep_inv[wp]: cap_delete_one "domain_sep_inv irqs st"
  (wp: mapM_x_wp' hoare_unless_wp dxo_wp_weak ignore: tcb_sched_action reschedule_required simp: crunch_simps)

lemma reply_cancel_ipc_domain_sep_inv[wp]:
  "\<lbrace>domain_sep_inv irqs st\<rbrace>
   reply_cancel_ipc t
   \<lbrace>\<lambda>_. domain_sep_inv irqs st\<rbrace>"
  apply(simp add: reply_cancel_ipc_def)
  apply (wp select_wp)
  apply(rule hoare_strengthen_post[OF thread_set_tcb_fault_update_domain_sep_inv])
  apply auto
  done

lemma domain_sep_inv_arch_state_update[simp]:
  "domain_sep_inv irqs st (s\<lparr>arch_state := blah\<rparr>) = domain_sep_inv irqs st s"
  apply(simp add: domain_sep_inv_def)
  done

lemma set_pt_neg_cte_wp_at[wp]:
  "\<lbrace>\<lambda>s. \<not> cte_wp_at P slot s\<rbrace>
   set_pt ptr pt
   \<lbrace>\<lambda>_ s. \<not> cte_wp_at P slot s\<rbrace>"
  unfolding set_pt_def
  apply(wp set_object_wp get_object_wp | simp)+
  apply(case_tac "ptr = fst slot")
   apply(clarsimp split: kernel_object.splits)
   apply(fastforce elim: cte_wp_atE simp: obj_at_def)
  apply(fastforce elim: cte_wp_atE intro: cte_wp_at_cteI cte_wp_at_tcbI)
  done

crunch domain_sep_inv[wp]: set_pt "domain_sep_inv irqs st"
  (wp: domain_sep_inv_triv)

lemma set_pd_neg_cte_wp_at[wp]:
  "\<lbrace>\<lambda>s. \<not> cte_wp_at P slot s\<rbrace>
   set_pd ptr pt
   \<lbrace>\<lambda>_ s. \<not> cte_wp_at P slot s\<rbrace>"
  unfolding set_pd_def
  apply(wp set_object_wp get_object_wp | simp)+
  apply(case_tac "ptr = fst slot")
   apply(clarsimp split: kernel_object.splits)
   apply(fastforce elim: cte_wp_atE simp: obj_at_def)
  apply(fastforce elim: cte_wp_atE intro: cte_wp_at_cteI cte_wp_at_tcbI)
  done

crunch domain_sep_inv[wp]: set_pd "domain_sep_inv irqs st"
  (wp: domain_sep_inv_triv)

lemma set_asid_pool_neg_cte_wp_at[wp]:
  "\<lbrace>\<lambda>s. \<not> cte_wp_at P slot s\<rbrace>
   set_asid_pool ptr pt
   \<lbrace>\<lambda>_ s. \<not> cte_wp_at P slot s\<rbrace>"
  unfolding set_asid_pool_def
  apply(wp set_object_wp get_object_wp | simp)+
  apply(case_tac "ptr = fst slot")
   apply(clarsimp split: kernel_object.splits)
   apply(fastforce elim: cte_wp_atE simp: obj_at_def)
  apply(fastforce elim: cte_wp_atE intro: cte_wp_at_cteI cte_wp_at_tcbI)
  done

crunch domain_sep_inv[wp]: set_asid_pool "domain_sep_inv irqs st"
  (wp: domain_sep_inv_triv)


crunch domain_sep_inv[wp]: finalise_cap "domain_sep_inv irqs st"
  (wp: crunch_wps dxo_wp_weak simp: crunch_simps ignore: set_object tcb_sched_action)

lemma finalise_cap_domain_sep_inv_cap:
  "\<lbrace>\<lambda>s. domain_sep_inv_cap irqs cap\<rbrace> finalise_cap cap b \<lbrace>\<lambda>rv s. domain_sep_inv_cap irqs (fst rv)\<rbrace>"
  including no_pre
  apply(case_tac cap)
            apply(wp | simp add: o_def split del: if_split  split: cap.splits arch_cap.splits | fastforce split: if_splits simp: domain_sep_inv_cap_def)+
      apply(rule hoare_pre, wp, fastforce)
     apply(rule hoare_pre, simp, wp, fastforce simp: domain_sep_inv_cap_def)
  apply(simp add: arch_finalise_cap_def)
  apply(rule hoare_pre)
   apply(wpc | wp | simp)+
  done

lemma get_cap_domain_sep_inv_cap:
  "\<lbrace>domain_sep_inv irqs st\<rbrace> get_cap cap \<lbrace>\<lambda>rv s. domain_sep_inv_cap irqs rv\<rbrace>"
  apply(wp get_cap_wp)
  apply(blast dest: cte_wp_at_domain_sep_inv_cap)
  done

crunch domain_sep_inv[wp]: cap_swap_for_delete "domain_sep_inv irqs st"
  (wp: get_cap_domain_sep_inv_cap dxo_wp_weak simp: crunch_simps ignore: cap_swap_ext)

lemma finalise_cap_returns_None:
  "\<lbrace>\<lambda>s. domain_sep_inv_cap irqs cap\<rbrace>
   finalise_cap cap b
   \<lbrace>\<lambda>rv s. \<not> irqs \<longrightarrow> snd rv = None\<rbrace>"
  apply(case_tac cap)
  apply(simp add: o_def split del: if_split | wp | fastforce simp: domain_sep_inv_cap_def | rule hoare_pre)+
  done

lemma rec_del_domain_sep_inv':
  notes drop_spec_valid[wp_split del] drop_spec_validE[wp_split del]
         rec_del.simps[simp del]
  shows
  "s \<turnstile> \<lbrace> domain_sep_inv irqs st\<rbrace>
     (rec_del call)
   \<lbrace>\<lambda> a s. (case call of (FinaliseSlotCall x y) \<Rightarrow> (y \<or> fst a) \<longrightarrow> \<not> irqs \<longrightarrow> snd a = None | _ \<Rightarrow> True) \<and> domain_sep_inv irqs st s\<rbrace>,\<lbrace>\<lambda>_. domain_sep_inv irqs st\<rbrace>"
  proof (induct s arbitrary: rule: rec_del.induct, simp_all only: rec_del_fails hoare_fail_any)
  case (1 slot exposed s) show ?case
    apply(simp add: split_def rec_del.simps)
    apply(wp empty_slot_domain_sep_inv drop_spec_validE[OF returnOk_wp] drop_spec_validE[OF liftE_wp] | simp)+
    apply(rule spec_strengthen_postE[OF "1.hyps"])
    apply fastforce
    done
  next
  case (2 slot exposed s) show ?case
    apply(simp add: rec_del.simps split del: if_split)
    apply(rule hoare_pre_spec_validE)
     apply(wp drop_spec_validE[OF returnOk_wp] drop_spec_validE[OF liftE_wp] set_cap_domain_sep_inv
          |simp add: split_def split del: if_split)+
           apply(rule spec_strengthen_postE)
            apply(rule "2.hyps", fastforce+)
          apply(rule drop_spec_validE, (wp preemption_point_inv| simp)+)[1]
         apply simp
         apply(rule spec_strengthen_postE)
          apply(rule "2.hyps", fastforce+)
         apply(wp  finalise_cap_domain_sep_inv_cap get_cap_wp
                   finalise_cap_returns_None
                   drop_spec_validE[OF liftE_wp] set_cap_domain_sep_inv
               |simp add: without_preemption_def split del: if_split
               |wp_once hoare_drop_imps)+
    apply(blast dest: cte_wp_at_domain_sep_inv_cap)
    done
  next
  case (3 ptr bits n slot s) show ?case
    apply(simp add: rec_del.simps)
    apply (wp drop_spec_validE[OF returnOk_wp] drop_spec_validE[OF liftE_wp])
    apply(rule hoare_pre_spec_validE)
    apply (wp drop_spec_validE[OF assertE_wp])
    apply(fastforce)
    done
  next
  case (4 ptr bits n slot s) show ?case
    apply(simp add: rec_del.simps)
    apply (wp drop_spec_validE[OF returnOk_wp] drop_spec_validE[OF liftE_wp] set_cap_domain_sep_inv
              drop_spec_validE[OF assertE_wp] get_cap_wp | simp add: without_preemption_def)+
    apply (rule spec_strengthen_postE[OF "4.hyps"])
     apply(simp add: returnOk_def return_def)
    apply(clarsimp simp: domain_sep_inv_cap_def)
    done
  qed

lemma rec_del_domain_sep_inv:
  "\<lbrace> domain_sep_inv irqs st\<rbrace>
     (rec_del call)
   \<lbrace>\<lambda>_. domain_sep_inv irqs st\<rbrace>,\<lbrace>\<lambda>_. domain_sep_inv irqs st\<rbrace>"
  apply(rule use_spec)
  apply(rule spec_strengthen_postE[OF rec_del_domain_sep_inv'])
  by fastforce

crunch domain_sep_inv[wp]: cap_delete "domain_sep_inv irqs st"

lemma preemption_point_domain_sep_inv[wp]:
  "\<lbrace>domain_sep_inv irqs st\<rbrace> preemption_point \<lbrace>\<lambda>_. domain_sep_inv irqs st\<rbrace>"
  by (wp preemption_point_inv | simp)+

lemma cap_revoke_domain_sep_inv':
  notes drop_spec_valid[wp_split del] drop_spec_validE[wp_split del]
  shows
  "s \<turnstile> \<lbrace> domain_sep_inv irqs st\<rbrace>
   cap_revoke slot
   \<lbrace> \<lambda>_. domain_sep_inv irqs st\<rbrace>, \<lbrace> \<lambda>_. domain_sep_inv irqs st\<rbrace>"
  proof(induct rule: cap_revoke.induct[where ?a1.0=s])
  case (1 slot s)
  show ?case
  apply(subst cap_revoke.simps)
  apply(rule hoare_pre_spec_validE)
   apply (wp "1.hyps")
           apply(wp spec_valid_conj_liftE2 | simp)+
           apply(wp drop_spec_validE[OF valid_validE[OF preemption_point_domain_sep_inv]]
                    drop_spec_validE[OF valid_validE[OF cap_delete_domain_sep_inv]]
                    drop_spec_validE[OF assertE_wp] drop_spec_validE[OF returnOk_wp]
                    drop_spec_validE[OF liftE_wp] select_wp
                | simp | wp_once hoare_drop_imps)+
  done
  qed

lemmas cap_revoke_domain_sep_inv[wp] = use_spec(2)[OF cap_revoke_domain_sep_inv']

(* FIXME: clagged from FinalCaps *)
lemma cap_move_cte_wp_at_other:
  "\<lbrace> cte_wp_at P slot and K (slot \<noteq> dest_slot \<and> slot \<noteq> src_slot) \<rbrace>
   cap_move cap src_slot dest_slot
   \<lbrace> \<lambda>_. cte_wp_at P slot \<rbrace>"
  unfolding cap_move_def
  apply (rule hoare_pre)
   apply (wp set_cdt_cte_wp_at set_cap_cte_wp_at' dxo_wp_weak static_imp_wp | simp)+
  done

(* FIXME: clagged from FinalCaps *)
lemma cte_wp_at_weak_derived_ReplyCap:
  "cte_wp_at (op = (ReplyCap x False)) slot s
       \<Longrightarrow> cte_wp_at (weak_derived (ReplyCap x False)) slot s"
  apply(erule cte_wp_atE)
   apply(rule cte_wp_at_cteI)
      apply assumption
     apply assumption
    apply assumption
   apply simp
  apply(rule cte_wp_at_tcbI)
  apply auto
  done

lemma thread_set_tcb_registers_caps_merge_default_tcb_neg_cte_wp_at[wp]:
  "\<lbrace>\<lambda>s. \<not> cte_wp_at P slot s\<rbrace>
   thread_set (tcb_registers_caps_merge default_tcb) word
   \<lbrace>\<lambda>_ s. \<not> cte_wp_at P slot s\<rbrace>"
  unfolding thread_set_def
  apply(wp set_object_wp | simp)+
  apply(case_tac "word = fst slot")
   apply(clarsimp split: kernel_object.splits)
   apply(erule notE)
   apply(erule cte_wp_atE)
    apply(fastforce simp: obj_at_def)
   apply(drule get_tcb_SomeD)
   apply(rule cte_wp_at_tcbI)
     apply(simp)
    apply assumption
   apply (clarsimp simp: tcb_cap_cases_def tcb_registers_caps_merge_def split: if_splits)
  apply(fastforce elim: cte_wp_atE intro: cte_wp_at_cteI cte_wp_at_tcbI)
  done

lemma thread_set_tcb_registers_caps_merge_default_tcb_domain_sep_inv[wp]:
  "\<lbrace>domain_sep_inv irqs st\<rbrace>
   thread_set (tcb_registers_caps_merge default_tcb) word
   \<lbrace>\<lambda>_. domain_sep_inv irqs st\<rbrace>"
  apply(wp domain_sep_inv_triv)
  done

lemma cancel_badged_sends_domain_sep_inv[wp]:
  "\<lbrace>domain_sep_inv irqs st\<rbrace>
   cancel_badged_sends epptr badge
   \<lbrace>\<lambda>rv. domain_sep_inv irqs st\<rbrace>"
  apply(simp add: cancel_badged_sends_def)
  apply(rule hoare_pre)
   apply(wp dxo_wp_weak mapM_wp | wpc | simp add: filterM_mapM | rule subset_refl | wp_once hoare_drop_imps)+
   done

crunch domain_sep_inv[wp]: finalise_slot "domain_sep_inv irqs st"

lemma invoke_cnode_domain_sep_inv:
  "\<lbrace> domain_sep_inv irqs st and valid_cnode_inv ci\<rbrace>
   invoke_cnode ci
   \<lbrace>\<lambda>_. domain_sep_inv irqs st\<rbrace>"
  unfolding invoke_cnode_def
  apply(case_tac ci)
        apply(wp cap_insert_domain_sep_inv cap_move_domain_sep_inv | simp split del: if_split)+
    apply(rule hoare_pre)
     apply(wp cap_move_domain_sep_inv cap_move_cte_wp_at_other get_cap_wp | simp | blast dest: cte_wp_at_weak_derived_domain_sep_inv_cap | wpc)+
   apply(fastforce dest:  cte_wp_at_weak_derived_ReplyCap)
  apply(wp | simp | wpc | rule hoare_pre)+
  done

lemma create_cap_domain_sep_inv[wp]:
  "\<lbrace> domain_sep_inv irqs st\<rbrace>
   create_cap tp sz p dev slot
   \<lbrace> \<lambda>_. domain_sep_inv irqs st\<rbrace>"
  apply(simp add: create_cap_def)
  apply(rule hoare_pre)
  apply(wp set_cap_domain_sep_inv dxo_wp_weak | wpc | simp)+
  apply clarsimp
  apply(case_tac tp, simp_all add: domain_sep_inv_cap_def)
  done

lemma detype_interrupts_states[simp]:
  "interrupt_states (detype S s) = interrupt_states s"
  apply(simp add: detype_def)
  done

lemma detype_domain_sep_inv[simp]:
  "domain_sep_inv irqs st s \<longrightarrow> domain_sep_inv irqs st (detype S s)"
  apply(fastforce simp: domain_sep_inv_def)
  done

lemma domain_sep_inv_detype_lift:
  "\<lbrace>P\<rbrace> f \<lbrace>\<lambda>rv. domain_sep_inv irqs st\<rbrace> \<Longrightarrow>
   \<lbrace>P\<rbrace> f \<lbrace>\<lambda>rv s. domain_sep_inv irqs st (detype S s)\<rbrace>"
  apply(strengthen detype_domain_sep_inv, assumption)
  done

lemma retype_region_neg_cte_wp_at_not_domain_sep_inv_cap:
  "\<lbrace>\<lambda>s. \<not> cte_wp_at (not domain_sep_inv_cap irqs) slot s \<rbrace>
   retype_region  base n sz ty dev
   \<lbrace>\<lambda>rv s. \<not> cte_wp_at (not domain_sep_inv_cap irqs) slot s\<rbrace>"
  apply(rule hoare_pre)
   apply(simp only: retype_region_def retype_addrs_def

                    foldr_upd_app_if fun_app_def K_bind_def)
   apply(wp dxo_wp_weak |simp)+
  apply clarsimp
  apply(case_tac "fst slot \<in> (\<lambda>p. ptr_add base (p * 2 ^ obj_bits_api ty sz)) `
                              {0..<n}")
   apply clarsimp
   apply(erule cte_wp_atE)
    apply(clarsimp simp: default_object_def empty_cnode_def split: apiobject_type.splits if_splits simp: pred_neg_def)
   apply(clarsimp simp: default_object_def default_tcb_def tcb_cap_cases_def split: apiobject_type.splits if_splits simp: pred_neg_def)
  apply(fastforce elim: cte_wp_atE intro: cte_wp_at_tcbI cte_wp_at_cteI)
  done


lemma retype_region_domain_sep_inv[wp]:
  "\<lbrace>domain_sep_inv irqs st\<rbrace>
   retype_region base n sz tp dev
   \<lbrace>\<lambda>_. domain_sep_inv irqs st\<rbrace>"
  apply(rule domain_sep_inv_wp[where P="\<top>" and R="\<top>", simplified])
   apply(rule retype_region_neg_cte_wp_at_not_domain_sep_inv_cap)
  apply wp
  done

lemma domain_sep_inv_cap_UntypedCap[simp]:
  "domain_sep_inv_cap irqs (UntypedCap dev base sz n)"
  apply(simp add: domain_sep_inv_cap_def)
  done

crunch domain_sep_inv[wp]: invoke_untyped "domain_sep_inv irqs st"
  (ignore: freeMemory retype_region wp: crunch_wps domain_sep_inv_detype_lift
   get_cap_wp mapME_x_inv_wp
   simp: crunch_simps mapM_x_def_bak unless_def)

lemma perform_page_invocation_domain_sep_inv_get_cap_helper:
  "\<lbrace>\<top>\<rbrace>
   get_cap blah
   \<lbrace>\<lambda>rv s.
     domain_sep_inv_cap irqs
       (ArchObjectCap (F rv))\<rbrace>"
  apply(simp add: domain_sep_inv_cap_def)
  apply(rule wp_post_taut)
  done


lemma set_object_tcb_context_update_neg_cte_wp_at:
  "\<lbrace>\<lambda>s. \<not> cte_wp_at P slot s \<and> obj_at (op = (TCB tcb)) ptr s\<rbrace>
   set_object ptr (TCB (tcb\<lparr>tcb_arch := arch_tcb_context_set X (arch_tcb tcb)\<rparr>))
   \<lbrace>\<lambda>_ s. \<not> cte_wp_at P slot s\<rbrace>"
  apply(wp set_object_wp)
  apply clarsimp
  apply(case_tac "ptr = fst slot")
   apply(erule cte_wp_atE)
    apply(fastforce simp: obj_at_def)
   apply(erule notE)
   apply(clarsimp simp: obj_at_def)
   apply(rule cte_wp_at_tcbI)
      apply(simp)
     apply(fastforce)
    apply(fastforce simp: tcb_cap_cases_def split: if_splits)
  apply(fastforce elim: cte_wp_atE intro: cte_wp_at_cteI cte_wp_at_tcbI)
  done

lemma as_user_neg_cte_wp_at[wp]:
  "\<lbrace>\<lambda>s. \<not> cte_wp_at P slot s\<rbrace>
   as_user t f
   \<lbrace>\<lambda>_ s. \<not> cte_wp_at P slot s\<rbrace>"
  unfolding as_user_def
  apply(wp set_object_tcb_context_update_neg_cte_wp_at | simp add: split_def)+
  apply(fastforce simp: obj_at_def)
  done

crunch domain_sep_inv[wp]: as_user "domain_sep_inv irqs st"
  (wp: domain_sep_inv_triv)

lemma set_object_tcb_context_update_domain_sep_inv:
  "\<lbrace>\<lambda>s. domain_sep_inv irqs st s \<and> obj_at (op = (TCB tcb)) ptr s\<rbrace>
   set_object ptr (TCB (tcb\<lparr>tcb_arch := arch_tcb_context_set X (tcb_arch tcb)\<rparr>))
   \<lbrace>\<lambda>_. domain_sep_inv irqs st\<rbrace>"
  apply(rule hoare_pre)
   apply(rule domain_sep_inv_wp)
    apply(rule hoare_pre)
     apply(rule set_object_tcb_context_update_neg_cte_wp_at)
    apply(fastforce)
   apply(wp | simp | elim conjE | assumption)+
  apply blast
  done

crunch domain_sep_inv[wp]: set_mrs "domain_sep_inv irqs st"
  (ignore: set_object
   wp: crunch_wps set_object_tcb_context_update_domain_sep_inv
   simp: crunch_simps)


crunch domain_sep_inv[wp]: send_signal "domain_sep_inv irqs st" (wp: dxo_wp_weak ignore:  switch_if_required_to)

crunch domain_sep_inv[wp]: copy_mrs, set_message_info, invalidate_tlb_by_asid "domain_sep_inv irqs st"
  (wp: crunch_wps)

lemma perform_page_invocation_domain_sep_inv:
  "\<lbrace>domain_sep_inv irqs st and valid_page_inv pgi\<rbrace>
  perform_page_invocation pgi
  \<lbrace>\<lambda>_. domain_sep_inv irqs st\<rbrace>"
  apply(rule hoare_pre)
   apply(wp mapM_wp[OF _ subset_refl] set_cap_domain_sep_inv
            mapM_x_wp[OF _ subset_refl]
            perform_page_invocation_domain_sep_inv_get_cap_helper static_imp_wp
        | simp add: perform_page_invocation_def o_def | wpc)+
  apply(clarsimp simp: valid_page_inv_def)
  apply(case_tac xa, simp_all add: domain_sep_inv_cap_def is_pg_cap_def)
  done

lemma perform_page_table_invocation_domain_sep_inv:
  "\<lbrace>domain_sep_inv irqs st and valid_pti pgi\<rbrace>
  perform_page_table_invocation pgi
  \<lbrace>\<lambda>_. domain_sep_inv irqs st\<rbrace>"
  apply(rule hoare_pre)
   apply(simp add: perform_page_table_invocation_def)
   apply(wp crunch_wps perform_page_invocation_domain_sep_inv_get_cap_helper
            set_cap_domain_sep_inv
        | wpc
        | simp add: o_def)+
  apply(clarsimp simp: valid_pti_def)
  apply(case_tac x, simp_all add: domain_sep_inv_cap_def is_pt_cap_def)
  done

lemma perform_page_directory_invocation_domain_sep_inv:
  "\<lbrace>domain_sep_inv irqs st\<rbrace>
  perform_page_directory_invocation pti
  \<lbrace>\<lambda>_. domain_sep_inv irqs st\<rbrace>"
  apply (simp add: perform_page_directory_invocation_def)
  apply (cases pti)
   apply (simp | wp)+
   done

lemma cap_insert_domain_sep_inv':
  "\<lbrace> domain_sep_inv irqs st and K (domain_sep_inv_cap irqs cap) \<rbrace>
  cap_insert cap slot dest_slot
   \<lbrace> \<lambda>_. domain_sep_inv irqs st\<rbrace>"
  apply(simp add: cap_insert_def)
  apply(wp set_cap_domain_sep_inv get_cap_wp dxo_wp_weak | simp split del: if_split)+
  done

lemma domain_sep_inv_cap_max_free_index_update[simp]:
  "domain_sep_inv_cap irqs (max_free_index_update cap) =
   domain_sep_inv_cap irqs cap"
  apply(simp add: max_free_index_def free_index_update_def split: cap.splits)
  done

lemma domain_sep_inv_cap_ArchObjectCap[simp]:
  "domain_sep_inv_cap irqs (ArchObjectCap arch_cap)"
  by(simp add: domain_sep_inv_cap_def)

lemma perform_asid_control_invocation_domain_sep_inv:
  notes blah[simp del] =  atLeastAtMost_iff atLeastatMost_subset_iff atLeastLessThan_iff
  shows
  "\<lbrace>domain_sep_inv irqs st\<rbrace>
   perform_asid_control_invocation blah
   \<lbrace>\<lambda>_. domain_sep_inv irqs st\<rbrace>"
  unfolding perform_asid_control_invocation_def
  apply(rule hoare_pre)
  apply (wp modify_wp cap_insert_domain_sep_inv' set_cap_domain_sep_inv
            get_cap_domain_sep_inv_cap[where st=st] static_imp_wp
        | wpc | simp )+
  done

lemma perform_asid_pool_invocation_domain_sep_inv:
  "\<lbrace>domain_sep_inv irqs st\<rbrace>
   perform_asid_pool_invocation blah
   \<lbrace>\<lambda>_. domain_sep_inv irqs st\<rbrace>"
  apply(simp add: perform_asid_pool_invocation_def)
  apply(rule hoare_pre)
  apply(wp set_cap_domain_sep_inv get_cap_wp | wpc | simp)+
  done

lemma arch_perform_invocation_domain_sep_inv:
  "\<lbrace>domain_sep_inv irqs st and valid_arch_inv ai\<rbrace>
   arch_perform_invocation ai
   \<lbrace>\<lambda>_. domain_sep_inv irqs st\<rbrace>"
  unfolding arch_perform_invocation_def
  apply(rule hoare_pre)
  apply(wp perform_page_table_invocation_domain_sep_inv
           perform_page_directory_invocation_domain_sep_inv
           perform_page_invocation_domain_sep_inv
           perform_asid_control_invocation_domain_sep_inv
           perform_asid_pool_invocation_domain_sep_inv
       | wpc)+
  apply(clarsimp simp: valid_arch_inv_def split: arch_invocation.splits)
  done

(* when blah is AckIRQ the preconditions here contradict each other, which
   is why this lemma is true *)
lemma invoke_irq_handler_domain_sep_inv:
  "\<lbrace>domain_sep_inv irqs st and irq_handler_inv_valid blah\<rbrace>
    invoke_irq_handler blah
   \<lbrace>\<lambda>_. domain_sep_inv irqs st\<rbrace>"
  apply(case_tac blah)
    apply(wp cap_insert_domain_sep_inv' | simp)+
    apply(rename_tac irq cap cslot_ptr s)
    apply(case_tac cap, simp_all add: domain_sep_inv_cap_def)[1]
   apply(wp | auto simp: domain_sep_inv_def)+
  done


(* similarly, the preconditions here tend to contradict one another *)
lemma invoke_control_domain_sep_inv:
  "\<lbrace>domain_sep_inv irqs st and irq_control_inv_valid blah\<rbrace>
    invoke_irq_control blah
   \<lbrace>\<lambda>_. domain_sep_inv irqs st\<rbrace>"
  including no_pre
  apply(case_tac blah)
    apply(wp cap_insert_domain_sep_inv' | simp )+
   apply(case_tac irqs)
    apply(simp add: set_irq_state_def, wp, simp)
    apply(fastforce simp: domain_sep_inv_def domain_sep_inv_cap_def)
   apply(fastforce simp: valid_def domain_sep_inv_def)
  apply(wp | simp)+
  done



crunch domain_sep_inv[wp]: receive_signal "domain_sep_inv irqs st"

lemma domain_sep_inv_cap_ReplyCap[simp]:
  "domain_sep_inv_cap irqs (ReplyCap param_a param_b)"
  by(simp add: domain_sep_inv_cap_def)

lemma setup_caller_cap_domain_sep_inv[wp]:
  "\<lbrace>domain_sep_inv irqs st\<rbrace>
   setup_caller_cap a b
   \<lbrace>\<lambda>_. domain_sep_inv irqs st\<rbrace>"
  apply(simp add: setup_caller_cap_def)
  apply(wp cap_insert_domain_sep_inv' | simp)+
  done

crunch domain_sep_inv[wp]: set_extra_badge "domain_sep_inv irqs st"

lemma derive_cap_domain_sep_inv_cap:
  "\<lbrace>\<lambda>s. domain_sep_inv_cap irqs cap\<rbrace>
   derive_cap slot cap
   \<lbrace>\<lambda>rv s. domain_sep_inv_cap irqs rv\<rbrace>,-"
  apply(simp add: derive_cap_def)
  apply(rule hoare_pre)
  apply(wp | wpc | simp add: arch_derive_cap_def)+
  apply auto
  done

lemma transfer_caps_domain_sep_inv:
  "\<lbrace>domain_sep_inv irqs st and valid_objs and valid_mdb
        and (\<lambda> s. (\<forall>x\<in>set caps.
               s \<turnstile> fst x) \<and>
              (\<forall>x\<in>set caps.
               cte_wp_at
                (\<lambda>cp. fst x \<noteq> NullCap \<longrightarrow>
                      cp = fst x)
                (snd x) s \<and>
               real_cte_at (snd x) s))\<rbrace>
  transfer_caps mi caps endpoint receiver receive_buffer
  \<lbrace>\<lambda>_. domain_sep_inv irqs st\<rbrace>"
  unfolding transfer_caps_def
  apply (wpsimp wp: transfer_caps_loop_pres_dest cap_insert_domain_sep_inv hoare_vcg_all_lift hoare_vcg_imp_lift)
  apply (fastforce elim: cte_wp_at_weakenE)
  done


lemma do_normal_transfer_domain_sep_inv:
  "\<lbrace>domain_sep_inv irqs st and valid_objs and valid_mdb\<rbrace>
   do_normal_transfer sender send_buffer ep badge grant receiver recv_buffer
   \<lbrace>\<lambda>_. domain_sep_inv irqs st\<rbrace>"
  unfolding do_normal_transfer_def
  apply (wp transfer_caps_domain_sep_inv hoare_vcg_ball_lift lec_valid_cap' | simp)+
  done

crunch domain_sep_inv[wp]: do_fault_transfer "domain_sep_inv irqs st"

lemma do_ipc_transfer_domain_sep_inv:
  "\<lbrace>domain_sep_inv irqs st and valid_objs and valid_mdb\<rbrace>
   do_ipc_transfer sender ep badge grant receiver
   \<lbrace>\<lambda>_. domain_sep_inv irqs st\<rbrace>"
  unfolding do_ipc_transfer_def
  apply (wp do_normal_transfer_domain_sep_inv hoare_vcg_all_lift | wpc | wp_once hoare_drop_imps)+
  apply clarsimp
  done

(* FIXME: clagged from FinalCaps *)
lemma valid_ep_recv_dequeue':
  "\<lbrakk> ko_at (Endpoint (Structures_A.endpoint.RecvEP (t # ts))) epptr s;
     valid_objs s\<rbrakk>
     \<Longrightarrow> valid_ep (case ts of [] \<Rightarrow> Structures_A.endpoint.IdleEP
                            | b # bs \<Rightarrow> Structures_A.endpoint.RecvEP ts) s"
  unfolding valid_objs_def valid_obj_def valid_ep_def obj_at_def
  apply (drule bspec)
  apply (auto split: list.splits)
  done

lemma send_ipc_domain_sep_inv:
  "\<lbrace>domain_sep_inv irqs st and valid_objs and valid_mdb and
    sym_refs \<circ> state_refs_of\<rbrace>
   send_ipc block call badge can_grant thread epptr
   \<lbrace>\<lambda>_. domain_sep_inv irqs st\<rbrace>"
  unfolding send_ipc_def
  apply (wp setup_caller_cap_domain_sep_inv | wpc | simp)+
        apply(rule_tac Q="\<lambda> r s. domain_sep_inv irqs st s" in hoare_strengthen_post)
         apply(wp do_ipc_transfer_domain_sep_inv dxo_wp_weak | wpc | simp)+
    apply (wp_once hoare_drop_imps)
    apply (wp get_endpoint_wp)+
  apply clarsimp
  apply (fastforce simp: valid_objs_def valid_obj_def obj_at_def ep_q_refs_of_def
                         ep_redux_simps neq_Nil_conv valid_ep_def case_list_cons_cong
                   elim: ep_queued_st_tcb_at)
  done

(* FIXME: following 2 clagged from FinalCaps *)
lemma hd_tl_in_set:
  "tl xs = (x # xs') \<Longrightarrow> x \<in> set xs"
  apply(case_tac xs, auto)
  done

lemma set_tl_subset:
  "list \<noteq> [] \<Longrightarrow> set (tl list) \<subseteq> set list"
  apply(case_tac list)
   apply auto
  done

crunch domain_sep_inv[wp]: complete_signal "domain_sep_inv irqs st"

lemma receive_ipc_base_domain_sep_inv:
  "\<lbrace>domain_sep_inv irqs st and valid_objs and valid_mdb and
    sym_refs \<circ> state_refs_of and ko_at (Endpoint ep) epptr \<rbrace>
   receive_ipc_base aag receiver ep epptr rights is_blocking
   \<lbrace>\<lambda>_. domain_sep_inv irqs st\<rbrace>"
  apply (clarsimp cong: endpoint.case_cong thread_get_def get_thread_state_def)
  apply (rule hoare_pre)
  apply (wp setup_caller_cap_domain_sep_inv dxo_wp_weak
        | wpc | simp split del: if_split)+
          apply(rule_tac Q="\<lambda> r s. domain_sep_inv irqs st s" in hoare_strengthen_post)
          apply(wp do_ipc_transfer_domain_sep_inv hoare_vcg_all_lift | wpc | simp)+
     apply(wp hoare_vcg_imp_lift [OF set_endpoint_get_tcb, unfolded disj_not1] hoare_vcg_all_lift get_endpoint_wp
         | wpc | simp add: do_nbrecv_failed_transfer_def)+
  apply (clarsimp simp: conj_comms)
  apply (fastforce simp: valid_objs_def valid_obj_def obj_at_def
                         ep_redux_simps neq_Nil_conv valid_ep_def case_list_cons_cong)
  done

lemma receive_ipc_domain_sep_inv:
  "\<lbrace>domain_sep_inv irqs st and valid_objs and valid_mdb and
    sym_refs \<circ> state_refs_of \<rbrace>
   receive_ipc receiver cap is_blocking
   \<lbrace>\<lambda>_. domain_sep_inv irqs st\<rbrace>"
  unfolding receive_ipc_def
  apply (simp add: receive_ipc_def split: cap.splits, clarsimp)
  apply (rule hoare_seq_ext[OF _ get_endpoint_sp])
  apply (rule hoare_seq_ext[OF _ gbn_sp])
  apply (case_tac ntfnptr, simp)
  apply (wp receive_ipc_base_domain_sep_inv get_ntfn_wp | simp split: if_split option.splits)+
  done

lemma send_fault_ipc_domain_sep_inv:
  "\<lbrace>domain_sep_inv irqs st and valid_objs and sym_refs \<circ> state_refs_of and valid_mdb and
     K (valid_fault fault)\<rbrace>
    send_fault_ipc thread fault
    \<lbrace>\<lambda>rv. domain_sep_inv irqs st\<rbrace>"
  apply(rule hoare_gen_asm)+
  unfolding send_fault_ipc_def
  apply(wp send_ipc_domain_sep_inv thread_set_valid_objs thread_set_tcb_fault_update_valid_mdb
           thread_set_refs_trivial thread_set_obj_at_impossible
           hoare_vcg_ex_lift
       | wpc| simp add: Let_def split_def lookup_cap_def valid_tcb_fault_update split del: if_split)+
    apply (wpe get_cap_inv[where P="domain_sep_inv irqs st and valid_objs and valid_mdb
                            and sym_refs o state_refs_of"])
    apply (wp | simp)+
  done

crunch domain_sep_inv[wp]: handle_fault "domain_sep_inv irqs st"

crunch domain_sep_inv[wp]: do_reply_transfer "domain_sep_inv irqs st"
  (wp:  dxo_wp_weak crunch_wps  ignore: set_object thread_set attempt_switch_to)

crunch domain_sep_inv[wp]: reply_from_kernel "domain_sep_inv irqs st"
  (wp: crunch_wps simp: crunch_simps)

crunch domain_sep_inv[wp]: setup_reply_master "domain_sep_inv irqs st"
  (wp: crunch_wps simp: crunch_simps)

crunch domain_sep_inv[wp]: restart "domain_sep_inv irqs st"
  (wp: crunch_wps dxo_wp_weak simp: crunch_simps ignore: tcb_sched_action switch_if_required_to)

lemma thread_set_tcb_ipc_buffer_update_neg_cte_wp_at[wp]:
  "\<lbrace>\<lambda>s. \<not> cte_wp_at P slot s\<rbrace>
    thread_set (tcb_ipc_buffer_update f) t
   \<lbrace>\<lambda>_ s. \<not> cte_wp_at P slot s\<rbrace>"
  unfolding thread_set_def
  apply(wp set_object_wp | simp)+
  apply(case_tac "t = fst slot")
   apply(clarsimp split: kernel_object.splits)
   apply(erule notE)
   apply(erule cte_wp_atE)
    apply(fastforce simp: obj_at_def)
   apply(drule get_tcb_SomeD)
   apply(rule cte_wp_at_tcbI)
     apply(simp)
    apply assumption
   apply (fastforce simp: tcb_cap_cases_def split: if_splits)
  apply(fastforce elim: cte_wp_atE intro: cte_wp_at_cteI cte_wp_at_tcbI)
  done

lemma thread_set_tcb_ipc_buffer_update_domain_sep_inv[wp]:
  "\<lbrace>domain_sep_inv irqs st\<rbrace>
   thread_set (tcb_ipc_buffer_update f) t
   \<lbrace>\<lambda>_. domain_sep_inv irqs st\<rbrace>"
  by (rule domain_sep_inv_triv; wp)

lemma thread_set_tcb_fault_handler_update_neg_cte_wp_at[wp]:
  "\<lbrace>\<lambda>s. \<not> cte_wp_at P slot s\<rbrace>
   thread_set (tcb_fault_handler_update blah) t
   \<lbrace>\<lambda>_ s. \<not> cte_wp_at P slot s\<rbrace>"
  unfolding thread_set_def
  apply(wp set_object_wp | simp)+
  apply(case_tac "t = fst slot")
   apply(clarsimp split: kernel_object.splits)
   apply(erule notE)
   apply(erule cte_wp_atE)
    apply(fastforce simp: obj_at_def)
   apply(drule get_tcb_SomeD)
   apply(rule cte_wp_at_tcbI)
     apply(simp)
    apply assumption
   apply (fastforce simp: tcb_cap_cases_def split: if_splits)
  apply(fastforce elim: cte_wp_atE intro: cte_wp_at_cteI cte_wp_at_tcbI)
  done

lemma thread_set_tcb_fault_handler_update_domain_sep_inv[wp]:
  "\<lbrace>domain_sep_inv irqs st\<rbrace>
   thread_set (tcb_fault_handler_update blah) t
   \<lbrace>\<lambda>_. domain_sep_inv irqs st\<rbrace>"
  by (rule domain_sep_inv_triv; wp)

lemma thread_set_tcb_tcb_mcpriority_update_neg_cte_wp_at[wp]:
  "\<lbrace>\<lambda>s. \<not> cte_wp_at P slot s\<rbrace>
   thread_set (tcb_mcpriority_update blah) t
   \<lbrace>\<lambda>_ s. \<not> cte_wp_at P slot s\<rbrace>"
  unfolding thread_set_def
  apply(wp set_object_wp | simp)+
  apply(case_tac "t = fst slot")
   apply(clarsimp split: kernel_object.splits)
   apply(erule notE)
   apply(erule cte_wp_atE)
    apply(fastforce simp: obj_at_def)
   apply(drule get_tcb_SomeD)
   apply(rule cte_wp_at_tcbI)
     apply(simp)
    apply assumption
   apply (fastforce simp: tcb_cap_cases_def split: if_splits)
  apply(fastforce elim: cte_wp_atE intro: cte_wp_at_cteI cte_wp_at_tcbI)
  done

lemma thread_set_tcb_tcp_mcpriority_update_domain_sep_inv[wp]:
  "\<lbrace>domain_sep_inv irqs st\<rbrace>
   thread_set (tcb_mcpriority_update blah) t
   \<lbrace>\<lambda>_. domain_sep_inv irqs st\<rbrace>"
  by (rule domain_sep_inv_triv; wp)

lemma same_object_as_domain_sep_inv_cap:
  "\<lbrakk>same_object_as a cap; domain_sep_inv_cap irqs cap\<rbrakk>
   \<Longrightarrow> domain_sep_inv_cap irqs a"
  apply(case_tac a, simp_all add: same_object_as_def domain_sep_inv_cap_def)
  apply(case_tac cap, simp_all)
  done

lemma checked_cap_insert_domain_sep_inv:
  "\<lbrace>domain_sep_inv irqs st\<rbrace>
   check_cap_at a b (check_cap_at c d (cap_insert a b e))
   \<lbrace>\<lambda>_. domain_sep_inv irqs st\<rbrace>"
  apply(wp get_cap_wp cap_insert_domain_sep_inv' | simp add: check_cap_at_def)+
  apply clarsimp
  apply(drule_tac cap=cap in cte_wp_at_domain_sep_inv_cap)
   apply assumption
  apply(erule (1) same_object_as_domain_sep_inv_cap)
  done

crunch domain_sep_inv[wp]: bind_notification "domain_sep_inv irqs st"

lemma set_mcpriority_domain_sep_inv[wp]:
  "\<lbrace>domain_sep_inv irqs st\<rbrace> set_mcpriority tcb_ref mcp \<lbrace>\<lambda>_. domain_sep_inv irqs st\<rbrace>"
  unfolding set_mcpriority_def by wp

lemma invoke_tcb_domain_sep_inv:
  "\<lbrace>domain_sep_inv irqs st and
    Tcb_AI.tcb_inv_wf tinv\<rbrace>
   invoke_tcb tinv
   \<lbrace>\<lambda>_. domain_sep_inv irqs st\<rbrace>"
  apply(case_tac tinv)
       apply((wp restart_domain_sep_inv hoare_vcg_if_lift  mapM_x_wp[OF _ subset_refl]
            | wpc
            | simp split del: if_split add: check_cap_at_def
            | clarsimp)+)[3]
    defer
    apply((wp | simp )+)[2]
  (* just NotificationControl and ThreadControl left *)
  apply (rename_tac option)
  apply (case_tac option)
  apply  ((wp | simp)+)[1]
  apply (simp add: split_def cong: option.case_cong)
  apply (wp checked_cap_insert_domain_sep_inv hoare_vcg_all_lift_R
            hoare_vcg_all_lift hoare_vcg_const_imp_lift_R
            cap_delete_domain_sep_inv
            cap_delete_deletes
            dxo_wp_weak
            cap_delete_valid_cap cap_delete_cte_at static_imp_wp
        |wpc
        |simp add: emptyable_def tcb_cap_cases_def tcb_cap_valid_def
                  tcb_at_st_tcb_at
        |strengthen use_no_cap_to_obj_asid_strg)+
  apply(rule hoare_pre)
  apply(simp add: option_update_thread_def tcb_cap_cases_def
       | wp hoare_vcg_all_lift
            thread_set_emptyable
            thread_set_valid_cap static_imp_wp
            thread_set_cte_at  thread_set_no_cap_to_trivial
       | wpc)+
  done

lemma invoke_domain_domain_set_inv:
  "\<lbrace>domain_sep_inv irqs st\<rbrace>
     invoke_domain word1 word2
   \<lbrace>\<lambda>_. domain_sep_inv irqs st\<rbrace>"
apply (simp add: invoke_domain_def set_domain_extended.dxo_eq)
apply (wp dxo_wp_weak | simp)+
done



lemma perform_invocation_domain_sep_inv':
  "\<lbrace>domain_sep_inv irqs st and valid_invocation iv and valid_objs and valid_mdb and sym_refs \<circ> state_refs_of\<rbrace>
   perform_invocation block call iv
   \<lbrace>\<lambda>_. domain_sep_inv irqs st\<rbrace>"
  apply(case_tac iv)
          apply(wp send_ipc_domain_sep_inv invoke_tcb_domain_sep_inv
                   invoke_cnode_domain_sep_inv invoke_control_domain_sep_inv
                   invoke_irq_handler_domain_sep_inv arch_perform_invocation_domain_sep_inv
                   invoke_domain_domain_set_inv
               | simp add: split_def
               | blast)+
  done

lemma perform_invocation_domain_sep_inv:
  "\<lbrace>domain_sep_inv irqs st and valid_invocation iv and invs\<rbrace>
   perform_invocation block call iv
   \<lbrace>\<lambda>_. domain_sep_inv irqs st\<rbrace>"
apply (rule hoare_weaken_pre[OF perform_invocation_domain_sep_inv'])
apply auto
done

lemma handle_invocation_domain_sep_inv:
  "\<lbrace>domain_sep_inv irqs st and invs and ct_active\<rbrace>
   handle_invocation calling blocking
   \<lbrace>\<lambda>_. domain_sep_inv irqs st\<rbrace>"
  apply (simp add: handle_invocation_def ts_Restart_case_helper split_def
                   liftE_liftM_liftME liftME_def bindE_assoc
              split del: if_split)
  apply(wp syscall_valid perform_invocation_domain_sep_inv
           set_thread_state_runnable_valid_sched
       | simp split del: if_split)+
       apply(rule_tac E="\<lambda>ft. domain_sep_inv irqs st and
                  valid_objs and
                  sym_refs \<circ> state_refs_of and
                  valid_mdb and
                  (\<lambda>y. valid_fault ft)" and R="Q" and Q=Q for Q in hoare_post_impErr)
         apply(wp
              | simp | clarsimp)+
     apply(rule_tac E="\<lambda>ft. domain_sep_inv irqs st and
                            valid_objs and
                            sym_refs \<circ> state_refs_of and
                            valid_mdb and
                            (\<lambda>y. valid_fault (CapFault x False ft))" and R="Q" and Q=Q 
                  for Q in hoare_post_impErr)
       apply (wp lcs_ex_cap_to2
             | clarsimp)+
  apply (auto intro: st_tcb_ex_cap simp: ct_in_state_def)
  done

lemma handle_send_domain_sep_inv:
  "\<lbrace>domain_sep_inv irqs st and invs and ct_active\<rbrace>
   handle_send a
   \<lbrace>\<lambda>_. domain_sep_inv irqs st\<rbrace>"
  apply(simp add: handle_send_def)
  apply(wp handle_invocation_domain_sep_inv)
  done

lemma handle_call_domain_sep_inv:
  "\<lbrace>domain_sep_inv irqs st and invs and ct_active\<rbrace>
   handle_call
   \<lbrace>\<lambda>_. domain_sep_inv irqs st\<rbrace>"
  apply(simp add: handle_call_def)
  apply(wp handle_invocation_domain_sep_inv)
  done

lemma handle_reply_domain_sep_inv:
  "\<lbrace>domain_sep_inv irqs st and invs\<rbrace> handle_reply \<lbrace>\<lambda>_. domain_sep_inv irqs st\<rbrace>"
  apply(simp add: handle_reply_def)
  apply(wp get_cap_wp | wpc)+
  apply auto
  done

crunch domain_sep_inv[wp]: delete_caller_cap "domain_sep_inv irqs st"

(* FIXME: clagged from Syscall_AC *)
lemma lookup_slot_for_thread_cap_fault:
  "\<lbrace>invs\<rbrace> lookup_slot_for_thread t s -, \<lbrace>\<lambda>f s. valid_fault (CapFault x y f)\<rbrace>"
  apply (simp add: lookup_slot_for_thread_def)
  apply (wp resolve_address_bits_valid_fault2)
  apply clarsimp
  apply (erule (1) invs_valid_tcb_ctable)
  done


lemma handle_recv_domain_sep_inv:
  "\<lbrace>domain_sep_inv irqs st and invs\<rbrace>
   handle_recv is_blocking
   \<lbrace>\<lambda>_. domain_sep_inv irqs st\<rbrace>"
  apply (simp add: handle_recv_def Let_def lookup_cap_def split_def)
  apply (wp hoare_vcg_all_lift lookup_slot_for_thread_cap_fault
            receive_ipc_domain_sep_inv delete_caller_cap_domain_sep_inv
            get_cap_wp get_ntfn_wp
        | wpc | simp
        | rule_tac Q="\<lambda>rv. invs and (\<lambda>s. cur_thread s = thread)" in hoare_strengthen_post, wp, 
          clarsimp simp: invs_valid_objs invs_sym_refs)+
    apply (rule_tac Q'="\<lambda>r s. domain_sep_inv irqs st s \<and> invs s \<and> tcb_at thread s \<and> thread = cur_thread s" in hoare_post_imp_R)
      apply wp
     apply ((clarsimp simp add: invs_valid_objs invs_sym_refs
           | intro impI allI conjI
           | rule cte_wp_valid_cap caps_of_state_cteD
           | fastforce simp:  valid_fault_def
           )+)[1]
    apply (wp delete_caller_cap_domain_sep_inv | simp add: split_def cong: conj_cong)+
    apply(wp | simp add: invs_valid_objs invs_mdb invs_sym_refs tcb_at_invs)+
  done

crunch domain_sep_inv[wp]: handle_interrupt "domain_sep_inv irqs st"
  (wp: dxo_wp_weak ignore: getActiveIRQ resetTimer ackInterrupt ignore: timer_tick)

crunch domain_sep_inv[wp]: handle_vm_fault, handle_hypervisor_fault "domain_sep_inv irqs st"
  (ignore: getFAR getDFSR getIFSR)

lemma handle_event_domain_sep_inv:
  "\<lbrace> domain_sep_inv irqs st and invs and
      (\<lambda>s. ev \<noteq> Interrupt \<longrightarrow> ct_active s) \<rbrace>
   handle_event ev
   \<lbrace> \<lambda>_. domain_sep_inv irqs st\<rbrace>"
  apply(case_tac ev, simp_all)
      apply(rule hoare_pre)
       apply(wpc
            | wp handle_send_domain_sep_inv handle_call_domain_sep_inv
                 handle_recv_domain_sep_inv handle_reply_domain_sep_inv
                 hy_inv
            | simp add: invs_valid_objs invs_mdb invs_sym_refs valid_fault_def)+
     apply(rule_tac E="\<lambda>rv s. domain_sep_inv irqs st s \<and> invs s \<and> valid_fault rv" and R="Q" and Q=Q for Q in hoare_post_impErr)
     apply(wp handle_vm_fault_domain_sep_inv | simp add: invs_valid_objs invs_mdb invs_sym_refs valid_fault_def | auto)+
  done

crunch domain_sep_inv[wp]: activate_thread "domain_sep_inv irqs st"

lemma domain_sep_inv_cur_thread_update[simp]:
  "domain_sep_inv irqs st (s\<lparr>cur_thread := X\<rparr>) = domain_sep_inv irqs st s"
  apply(simp add: domain_sep_inv_def)
  done

crunch domain_sep_inv[wp]: choose_thread "domain_sep_inv irqs st"
  (wp: crunch_wps dxo_wp_weak ignore: tcb_sched_action ARM.clearExMonitor)

end

lemma (in is_extended') domain_sep_inv[wp]: "I (domain_sep_inv irqs st)" by (rule lift_inv, simp)

context begin interpretation Arch . (*FIXME: arch_split*)

lemma schedule_domain_sep_inv: "\<lbrace>domain_sep_inv irqs st\<rbrace> (schedule :: (unit,det_ext) s_monad) \<lbrace>\<lambda>_. domain_sep_inv irqs st\<rbrace>"
  apply (simp add: schedule_def allActiveTCBs_def)
  apply (wp alternative_wp select_wp
            guarded_switch_to_lift | wpc | clarsimp simp: get_thread_state_def thread_get_def trans_state_update'[symmetric])+
  done

lemma call_kernel_domain_sep_inv:
  "\<lbrace> domain_sep_inv irqs st and invs and
      (\<lambda>s. ev \<noteq> Interrupt \<longrightarrow> ct_active s) \<rbrace>
   call_kernel ev :: (unit,det_ext) s_monad
   \<lbrace> \<lambda>_. domain_sep_inv irqs st\<rbrace>"
apply (simp add: call_kernel_def getActiveIRQ_def)
apply (wp handle_interrupt_domain_sep_inv handle_event_domain_sep_inv schedule_domain_sep_inv
     | simp)+
done

end

end
