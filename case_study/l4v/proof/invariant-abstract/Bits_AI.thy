(*
 * Copyright 2014, General Dynamics C4 Systems
 *
 * This software may be distributed and modified according to the terms of
 * the GNU General Public License version 2. Note that NO WARRANTY is provided.
 * See "LICENSE_GPLv2.txt" for details.
 *
 * @TAG(GD_GPL)
 *)

theory Bits_AI
imports "./$L4V_ARCH/ArchBits_AI"
begin

lemmas crunch_wps = hoare_drop_imps mapM_wp' mapM_x_wp'

lemmas crunch_simps = split_def whenE_def unlessE_def Let_def if_fun_split
                      assertE_def zipWithM_mapM zipWithM_x_mapM


lemma set_object_is_modify:
  "set_object ptr obj = modify (\<lambda>s. s \<lparr> kheap := kheap s (ptr \<mapsto> obj) \<rparr>)"
  unfolding set_object_def modify_def by simp

definition
  intr :: "ExceptionTypes_A.interrupt \<Rightarrow> irq \<Rightarrow> bool" where
 "intr x y \<equiv> (x = Interrupted y)"

lemma intr_simp[simp]:
 "intr (Interrupted x) y = (x = y)"
  by (simp add: intr_def)

lemma cap_fault_injection:
 "cap_fault_on_failure addr b = injection_handler (ExceptionTypes_A.CapFault addr b)"
  apply (rule ext)
  apply (simp add: cap_fault_on_failure_def injection_handler_def o_def)
  done

lemma lookup_error_injection:
 "lookup_error_on_failure b = injection_handler (ExceptionTypes_A.FailedLookup b)"
  apply (rule ext)
  apply (simp add: lookup_error_on_failure_def injection_handler_def o_def)
  done


ML \<open>Thm.join_proofs @{thms lookup_error_injection}\<close>

lemmas cap_fault_wp[wp] = injection_wp[OF cap_fault_injection]

lemmas cap_fault_wp_E[wp] = injection_wp_E[OF cap_fault_injection]

lemmas cap_fault_bindE = injection_bindE[OF cap_fault_injection cap_fault_injection]

lemmas cap_fault_liftE[simp] = injection_liftE[OF cap_fault_injection]

lemmas lookup_error_wp[wp] = injection_wp[OF lookup_error_injection]

lemmas lookup_error_wp_E[wp] = injection_wp_E[OF lookup_error_injection]

lemmas lookup_error_bindE = injection_bindE[OF lookup_error_injection lookup_error_injection]

lemmas lookup_error_liftE[simp] = injection_liftE[OF lookup_error_injection]

lemma unify_failure_injection:
  "unify_failure = injection_handler (\<lambda>x. ())"
  by (intro ext, simp add: unify_failure_def injection_handler_def)


lemmas unify_failure_wp[wp] = injection_wp [OF unify_failure_injection]

lemmas unify_failure_wp_E[wp] = injection_wp_E [OF unify_failure_injection]

lemma ep_cases_weak_wp:
  assumes "\<lbrace>P_A\<rbrace> a \<lbrace>Q\<rbrace>" 
  assumes "\<And>q. \<lbrace>P_B\<rbrace> b q \<lbrace>Q\<rbrace>"
  assumes "\<And>q. \<lbrace>P_C\<rbrace> c q \<lbrace>Q\<rbrace>"
  shows 
  "\<lbrace>P_A and P_B and P_C\<rbrace> 
    case ts of 
      Structures_A.IdleEP \<Rightarrow> a
    | Structures_A.SendEP q \<Rightarrow> b q
    | Structures_A.RecvEP q \<Rightarrow> c q \<lbrace>Q\<rbrace>"
  apply (cases ts)
  apply (simp, rule hoare_weaken_pre, rule assms, simp)+
  done

lemma ntfn_cases_weak_wp:
  assumes "\<lbrace>P_A\<rbrace> a \<lbrace>Q\<rbrace>" 
  assumes "\<And>q. \<lbrace>P_B\<rbrace> b q \<lbrace>Q\<rbrace>"
  assumes "\<And>bdg msg. \<lbrace>P_C\<rbrace> c bdg msg \<lbrace>Q\<rbrace>"
  shows 
  "\<lbrace>P_A and P_B and P_C\<rbrace> 
    case ts of 
      Structures_A.IdleNtfn \<Rightarrow> a
    | Structures_A.WaitingNtfn q \<Rightarrow> b q
    | Structures_A.ActiveNtfn bdg \<Rightarrow> c bdg msg \<lbrace>Q\<rbrace>"
  apply (cases ts)
  apply (simp, rule hoare_weaken_pre, rule assms, simp)+
  done

lemma NullCap_valid [simp]: "s \<turnstile> cap.NullCap"
  by (simp add: valid_cap_def)

lemma empty_on_failure_wp[wp]:
  "\<lbrace>P\<rbrace> m \<lbrace>Q\<rbrace>,\<lbrace>\<lambda>rv. Q []\<rbrace>
    \<Longrightarrow> \<lbrace>P\<rbrace> empty_on_failure m \<lbrace>Q\<rbrace>"
  by (simp add: empty_on_failure_def) wp

end
