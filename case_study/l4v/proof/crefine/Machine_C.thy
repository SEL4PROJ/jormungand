(*
 * Copyright 2014, General Dynamics C4 Systems
 *
 * This software may be distributed and modified according to the terms of
 * the GNU General Public License version 2. Note that NO WARRANTY is provided.
 * See "LICENSE_GPLv2.txt" for details.
 *
 * @TAG(GD_GPL)
 *)

(*
   Author: Gerwin Klein
   
   Assumptions and lemmas on machine operations.
*)

theory Machine_C
imports "../../lib/clib/Ctac"
begin

locale kernel_m = kernel +
assumes resetTimer_ccorres:
  "ccorres dc xfdc \<top> UNIV []
           (doMachineOp resetTimer)
           (Call resetTimer_'proc)"

assumes writeTTBR0_ccorres:
  "ccorres dc xfdc \<top> (\<lbrace>\<acute>addr = pd\<rbrace>) []
           (doMachineOp (writeTTBR0 pd))
           (Call writeTTBR0_'proc)"

assumes setHardwareASID_ccorres:
  "ccorres dc xfdc \<top> (\<lbrace>\<acute>hw_asid = hw_asid\<rbrace>) []
           (doMachineOp (setHardwareASID hw_asid))
           (Call setHardwareASID_'proc)"

assumes isb_ccorres:
  "ccorres dc xfdc \<top> UNIV []
           (doMachineOp isb)
           (Call isb_'proc)"

assumes dsb_ccorres:
  "ccorres dc xfdc \<top> UNIV []
           (doMachineOp dsb)
           (Call dsb_'proc)"

assumes dmb_ccorres:
  "ccorres dc xfdc \<top> UNIV []
           (doMachineOp dmb)
           (Call dmb_'proc)"

assumes invalidateTLB_ccorres:
  "ccorres dc xfdc \<top> UNIV []
           (doMachineOp invalidateTLB)
           (Call invalidateTLB_'proc)"

assumes invalidateTLB_ASID_ccorres:
  "ccorres dc xfdc \<top> (\<lbrace>\<acute>hw_asid = hw_asid \<rbrace>) []
           (doMachineOp (invalidateTLB_ASID hw_asid))
           (Call invalidateTLB_ASID_'proc)"

assumes invalidateTLB_VAASID_ccorres:
  "ccorres dc xfdc \<top> (\<lbrace>\<acute>mva_plus_asid = w\<rbrace>) []
           (doMachineOp (invalidateTLB_VAASID w))
           (Call invalidateTLB_VAASID_'proc)"

assumes cleanByVA_ccorres:
  "ccorres dc xfdc \<top> (\<lbrace>\<acute>vaddr = w1\<rbrace> \<inter> \<lbrace>\<acute>paddr = w2\<rbrace>) []
           (doMachineOp (cleanByVA w1 w2))
           (Call cleanByVA_'proc)"

assumes cleanByVA_PoU_ccorres:
  "ccorres dc xfdc \<top> (\<lbrace>\<acute>vaddr = w1\<rbrace> \<inter> \<lbrace>\<acute>paddr = w2\<rbrace>) []
           (doMachineOp (cleanByVA_PoU w1 w2))
           (Call cleanByVA_PoU_'proc)"

assumes cleanByVA_PoU_preserves_kernel_bytes:
 "\<forall>s. \<Gamma>\<turnstile>\<^bsub>/UNIV\<^esub> {s} Call cleanByVA_PoU_'proc
      {t. hrs_htd (t_hrs_' (globals t)) = hrs_htd (t_hrs_' (globals s))
         \<and> (\<forall>x. snd (hrs_htd (t_hrs_' (globals s)) x) 0 \<noteq> None
             \<longrightarrow> hrs_mem (t_hrs_' (globals t)) x = hrs_mem (t_hrs_' (globals s)) x)}"

assumes invalidateByVA_ccorres:
  "ccorres dc xfdc \<top> (\<lbrace>\<acute>vaddr = w1\<rbrace> \<inter> \<lbrace>\<acute>paddr = w2\<rbrace>) []
           (doMachineOp (invalidateByVA w1 w2))
           (Call invalidateByVA_'proc)"

assumes invalidateByVA_I_ccorres:
  "ccorres dc xfdc \<top> (\<lbrace>\<acute>vaddr = w1\<rbrace> \<inter> \<lbrace>\<acute>paddr = w2\<rbrace>) []
           (doMachineOp (invalidateByVA_I w1 w2))
           (Call invalidateByVA_I_'proc)"

assumes invalidate_I_PoU_ccorres:
  "ccorres dc xfdc \<top> UNIV []
           (doMachineOp invalidate_I_PoU)
           (Call invalidate_I_PoU_'proc)"

assumes cleanInvalByVA_ccorres:
  "ccorres dc xfdc \<top> (\<lbrace>\<acute>vaddr = w1\<rbrace> \<inter> \<lbrace>\<acute>paddr = w2\<rbrace>) []
           (doMachineOp (cleanInvalByVA w1 w2))
           (Call cleanInvalByVA_'proc)"

assumes branchFlush_ccorres:
  "ccorres dc xfdc \<top> (\<lbrace>\<acute>vaddr = w1\<rbrace> \<inter> \<lbrace>\<acute>paddr = w2\<rbrace>) []
           (doMachineOp (branchFlush w1 w2))
           (Call branchFlush_'proc)"

assumes clean_D_PoU_ccorres:
  "ccorres dc xfdc \<top> UNIV []
           (doMachineOp clean_D_PoU)
           (Call clean_D_PoU_'proc)"

assumes cleanInvalidate_D_PoC_ccorres:
  "ccorres dc xfdc \<top> UNIV []
           (doMachineOp cleanInvalidate_D_PoC)
           (Call cleanInvalidate_D_PoC_'proc)"

assumes cleanInvalidateL2Range_ccorres:
  "ccorres dc xfdc \<top> (\<lbrace>\<acute>start = w1\<rbrace> \<inter> \<lbrace>\<acute>end = w2\<rbrace>) []
           (doMachineOp (cleanInvalidateL2Range w1 w2))
           (Call cleanInvalidateL2Range_'proc)"

assumes invalidateL2Range_ccorres:
  "ccorres dc xfdc \<top> (\<lbrace>\<acute>start = w1\<rbrace> \<inter> \<lbrace>\<acute>end = w2\<rbrace>) []
           (doMachineOp (invalidateL2Range w1 w2))
           (Call invalidateL2Range_'proc)"

assumes cleanL2Range_ccorres:
  "ccorres dc xfdc \<top> (\<lbrace>\<acute>start = w1\<rbrace> \<inter> \<lbrace>\<acute>end = w2\<rbrace>) []
           (doMachineOp (cleanL2Range w1 w2))
           (Call plat_cleanL2Range_'proc)"

assumes clearExMonitor_ccorres:
  "ccorres dc xfdc \<top> UNIV []
           (doMachineOp ARM.clearExMonitor)
           (Call clearExMonitor_'proc)"

assumes getIFSR_ccorres:
  "ccorres (op =) ret__unsigned_long_' \<top> UNIV []
           (doMachineOp getIFSR)
           (Call getIFSR_'proc)"

assumes getDFSR_ccorres:
  "ccorres (op =) ret__unsigned_long_' \<top> UNIV []
           (doMachineOp getDFSR)
           (Call getDFSR_'proc)"

assumes getFAR_ccorres:
  "ccorres (op =) ret__unsigned_long_' \<top> UNIV []
           (doMachineOp getFAR)
           (Call getFAR_'proc)"

assumes getActiveIRQ_ccorres:
"ccorres (\<lambda>(a::10 word option) c::16 word.
     case a of None \<Rightarrow> c = (0xFFFF::16 word)
     | Some (x::10 word) \<Rightarrow> c = ucast x \<and> c \<noteq> (0xFFFF::16 word))
     (\<lambda>t. irq_' (s\<lparr>globals := globals t, irq_' := ret__unsigned_short_' t\<rparr> ))
     \<top> UNIV hs
 (doMachineOp getActiveIRQ) (Call getActiveIRQ_'proc)"

(* This is not very correct, however our current implementation of Hardware in haskell is stateless *)
assumes isIRQPending_ccorres:
  "ccorres (\<lambda>rv rv'. rv' = from_bool (rv \<noteq> None)) ret__unsigned_long_'
      \<top> UNIV []
      (doMachineOp getActiveIRQ) (Call isIRQPending_'proc)"

assumes armv_contextSwitch_HWASID_ccorres:
  "ccorres dc xfdc \<top> (UNIV \<inter> {s. cap_pd_' s = pde_Ptr pd} \<inter> {s. hw_asid_' s = hwasid}) []
     (doMachineOp (armv_contextSwitch_HWASID pd hwasid)) (Call armv_contextSwitch_HWASID_'proc)"

assumes getActiveIRQ_Normal:
  "\<Gamma> \<turnstile> \<langle>Call getActiveIRQ_'proc, Normal s\<rangle> \<Rightarrow> s' \<Longrightarrow> isNormal s'"

assumes maskInterrupt_ccorres:
  "ccorres dc xfdc \<top> (\<lbrace>\<acute>disable = from_bool m\<rbrace> \<inter> \<lbrace>\<acute>irq = ucast irq\<rbrace>) []
           (doMachineOp (maskInterrupt m irq))
           (Call maskInterrupt_'proc)"

assumes invalidateTLB_VAASID_spec:
 "\<Gamma>\<turnstile>\<^bsub>/UNIV\<^esub> UNIV (Call invalidateMVA_'proc) UNIV"

assumes cleanCacheRange_PoU_spec:
 "\<Gamma>\<turnstile>\<^bsub>/UNIV\<^esub> UNIV (Call cleanCacheRange_PoU_'proc) UNIV"

(* The following are fastpath specific assumptions.
   We might want to move them somewhere else. *)

(*  clearExMonitor_fp is an inline-friendly version of clearExMonitor *)
assumes clearExMonitor_fp_ccorres:
  "ccorres dc xfdc (\<lambda>_. True) UNIV [] (doMachineOp ARM.clearExMonitor)
   (Call clearExMonitor_fp_'proc)"

(*
  @{text slowpath} is an assembly stub that switches execution
  from the fastpath to the slowpath. Its contract is equivalence
  to the toplevel slowpath function @{term callKernel} for the
  @{text SyscallEvent} case.
*)
assumes slowpath_ccorres:
  "ccorres dc xfdc
     (\<lambda>s. invs' s \<and> ct_in_state' (op = Running) s)
     ({s. syscall_' s = syscall_from_H ev})
     [SKIP]
     (callKernel (SyscallEvent ev)) (Call slowpath_'proc)"

(*
  @{text slowpath} does not return, but uses the regular
  slowpath kernel exit instead.
*)
assumes slowpath_noreturn_spec:
  "\<Gamma> \<turnstile> UNIV Call slowpath_'proc {},UNIV"

(*
  @{text fastpath_restore} updates badge and msgInfo registers
  and returns to the user.
*)
assumes fastpath_restore_ccorres:
  "ccorres dc xfdc
     (\<lambda>s. t = ksCurThread s)
     ({s. badge_' s = bdg} \<inter> {s. msgInfo_' s = msginfo}
           \<inter> {s. cur_thread_' s = tcb_ptr_to_ctcb_ptr t})
     [SKIP]
     (asUser t (zipWithM_x setRegister
               [ARM_H.badgeRegister, ARM_H.msgInfoRegister]
               [bdg, msginfo]))
     (Call fastpath_restore_'proc)"

assumes ackInterrupt_ccorres:
  "ccorres dc xfdc \<top> UNIV hs
           (doMachineOp (ackInterrupt irq))
           (Call ackInterrupt_'proc)"

context kernel_m begin

lemma index_xf_for_sequence:
  "\<forall>s f. index_' (index_'_update f s) = f (index_' s)
          \<and> globals (index_'_update f s) = globals s"
  by simp

lemma upto_enum_word_nth:
  "\<lbrakk>i \<le> j; k \<le> unat (j - i)\<rbrakk> \<Longrightarrow> [i .e. j] ! k = i + of_nat k"
  apply (clarsimp simp: upto_enum_def nth_upt nth_append)
  apply (clarsimp simp: toEnum_of_nat word_le_nat_alt[symmetric])
  apply (rule conjI, clarsimp)
   apply (subst toEnum_of_nat, unat_arith)
   apply unat_arith
  apply (clarsimp simp: not_less unat_sub[symmetric])
  apply unat_arith
  done

lemma upto_enum_step_nth:
  "\<lbrakk>a \<le> c; n \<le> unat ((c - a) div (b - a))\<rbrakk> \<Longrightarrow> [a, b .e. c] ! n = a + of_nat n * (b - a)"
  apply (clarsimp simp: upto_enum_step_def not_less[symmetric])
  apply (subst upto_enum_word_nth)
    apply (auto simp: not_less word_of_nat_le)
  done

lemma lineStart_le_mono:
  "x \<le> y \<Longrightarrow> lineStart x \<le> lineStart y"
  by (clarsimp simp: lineStart_def cacheLineBits_def shiftr_shiftl1 neg_mask_mono_le)

lemma neg_mask_add:
  "y && mask n = 0 \<Longrightarrow> x + y && ~~ mask n = (x && ~~ mask n) + y"
  by (clarsimp simp: mask_out_sub_mask mask_eqs(7)[symmetric] mask_twice)

lemma lineStart_sub:
  "\<lbrakk> x && mask 5 = y && mask 5\<rbrakk> \<Longrightarrow> lineStart (x - y) = lineStart x - lineStart y"
  apply (clarsimp simp: lineStart_def cacheLineBits_def shiftr_shiftl1)
  apply (clarsimp simp: mask_out_sub_mask)
  apply (clarsimp simp: mask_eqs(8)[symmetric])
  done


lemma minus_minus_swap:
  "\<lbrakk> a \<le> c; b \<le> d; b \<le> a; d \<le> c\<rbrakk> \<Longrightarrow> (d :: nat) - b = c - a \<Longrightarrow> a - b = c - d"
  by arith

lemma minus_minus_swap':
  "\<lbrakk> c \<le> a; d \<le> b; b \<le> a; d \<le> c\<rbrakk> \<Longrightarrow> (b :: nat) - d = a - c \<Longrightarrow> a - b = c - d"
  by arith

lemma lineStart_mask:
  "lineStart x && mask 5 = 0"
  by (clarsimp simp: lineStart_def cacheLineBits_def shiftr_shiftl1 mask_AND_NOT_mask)

lemma cachRangeOp_corres_helper:
  "\<lbrakk>w1 \<le> w2; w3 \<le> w3 + (w2 - w1); w1 && mask 5 = w3 && mask 5\<rbrakk>
   \<Longrightarrow> unat (lineStart w2 - lineStart w1) div 32 =
           unat (lineStart (w3 + (w2 - w1)) - lineStart w3) div 32"
  apply (subst dvd_div_div_eq_mult, simp)
    apply (clarsimp simp: and_mask_dvd_nat[where n=5, simplified])
    apply (clarsimp simp: lineStart_def cacheLineBits_def shiftr_shiftl1)
    apply (subst mask_eqs(8)[symmetric])
    apply (clarsimp simp: mask_AND_NOT_mask)
   apply (clarsimp simp: and_mask_dvd_nat[where n=5, simplified])
   apply (subst mask_eqs(8)[symmetric])
   apply (clarsimp simp: lineStart_mask)
  apply (subgoal_tac "w3 + (w2 - w1) && mask 5 = w2 && mask 5")
   apply clarsimp
   apply (rule_tac x=w1 and y=w3 in linorder_le_cases)
    apply (subgoal_tac "lineStart (w3 + (w2 - w1)) - lineStart w2 = lineStart w3 - lineStart w1")
     apply (rule word_unat.Rep_eqD)
     apply (subst unat_sub, clarsimp simp: lineStart_le_mono)+
     apply (rule minus_minus_swap)
         apply (clarsimp simp: word_le_nat_alt[symmetric] intro!: lineStart_le_mono)
         apply (clarsimp simp: word_le_nat_alt unat_plus_simple[THEN iffD1] unat_sub)
         apply arith
        apply (clarsimp simp: word_le_nat_alt[symmetric] lineStart_le_mono)
       apply (clarsimp simp: word_le_nat_alt[symmetric] lineStart_le_mono)
      apply (clarsimp simp: word_le_nat_alt[symmetric] lineStart_le_mono)
     apply (subst unat_sub[symmetric], clarsimp simp: intro!: lineStart_le_mono)+
      apply (clarsimp simp: word_le_nat_alt unat_plus_simple[THEN iffD1] unat_sub)
      apply arith
     apply clarsimp
    apply (clarsimp simp: lineStart_sub[symmetric] field_simps)
   apply (subgoal_tac "lineStart w2 - lineStart (w3 + (w2 - w1)) = lineStart w1 - lineStart w3")
    apply (rule word_unat.Rep_eqD)
    apply (subst unat_sub, clarsimp simp: lineStart_le_mono)+
    apply (rule minus_minus_swap')
        apply (clarsimp simp: word_le_nat_alt[symmetric] intro!: lineStart_le_mono)
        apply (clarsimp simp: word_le_nat_alt unat_plus_simple[THEN iffD1] unat_sub)
        apply arith
       apply (clarsimp simp: word_le_nat_alt[symmetric] lineStart_le_mono)
      apply (clarsimp simp: word_le_nat_alt[symmetric] lineStart_le_mono)
     apply (clarsimp simp: word_le_nat_alt[symmetric] lineStart_le_mono)
    apply (subst unat_sub[symmetric], clarsimp simp: intro!: lineStart_le_mono)+
     apply (clarsimp simp: word_le_nat_alt unat_plus_simple[THEN iffD1] unat_sub)
     apply arith
    apply clarsimp
   apply (clarsimp simp: lineStart_sub[symmetric] field_simps)
  apply (subst mask_eqs(7)[symmetric])
  apply (subst mask_eqs(8)[symmetric])
  apply (clarsimp simp: mask_eqs)
  done

definition "lineIndex x \<equiv> lineStart x >> cacheLineBits"


lemma shiftr_shiftl_shiftr[simp]:
  "x >> a << a >> a = (x :: ('a :: len) word) >> a"
  apply (rule word_eqI)
  apply (simp add: word_size nth_shiftr nth_shiftl)
  apply safe
  apply (drule test_bit_size)
  apply (simp add: word_size)
  done

lemma lineIndex_def2:
  "lineIndex x = x >> cacheLineBits"
  by (simp add: lineIndex_def lineStart_def)


lemma lineIndex_le_mono:
  "x \<le> y \<Longrightarrow> lineIndex x \<le> lineIndex y"
  by (clarsimp simp: lineIndex_def2 cacheLineBits_def le_shiftr)

lemma add_right_shift:
  "\<lbrakk>x && mask n = 0; y && mask n = 0; x \<le> x + y \<rbrakk>
    \<Longrightarrow> (x + y :: ('a :: len) word) >> n = (x >> n) + (y >> n)"
  apply (simp add: no_olen_add_nat is_aligned_mask[symmetric])
  apply (simp add: unat_arith_simps shiftr_div_2n' split del: if_split)
  apply (subst if_P)
   apply (erule order_le_less_trans[rotated])
   apply (simp add: add_mono)
  apply (simp add: shiftr_div_2n' is_aligned_def)
  done

lemma sub_right_shift:
  "\<lbrakk>x && mask n = 0; y && mask n = 0; y \<le> x \<rbrakk>
    \<Longrightarrow> (x - y) >> n = (x >> n :: ('a :: len) word) - (y >> n)"
  using add_right_shift[where x="x - y" and y=y and n=n]
  by (simp add: aligned_sub_aligned is_aligned_mask[symmetric]
                word_sub_le)

lemma lineIndex_lineStart_diff:
  "w1 \<le> w2 \<Longrightarrow> (unat (lineStart w2 - lineStart w1) div 32) = unat (lineIndex w2 - lineIndex w1)"
  apply (subst shiftr_div_2n'[symmetric, where n=5, simplified])
  apply (drule lineStart_le_mono)
  apply (drule sub_right_shift[OF lineStart_mask lineStart_mask])
  apply (simp add: lineIndex_def cacheLineBits_def)
  done

lemma cacheRangeOp_ccorres:
  "\<lbrakk>\<And>x y. empty_fail (oper x y);
    \<forall>n. ccorres dc xfdc \<top> (\<lbrace>\<acute>index = lineIndex w1 + of_nat n\<rbrace>) hs
                (doMachineOp (oper (lineStart w1 + of_nat n * 0x20)
                                   (lineStart w3 + of_nat n * 0x20)))
                f;
   \<forall>s. \<Gamma>\<turnstile>\<^bsub>/UNIV\<^esub> {s} f ({t. index_' t = index_' s}) \<rbrakk> \<Longrightarrow>
   ccorres dc xfdc (\<lambda>_. w1 \<le> w2 \<and> w3 \<le> w3 + (w2 - w1)
                      \<and> w1 && mask 5 = w3 && mask 5)
                   (\<lbrace>\<acute>index = w1 >> 5\<rbrace>) hs
           (doMachineOp (cacheRangeOp oper w1 w2 w3))
           (While \<lbrace>\<acute>index < (w2 >> 5) + 1\<rbrace>
             (f;; \<acute>index :== \<acute>index + 1))"
  apply (clarsimp simp: cacheRangeOp_def doMachineOp_mapM_x split_def
                        cacheLine_def cacheLineBits_def)
  apply (rule ccorres_gen_asm[where G=\<top>, simplified])
  apply (rule ccorres_guard_imp)
    apply (rule ccorres_rel_imp)
     apply (rule_tac i="unat (lineIndex w1)" and F="\<lambda>_. \<top>"
             in ccorres_mapM_x_while_gen'[OF _ _ _ _ _ index_xf_for_sequence,
                                           where j=1, simplified], simp_all)
      apply clarsimp
      apply (clarsimp simp: length_upto_enum_step lineStart_le_mono)
      apply (clarsimp simp: upto_enum_step_nth lineStart_le_mono)
     apply (clarsimp simp: length_upto_enum_step lineStart_le_mono unat_div)
     apply (subst min_absorb1[OF order_eq_refl])
      apply (erule (2) cachRangeOp_corres_helper)
     apply (simp add: lineIndex_lineStart_diff)
     apply (simp add: lineIndex_def2 cacheLineBits_def)
     apply unat_arith
    apply wp
   apply (clarsimp simp: length_upto_enum_step lineStart_le_mono unat_div)
   apply (subst min_absorb1[OF order_eq_refl])
    apply (erule (2) cachRangeOp_corres_helper)
   apply (simp add: lineIndex_lineStart_diff unat_sub[OF lineIndex_le_mono])
   apply (subst le_add_diff_inverse)
    apply (simp add: lineIndex_le_mono word_le_nat_alt[symmetric])
   apply (simp add: lineIndex_def2 cacheLineBits_def)
   apply (rule unat_mono[where 'a=32 and b="0xFFFFFFFF", simplified])
   apply word_bitwise
  apply (simp add: lineIndex_def cacheLineBits_def lineStart_def)
  done


lemma lineStart_eq_minus_mask:
  "lineStart w1 = w1 - (w1 && mask 5)"
  by (simp add: lineStart_def cacheLineBits_def mask_out_sub_mask[symmetric] and_not_mask)

lemma lineStart_idem[simp]:
  "lineStart (lineStart x) = lineStart x"
  by (simp add: lineStart_def cacheLineBits_def)


lemma cache_range_lineIndex_helper:
  "lineIndex w1 + of_nat n << 5 = w1 - (w1 && mask 5) + of_nat n * 0x20"
  apply (clarsimp simp: lineIndex_def cacheLineBits_def word_shiftl_add_distrib lineStart_def[symmetric, unfolded cacheLineBits_def] lineStart_eq_minus_mask[symmetric])
  apply (simp add: shiftl_t2n)
  done


lemma cleanCacheRange_PoC_ccorres:
  "ccorres dc xfdc (\<lambda>_. w1 \<le> w2 \<and> w3 \<le> w3 + (w2 - w1)
                      \<and> w1 && mask 5 = w3 && mask 5)
                   (\<lbrace>\<acute>start = w1\<rbrace> \<inter> \<lbrace>\<acute>end = w2\<rbrace> \<inter> \<lbrace>\<acute>pstart = w3\<rbrace>) []
           (doMachineOp (cleanCacheRange_PoC w1 w2 w3))
           (Call cleanCacheRange_PoC_'proc)"
  apply (rule ccorres_gen_asm[where G=\<top>, simplified])
  apply (cinit' lift: start_' end_' pstart_')
   apply (clarsimp simp: cleanCacheRange_PoC_def word_sle_def whileAnno_def)
   apply (ccorres_remove_UNIV_guard)
   apply csymbr
   apply (rule cacheRangeOp_ccorres[simplified dc_def])
     apply (rule empty_fail_cleanByVA)
    apply clarsimp
  apply (cinitlift index_')
    apply (rule ccorres_guard_imp2)
     apply csymbr
     apply (ctac add: cleanByVA_ccorres[unfolded dc_def])
    apply (clarsimp simp: lineStart_def cacheLineBits_def shiftr_shiftl1
                          mask_out_sub_mask)
    apply (drule_tac s="w1 && mask 5" in sym, simp add: cache_range_lineIndex_helper)
   apply (vcg exspec=cleanByVA_modifies)
  apply clarsimp
  done

lemma cleanInvalidateCacheRange_RAM_ccorres:
  "ccorres dc xfdc ((\<lambda>s. unat (w2 - w1) \<le> gsMaxObjectSize s)
                      and (\<lambda>_. w1 \<le> w2 \<and> w3 \<le> w3 + (w2 - w1) 
                      \<and> w1 && mask 5 = w3 && mask 5 \<and> unat (w2 - w2) \<le> gsMaxObjectSize s))
                   (\<lbrace>\<acute>start = w1\<rbrace> \<inter> \<lbrace>\<acute>end = w2\<rbrace> \<inter> \<lbrace>\<acute>pstart = w3\<rbrace>) []
           (doMachineOp (cleanInvalidateCacheRange_RAM w1 w2 w3))
           (Call cleanInvalidateCacheRange_RAM_'proc)"
  apply (rule ccorres_gen_asm)
  apply (cinit' lift: start_' end_' pstart_')
   apply (clarsimp simp: word_sle_def whileAnno_def)
   apply (ccorres_remove_UNIV_guard)
   apply (rule ccorres_Guard_Seq)
   apply (rule ccorres_basic_srnoop)
     apply (simp add: cleanInvalidateCacheRange_RAM_def doMachineOp_bind
                      empty_fail_dsb empty_fail_cleanCacheRange_PoC empty_fail_cleanInvalidateL2Range
                      empty_fail_cacheRangeOp empty_fail_cleanInvalByVA)
     apply (ctac (no_vcg) add: cleanCacheRange_PoC_ccorres)
      apply (ctac (no_vcg) add: dsb_ccorres)
       apply (ctac (no_vcg) add: cleanInvalidateL2Range_ccorres)
        apply csymbr
        apply (rule ccorres_split_nothrow_novcg)
            apply (rule cacheRangeOp_ccorres)
              apply (rule empty_fail_cleanInvalByVA)
             apply clarsimp
             apply (cinitlift index_')
             apply (rule ccorres_guard_imp2)
              apply csymbr
              apply (ctac add: cleanInvalByVA_ccorres)
             apply (clarsimp simp: lineStart_def cacheLineBits_def shiftr_shiftl1
                                   mask_out_sub_mask)
             apply (drule_tac s="w1 && mask 5" in sym, simp add: cache_range_lineIndex_helper)          
            apply (vcg exspec=cleanInvalByVA_modifies)
           apply (rule ceqv_refl)
          apply (ctac (no_vcg) add: dsb_ccorres[simplified dc_def])
       apply (wp | clarsimp simp: guard_is_UNIVI o_def)+
  apply (frule(1) ghost_assertion_size_logic)
  apply (clarsimp simp: o_def)
  done

lemma cleanCacheRange_RAM_ccorres:
  "ccorres dc xfdc (\<lambda>s. w1 \<le> w2 \<and> w3 \<le> w3 + (w2 - w1)
                      \<and> w1 && mask 5 = w3 && mask 5
                      \<and> unat (w2 - w1) \<le> gsMaxObjectSize s)
                   (\<lbrace>\<acute>start = w1\<rbrace> \<inter> \<lbrace>\<acute>end = w2\<rbrace> \<inter> \<lbrace>\<acute>pstart = w3\<rbrace>) []
           (doMachineOp (cleanCacheRange_RAM w1 w2 w3))
           (Call cleanCacheRange_RAM_'proc)"
  apply (cinit' lift: start_' end_' pstart_')
   apply (simp add: cleanCacheRange_RAM_def doMachineOp_bind
                    empty_fail_dsb empty_fail_cleanCacheRange_PoC empty_fail_cleanL2Range)
   apply (rule ccorres_Guard_Seq)
   apply (rule ccorres_basic_srnoop2, simp)
   apply (ctac (no_vcg) add: cleanCacheRange_PoC_ccorres)
    apply (ctac (no_vcg) add: dsb_ccorres)
     apply (rule_tac P="\<lambda>s. unat (w2 - w1) \<le> gsMaxObjectSize s"
        in ccorres_cross_over_guard)
     apply (rule ccorres_Guard_Seq)
     apply (rule ccorres_basic_srnoop2, simp)
     apply (ctac (no_vcg) add: cleanL2Range_ccorres[unfolded dc_def])
    apply wp+
  apply clarsimp
  apply (auto dest: ghost_assertion_size_logic simp: o_def)
  done

lemma cleanCacheRange_PoU_ccorres:
  "ccorres dc xfdc ((\<lambda>s. unat (w2 - w1) \<le> gsMaxObjectSize s)
                    and (\<lambda>_. w1 \<le> w2 \<and> w3 \<le> w3 + (w2 - w1)
                      \<and> w1 && mask 5 = w3 && mask 5))
                   (\<lbrace>\<acute>start = w1\<rbrace> \<inter> \<lbrace>\<acute>end = w2\<rbrace> \<inter> \<lbrace>\<acute>pstart = w3\<rbrace>) []
           (doMachineOp (cleanCacheRange_PoU w1 w2 w3))
           (Call cleanCacheRange_PoU_'proc)"
  apply (rule ccorres_gen_asm)
  apply (cinit' lift: start_' end_' pstart_')
   apply (clarsimp simp: word_sle_def whileAnno_def)
   apply (ccorres_remove_UNIV_guard)
   apply (rule ccorres_Guard_Seq)
   apply (rule ccorres_basic_srnoop2, simp)
   apply (simp add: cleanCacheRange_PoU_def)
   apply csymbr
   apply (rule cacheRangeOp_ccorres[simplified dc_def])
     apply (rule empty_fail_cleanByVA_PoU)
    apply clarsimp
    apply (cinitlift index_')
    apply (rule ccorres_guard_imp2)
     apply csymbr
     apply (ctac add: cleanByVA_PoU_ccorres[unfolded dc_def])
    apply (clarsimp simp: lineStart_def cacheLineBits_def shiftr_shiftl1
                          mask_out_sub_mask)
    apply (drule_tac s="w1 && mask 5" in sym, simp add: cache_range_lineIndex_helper)
   apply (vcg exspec=cleanByVA_PoU_modifies)
  apply clarsimp
  apply (frule(1) ghost_assertion_size_logic)
  apply (clarsimp simp: o_def)
  done

lemma dmo_if:
  "(doMachineOp (if a then b else c)) = (if a then (doMachineOp b) else (doMachineOp c))"
  by (simp split: if_split)

lemma invalidateCacheRange_RAM_ccorres:
  "ccorres dc xfdc ((\<lambda>s. unat (w2 - w1) \<le> gsMaxObjectSize s)
                    and (\<lambda>_. w1 \<le> w2 \<and> w3 \<le> w3 + (w2 - w1)
                      \<and> w1 && mask 5 = w3 && mask 5))
                   (\<lbrace>\<acute>start = w1\<rbrace> \<inter> \<lbrace>\<acute>end = w2\<rbrace> \<inter> \<lbrace>\<acute>pstart = w3\<rbrace>) []
           (doMachineOp (invalidateCacheRange_RAM w1 w2 w3))
           (Call invalidateCacheRange_RAM_'proc)"
  apply (rule ccorres_gen_asm)
  apply (cinit' lift: start_' end_' pstart_')
   apply (clarsimp simp: word_sle_def whileAnno_def split del: if_split)
   apply (ccorres_remove_UNIV_guard)
   apply (simp add: invalidateCacheRange_RAM_def doMachineOp_bind when_def
                    split_if_empty_fail empty_fail_cleanCacheRange_RAM
                    empty_fail_invalidateL2Range empty_fail_cacheRangeOp empty_fail_invalidateByVA
                    empty_fail_dsb dmo_if
              split del: if_split)
   apply (rule ccorres_split_nothrow_novcg)
       apply (rule ccorres_cond[where R=\<top>])
         apply (clarsimp simp: lineStart_def cacheLineBits_def)
        apply (rule ccorres_call[OF cleanCacheRange_RAM_ccorres, where xf'=xfdc], (clarsimp)+)
       apply (rule ccorres_return_Skip[unfolded dc_def])
      apply ceqv
     apply (rule ccorres_split_nothrow_novcg)
         apply (rule ccorres_cond[where R=\<top>])
           apply (clarsimp simp: lineStart_def cacheLineBits_def)
          apply csymbr
          apply (rule ccorres_call[OF cleanCacheRange_RAM_ccorres, where xf'=xfdc], (clarsimp)+)
         apply (rule ccorres_return_Skip[unfolded dc_def])
        apply ceqv
       apply (rule_tac P="\<lambda>s. unat (w2 - w1) \<le> gsMaxObjectSize s"
          in ccorres_cross_over_guard)
       apply (rule ccorres_Guard_Seq)
       apply (rule ccorres_basic_srnoop2, simp)
       apply (ctac add: invalidateL2Range_ccorres)
         apply (rule ccorres_Guard_Seq)
         apply (rule ccorres_basic_srnoop2, simp)
         apply (csymbr)
         apply (rule ccorres_split_nothrow_novcg)
             apply (rule cacheRangeOp_ccorres)
               apply (simp add: empty_fail_invalidateByVA)
              apply clarsimp
              apply (cinitlift index_')
              apply (rule ccorres_guard_imp2)
               apply csymbr
               apply (ctac add: invalidateByVA_ccorres)
              apply (clarsimp simp: lineStart_def cacheLineBits_def shiftr_shiftl1
                          mask_out_sub_mask)
              apply (drule_tac s="w1 && mask 5" in sym, simp add: cache_range_lineIndex_helper)
             apply (vcg exspec=invalidateByVA_modifies)
            apply ceqv
           apply (ctac add: dsb_ccorres[unfolded dc_def])
          apply wp
         apply (simp add: guard_is_UNIV_def)
        apply wp
       apply (vcg exspec=plat_invalidateL2Range_modifies)
      apply wp
     apply (simp add: guard_is_UNIV_def)
     apply (auto dest: ghost_assertion_size_logic simp: o_def)[1]
    apply (wp | clarsimp split: if_split)+
   apply (clarsimp simp: lineStart_def cacheLineBits_def guard_is_UNIV_def)
  apply (clarsimp simp: lineStart_mask)
  apply (subst mask_eqs(7)[symmetric])
  apply (subst mask_eqs(8)[symmetric])
  apply (simp add: lineStart_mask mask_eqs)
  done

lemma invalidateCacheRange_I_ccorres:
  "ccorres dc xfdc (\<lambda>_. w1 \<le> w2 \<and> w3 \<le> w3 + (w2 - w1)
                      \<and> w1 && mask 5 = w3 && mask 5)
                   (\<lbrace>\<acute>start = w1\<rbrace> \<inter> \<lbrace>\<acute>end = w2\<rbrace> \<inter> \<lbrace>\<acute>pstart = w3\<rbrace>) []
           (doMachineOp (invalidateCacheRange_I w1 w2 w3))
           (Call invalidateCacheRange_I_'proc)"
  apply (rule ccorres_gen_asm[where G=\<top>, simplified])
  apply (cinit' lift: start_' end_' pstart_')
   apply (clarsimp simp: word_sle_def whileAnno_def)
   apply (ccorres_remove_UNIV_guard)
   apply (simp add: invalidateCacheRange_I_def)
   apply csymbr
   apply (rule cacheRangeOp_ccorres[simplified dc_def])
     apply (rule empty_fail_invalidateByVA_I)
    apply clarsimp
    apply (cinitlift index_')
    apply (rule ccorres_guard_imp2)
     apply csymbr
     apply (ctac add: invalidateByVA_I_ccorres[unfolded dc_def])
    apply (clarsimp simp: lineStart_def cacheLineBits_def shiftr_shiftl1
                          mask_out_sub_mask)
    apply (drule_tac s="w1 && mask 5" in sym, simp add: cache_range_lineIndex_helper)
   apply (vcg exspec=invalidateByVA_I_modifies)
  apply clarsimp
  done
 
lemma branchFlushRange_ccorres:
  "ccorres dc xfdc (\<lambda>_. w1 \<le> w2 \<and> w3 \<le> w3 + (w2 - w1)
                      \<and> w1 && mask 5 = w3 && mask 5)
                   (\<lbrace>\<acute>start = w1\<rbrace> \<inter> \<lbrace>\<acute>end = w2\<rbrace> \<inter> \<lbrace>\<acute>pstart = w3\<rbrace>) []
           (doMachineOp (branchFlushRange w1 w2 w3))
           (Call branchFlushRange_'proc)"
  apply (rule ccorres_gen_asm[where G=\<top>, simplified])
  apply (cinit' lift: start_' end_' pstart_')
   apply (clarsimp simp: word_sle_def whileAnno_def)
   apply (ccorres_remove_UNIV_guard)
   apply (simp add: branchFlushRange_def)
   apply csymbr
   apply (rule cacheRangeOp_ccorres[simplified dc_def])
     apply (rule empty_fail_branchFlush)
    apply clarsimp
    apply (cinitlift index_')
    apply (rule ccorres_guard_imp2)
     apply csymbr
     apply (ctac add: branchFlush_ccorres[unfolded dc_def])
    apply (clarsimp simp: lineStart_def cacheLineBits_def shiftr_shiftl1
                          mask_out_sub_mask)
    apply (drule_tac s="w1 && mask 5" in sym, simp add: cache_range_lineIndex_helper)
   apply (vcg exspec=branchFlush_modifies)
  apply clarsimp
  done

lemma cleanCaches_PoU_ccorres:
  "ccorres dc xfdc \<top> UNIV []
           (doMachineOp cleanCaches_PoU)
           (Call cleanCaches_PoU_'proc)"
  apply cinit'
   apply (simp add: cleanCaches_PoU_def doMachineOp_bind
                   empty_fail_dsb empty_fail_clean_D_PoU empty_fail_invalidate_I_PoU)
   apply (ctac (no_vcg) add: dsb_ccorres)
    apply (ctac (no_vcg) add: clean_D_PoU_ccorres)
     apply (ctac (no_vcg) add: dsb_ccorres)
      apply (ctac (no_vcg) add: invalidate_I_PoU_ccorres)
       apply (ctac (no_vcg) add: dsb_ccorres)
      apply wp+
  apply clarsimp
  done


lemma setCurrentPD_ccorres:
  "ccorres dc xfdc \<top> (\<lbrace>\<acute>addr = pd\<rbrace>) []
           (doMachineOp (setCurrentPD pd))
           (Call setCurrentPD_'proc)"
  apply cinit'
   apply (clarsimp simp: setCurrentPD_def doMachineOp_bind empty_fail_dsb empty_fail_isb
                    writeTTBR0_empty_fail
                   intro!: ccorres_cond_empty)
   apply (rule ccorres_rhs_assoc)
   apply (ctac (no_vcg) add: dsb_ccorres)
    apply (ctac (no_vcg) add: writeTTBR0_ccorres)
     apply (ctac (no_vcg) add: isb_ccorres)
    apply wp+
  apply clarsimp
  done

end

end
