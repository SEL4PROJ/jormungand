(*
 * Copyright 2014, General Dynamics C4 Systems
 *
 * This software may be distributed and modified according to the terms of
 * the GNU General Public License version 2. Note that NO WARRANTY is provided.
 * See "LICENSE_GPLv2.txt" for details.
 *
 * @TAG(GD_GPL)
 *)


theory CSpace_C
imports CSpaceAcc_C Machine_C
begin

context kernel_m
begin

lemma maskCapRights_cap_cases:
  "return (maskCapRights R c) =
  (case c of
    ArchObjectCap ac \<Rightarrow> return (Arch.maskCapRights R ac)
  | EndpointCap _ _ _ _ _ \<Rightarrow> 
    return (capEPCanGrant_update
       (\<lambda>_. capEPCanGrant c \<and> capAllowGrant R)
            (capEPCanReceive_update
               (\<lambda>_. capEPCanReceive c \<and> capAllowRead R)
                    (capEPCanSend_update
                          (\<lambda>_. capEPCanSend c \<and> capAllowWrite R) c)))
  | NotificationCap _ _ _ _ \<Rightarrow>
    return (capNtfnCanReceive_update
                        (\<lambda>_. capNtfnCanReceive c \<and> capAllowRead R)
                        (capNtfnCanSend_update
                          (\<lambda>_. capNtfnCanSend c \<and> capAllowWrite R) c))
  | _ \<Rightarrow> return c)"
  apply (simp add: maskCapRights_def Let_def split del: if_split)
  apply (cases c; simp add: isCap_simps split del: if_split)
  done


lemma imp_ignore: "B \<Longrightarrow> A \<longrightarrow> B" by blast

lemma wordFromVMRights_spec:
  "\<forall>s. \<Gamma> \<turnstile> {s} Call wordFromVMRights_'proc \<lbrace>\<acute>ret__unsigned_long = \<^bsup>s\<^esup>vm_rights\<rbrace>"
  by vcg simp?

lemma vmRightsFromWord_spec:
  "\<forall>s. \<Gamma> \<turnstile> {s} Call vmRightsFromWord_'proc \<lbrace>\<acute>ret__unsigned_long = \<^bsup>s\<^esup>w\<rbrace>"
  by vcg simp?

lemmas vmrights_defs =
  Kernel_C.VMNoAccess_def 
  Kernel_C.VMReadOnly_def
  Kernel_C.VMKernelOnly_def
  Kernel_C.VMReadWrite_def

lemma maskVMRights_spec:
  "\<forall>s. \<Gamma> \<turnstile> ({s} \<inter> 
           \<lbrace> \<acute>vm_rights && mask 2 = \<acute>vm_rights \<rbrace>)
  Call maskVMRights_'proc
  \<lbrace> vmrights_to_H \<acute>ret__unsigned_long = 
    maskVMRights (vmrights_to_H \<^bsup>s\<^esup>vm_rights) (cap_rights_to_H (seL4_CapRights_lift \<^bsup>s\<^esup>cap_rights_mask)) \<and>
    \<acute>ret__unsigned_long && mask 2 = \<acute>ret__unsigned_long \<rbrace>"
  apply vcg
  apply clarsimp
  apply (rule conjI) 
   apply ((auto simp: vmrights_to_H_def maskVMRights_def vmrights_defs 
                      cap_rights_to_H_def to_bool_def
               split: bool.split 
         | simp add: mask_def
         | word_bitwise)+)[1]
  apply clarsimp
  apply (subgoal_tac "vm_rights = 0 \<or> vm_rights = 1 \<or> vm_rights = 2 \<or> vm_rights = 3")
   apply (auto simp: vmrights_to_H_def maskVMRights_def vmrights_defs
                     cap_rights_to_H_def seL4_CapRights_lift_def
                     to_bool_def mask_def
                   split: bool.splits)[1]
  apply (subst(asm) mask_eq_iff_w2p)
   apply (simp add: word_size)
  apply (rule ccontr, clarsimp)
  apply (drule inc_le, simp, drule(1) order_le_neq_trans [OF _ not_sym])+
  apply (drule inc_le, simp)
  done


lemma small_frame_cap_rights [simp]:
  "cap_get_tag cap = scast cap_small_frame_cap
  \<Longrightarrow> cap_small_frame_cap_CL.capFVMRights_CL (cap_small_frame_cap_lift cap) && mask 2 =
     cap_small_frame_cap_CL.capFVMRights_CL (cap_small_frame_cap_lift cap)"
  apply (simp add: cap_small_frame_cap_lift_def)
  by (simp add: cap_lift_def cap_tag_defs mask_def word_bw_assocs)

lemma frame_cap_rights [simp]:
  "cap_get_tag cap = scast cap_frame_cap
  \<Longrightarrow> cap_frame_cap_CL.capFVMRights_CL (cap_frame_cap_lift cap) && mask 2 =
     cap_frame_cap_CL.capFVMRights_CL (cap_frame_cap_lift cap)"
  apply (simp add: cap_frame_cap_lift_def)
  by (simp add: cap_lift_def cap_tag_defs mask_def word_bw_assocs)

lemma Arch_maskCapRights_ccorres [corres]:
  "ccorres ccap_relation ret__struct_cap_C_'
  \<top>
  (UNIV \<inter> \<lbrace>ccap_relation (ArchObjectCap arch_cap) \<acute>cap\<rbrace> \<inter>
  \<lbrace>ccap_rights_relation R \<acute>cap_rights_mask\<rbrace>)
  []
  (return (Arch.maskCapRights R arch_cap))
  (Call Arch_maskCapRights_'proc)"
  apply (cinit' (trace) lift: cap_' cap_rights_mask_')
   apply csymbr
   apply (unfold ARM_H.maskCapRights_def)
   apply (simp only: Let_def)
   apply (case_tac "cap_get_tag cap = scast cap_small_frame_cap")
    apply (clarsimp simp add: ccorres_cond_iffs cap_get_tag_isCap isCap_simps)
    apply (rule ccorres_from_vcg_throws [where P=\<top> and P'=UNIV])
    apply (rule allI, rule conseqPre, vcg)
    apply (clarsimp simp: cap_get_tag_isCap isCap_simps)
    apply (clarsimp simp: return_def)
    apply (unfold ccap_relation_def)[1]
    apply (simp add: cap_small_frame_cap_lift [THEN iffD1])
    apply (clarsimp simp: cap_to_H_def)
    apply (simp add: map_option_case split: option.splits)
    apply (clarsimp simp add: cap_to_H_def Let_def split: cap_CL.splits if_split_asm)
       apply (simp add: cap_small_frame_cap_lift_def)
       apply (simp add: ccap_rights_relation_def)
      apply (simp add: cap_small_frame_cap_lift_def)
      apply (simp add: ccap_rights_relation_def)
     apply (simp add: pageSize_def)
    apply (simp add: pageSize_def)
   apply (clarsimp simp add: cap_get_tag_isCap isCap_simps simp del: not_ex)
   apply (rule conjI, clarsimp)
    apply (simp add: ccorres_cond_iffs)
    apply (rule ccorres_guard_imp)
      apply (csymbr)
      apply (case_tac "cap_get_tag cap = scast cap_frame_cap")
       apply (clarsimp simp add: ccorres_cond_iffs cap_get_tag_isCap isCap_simps simp del: not_ex)
       apply (rule ccorres_from_vcg_throws [where P=\<top> and P'=UNIV])
       apply (rule allI, rule conseqPre, vcg)
       apply (clarsimp simp: cap_get_tag_isCap isCap_simps simp del: not_ex)
       apply (clarsimp simp: return_def)
       apply (unfold ccap_relation_def)[1]
       apply (simp add: cap_frame_cap_lift [THEN iffD1])
       apply (clarsimp simp: cap_to_H_def)
       apply (simp add: map_option_case split: option.splits)
       apply (clarsimp simp add: isCap_simps pageSize_def cap_to_H_def Let_def simp del: not_ex
                          split: cap_CL.splits if_split_asm)
        apply (simp add: cap_frame_cap_lift_def)
        apply (simp add: ccap_rights_relation_def)
        apply (simp add: c_valid_cap_def cl_valid_cap_def cap_lift_frame_cap)
       apply (simp add: cap_frame_cap_lift_def)
       apply (simp add: ccap_rights_relation_def)
       apply (simp add: c_valid_cap_def cl_valid_cap_def cap_lift_frame_cap)
      apply (clarsimp simp add: cap_get_tag_isCap isCap_simps simp del: not_ex)+
   apply (simp add: ccorres_cond_iffs)
   apply (rule ccorres_from_vcg_throws)
   apply (rule allI, rule conseqPre, vcg)
   apply (clarsimp simp add: return_def simp del: not_ex)
   apply (cases arch_cap)
       by (fastforce simp add: cap_get_tag_isCap isCap_simps  simp del: not_ex omgwtfbbq)+

lemma to_bool_mask_to_bool_bf:
  "to_bool (x && mask (Suc 0)) = to_bool_bf (x::word32)"
  apply (simp add: to_bool_bf_def to_bool_def)
  apply (rule iffI)
   prefer 2
   apply simp  
  apply (subgoal_tac "x && mask (Suc 0) < 2^(Suc 0)")
   apply simp
   apply (drule word_less_cases [where y=2])
   apply auto[1]
  apply (rule and_mask_less')
  apply simp
  done

lemma to_bool_cap_rights_bf:
  "to_bool (capAllowRead_CL (seL4_CapRights_lift R)) =
   to_bool_bf (capAllowRead_CL (seL4_CapRights_lift R))"
  "to_bool (capAllowWrite_CL (seL4_CapRights_lift R)) =
   to_bool_bf (capAllowWrite_CL (seL4_CapRights_lift R))"
  "to_bool (capAllowGrant_CL (seL4_CapRights_lift R)) =
   to_bool_bf (capAllowGrant_CL (seL4_CapRights_lift R))"
  by (subst to_bool_bf_to_bool_mask, 
      simp add: seL4_CapRights_lift_def mask_def word_bw_assocs, simp)+

lemma to_bool_ntfn_cap_bf:
  "cap_lift c = Some (Cap_notification_cap cap) \<Longrightarrow> 
  to_bool (capNtfnCanSend_CL cap) = to_bool_bf (capNtfnCanSend_CL cap) \<and>
  to_bool (capNtfnCanReceive_CL cap) = to_bool_bf (capNtfnCanReceive_CL cap)"
  apply (simp add:cap_lift_def Let_def split: if_split_asm)
  apply (subst to_bool_bf_to_bool_mask,
         clarsimp simp: cap_lift_thread_cap mask_def word_bw_assocs)+
  apply simp
  done
   
lemma to_bool_ep_cap_bf:
  "cap_lift c = Some (Cap_endpoint_cap cap) \<Longrightarrow> 
  to_bool (capCanSend_CL cap) = to_bool_bf (capCanSend_CL cap) \<and>
  to_bool (capCanReceive_CL cap) = to_bool_bf (capCanReceive_CL cap) \<and>
  to_bool (capCanGrant_CL cap) = to_bool_bf (capCanGrant_CL cap)"
  apply (simp add:cap_lift_def Let_def split: if_split_asm)
  apply (subst to_bool_bf_to_bool_mask,
         clarsimp simp: cap_lift_thread_cap mask_def word_bw_assocs)+
  apply simp
  done

lemma isArchCap_spec:
  "\<forall>s. \<Gamma>\<turnstile> {s} Call isArchCap_'proc \<lbrace>\<acute>ret__unsigned_long = from_bool (isArchCap_tag (cap_get_tag (cap_' s)))\<rbrace>"
  apply vcg
  apply (clarsimp simp: from_bool_def isArchCap_tag_def bool.split)
  apply (clarsimp simp: word_mod_2p_is_mask[where n=1, simplified] mask_def)
  apply word_bitwise
  done

lemma maskCapRights_ccorres [corres]:
  "ccorres ccap_relation ret__struct_cap_C_' 
           \<top> 
           (UNIV \<inter> \<lbrace>ccap_relation cap \<acute>cap\<rbrace> \<inter> \<lbrace>ccap_rights_relation R \<acute>cap_rights\<rbrace>) 
           [] 
           (return (RetypeDecls_H.maskCapRights R cap)) (Call maskCapRights_'proc)"
  apply (cinit' lift: cap_' cap_rights_')
  apply csymbr
  apply (simp add: maskCapRights_cap_cases cap_get_tag_isCap del: Collect_const)
  apply wpc
              apply (simp add: Collect_const_mem from_bool_def)
              apply csymbr
              apply (simp add: cap_get_tag_isCap isCap_simps del: Collect_const)
              apply (simp add: ccorres_cond_iffs) 
              apply (rule ccorres_from_vcg_throws [where P=\<top> and P'=UNIV])
              apply (rule allI)
              apply (rule conseqPre)
               apply vcg
              apply clarsimp
              apply (simp add: cap_get_tag_isCap isCap_simps return_def)
             apply (simp add: Collect_const_mem from_bool_def)
             apply csymbr
             apply (simp add: cap_get_tag_isCap isCap_simps del: Collect_const)
             apply (simp add: ccorres_cond_iffs) 
             apply (rule ccorres_from_vcg_throws [where P=\<top> and P'=UNIV])
             apply (rule allI)
             apply (rule conseqPre)
              apply vcg
             apply (clarsimp simp: return_def)
            apply (simp add: Collect_const_mem from_bool_def)
            apply csymbr
            apply (simp add: cap_get_tag_isCap isCap_simps del: Collect_const)
            apply (simp add: ccorres_cond_iffs) 
            apply (rule ccorres_from_vcg_throws [where P=\<top> and P'=UNIV])
            apply (rule allI)
            apply (rule conseqPre)
             apply vcg
            apply clarsimp
            apply (simp add: cap_get_tag_isCap isCap_simps return_def)
            apply (rule imp_ignore)
            apply (rule imp_ignore)
            apply (rule imp_ignore)
            apply (rule imp_ignore)
            apply (rule imp_ignore)
            apply clarsimp
            apply (unfold ccap_relation_def)[1]
            apply (simp add: cap_notification_cap_lift [THEN iffD1])
            apply (clarsimp simp: cap_to_H_def)
            apply (simp add: map_option_case split: option.splits)
            apply (clarsimp simp add: cap_to_H_def Let_def
                               split: cap_CL.splits if_split_asm)
            apply (simp add: cap_notification_cap_lift_def)
            apply (simp add: ccap_rights_relation_def cap_rights_to_H_def
                             to_bool_ntfn_cap_bf
                             to_bool_mask_to_bool_bf to_bool_cap_rights_bf)
           apply (simp add: Collect_const_mem from_bool_def)
           apply csymbr
           apply (simp add: cap_get_tag_isCap isCap_simps ccorres_cond_iffs)
           apply (rule ccorres_from_vcg_throws [where P=\<top> and P'=UNIV])
           apply (rule allI)
           apply (rule conseqPre)
            apply vcg
           apply (clarsimp simp: cap_get_tag_isCap isCap_simps return_def)
          apply (simp add: Collect_const_mem from_bool_def)
          apply csymbr
          apply (simp add: cap_get_tag_isCap isCap_simps ccorres_cond_iffs)
          apply (rule ccorres_from_vcg_throws [where P=\<top> and P'=UNIV])
          apply (rule allI)
          apply (rule conseqPre)
           apply vcg
          apply clarsimp
          apply (simp add: cap_get_tag_isCap isCap_simps return_def)
          apply (rule imp_ignore)
          apply (rule imp_ignore)
          apply (rule imp_ignore)
          apply (rule imp_ignore)
          apply (rule imp_ignore)
          apply (rule imp_ignore)
          apply (rule imp_ignore)
          apply (rule imp_ignore)
          apply clarsimp
          apply (unfold ccap_relation_def)[1]
          apply (simp add: cap_endpoint_cap_lift [THEN iffD1])
          apply (clarsimp simp: cap_to_H_def)
          apply (simp add: map_option_case split: option.splits)
          apply (clarsimp simp add: cap_to_H_def Let_def
                             split: cap_CL.splits if_split_asm)
          apply (simp add: cap_endpoint_cap_lift_def)
          apply (simp add: ccap_rights_relation_def cap_rights_to_H_def
                           to_bool_ep_cap_bf
                           to_bool_mask_to_bool_bf to_bool_cap_rights_bf)
         apply (simp add: Collect_const_mem from_bool_def)
         apply csymbr
         apply (simp add: cap_get_tag_isCap isCap_simps del: Collect_const)
         apply (simp add: ccorres_cond_iffs) 
         apply (rule ccorres_from_vcg_throws [where P=\<top> and P'=UNIV])
         apply (rule allI)
         apply (rule conseqPre)
          apply vcg
         apply (clarsimp simp: return_def)
        apply (simp add: Collect_const_mem from_bool_def)
        apply csymbr
        apply (simp add: cap_get_tag_isCap isCap_simps ccorres_cond_iffs)
        apply (rule ccorres_from_vcg_throws [where P=\<top> and P'=UNIV])
        apply (rule allI)
        apply (rule conseqPre)
         apply vcg
        apply (clarsimp simp: cap_get_tag_isCap isCap_simps return_def)
       apply (simp add: Collect_const_mem from_bool_def)
       apply (subst bind_return [symmetric])
       apply (rule ccorres_split_throws)
        apply ctac
          apply (rule_tac P=\<top> and P'="\<lbrace>\<acute>ret__struct_cap_C = ret__struct_cap_C\<rbrace>" in ccorres_inst)
          apply (rule ccorres_from_vcg_throws)
          apply (clarsimp simp: return_def)
          apply (rule conseqPre)
           apply vcg
          apply clarsimp
         apply wp
        apply vcg
       apply vcg
      apply (simp add: Collect_const_mem from_bool_def)
      apply csymbr
      apply (simp add: cap_get_tag_isCap isCap_simps del: Collect_const)
      apply (simp add: ccorres_cond_iffs) 
      apply (rule ccorres_from_vcg_throws [where P=\<top> and P'=UNIV])
      apply (rule allI)
      apply (rule conseqPre)
       apply vcg
      apply (clarsimp simp: return_def)
     apply (simp add: Collect_const_mem from_bool_def)
     apply csymbr
     apply (simp add: cap_get_tag_isCap isCap_simps del: Collect_const)
     apply (simp add: ccorres_cond_iffs) 
     apply (rule ccorres_from_vcg_throws [where P=\<top> and P'=UNIV])
     apply (rule allI)
     apply (rule conseqPre)
      apply vcg
     apply (clarsimp simp: return_def)
    apply (simp add: Collect_const_mem from_bool_def)
    apply csymbr
    apply (simp add: cap_get_tag_isCap isCap_simps del: Collect_const)
    apply (simp add: ccorres_cond_iffs) 
    apply (rule ccorres_from_vcg_throws [where P=\<top> and P'=UNIV])
    apply (rule allI)
    apply (rule conseqPre)
     apply vcg
    apply clarsimp
    apply (simp add: cap_get_tag_isCap isCap_simps return_def)
   apply (simp add: Collect_const_mem from_bool_def)
   apply csymbr
   apply (simp add: cap_get_tag_isCap isCap_simps del: Collect_const)
   apply (simp add: ccorres_cond_iffs) 
   apply (rule ccorres_from_vcg_throws [where P=\<top> and P'=UNIV])
   apply (rule allI)
   apply (rule conseqPre)
    apply vcg
   apply (clarsimp simp: return_def)
  apply clarsimp
  done

abbreviation
  "lookupCap_xf \<equiv> liftxf errstate lookupCap_ret_C.status_C lookupCap_ret_C.cap_C ret__struct_lookupCap_ret_C_'"

lemma ccorres_return_cte_cteCap [corres]:
  fixes ptr' :: "cstate \<Rightarrow> cte_C ptr"
  assumes r1: "\<And>s s' g. (s, s') \<in> rf_sr \<Longrightarrow> (s, xfu g s') \<in> rf_sr"
  and xf_xfu: "\<And>s g. xf (xfu g s) = g s"
  shows "ccorres ccap_relation xf 
         (\<lambda>s. ctes_of s ptr = Some cte) {s. ptr_val (ptr' s) = ptr}  hs 
         (return (cteCap cte))
         (Basic (\<lambda>s. xfu (\<lambda>_. h_val (hrs_mem (t_hrs_' (globals s))) 
           (Ptr &(ptr' s \<rightarrow>[''cap_C'']))) s))"
  apply (rule ccorres_return)
  apply (rule conseqPre)
   apply vcg
  apply (clarsimp simp: xf_xfu ccap_relation_def)
  apply rule
  apply (erule r1)  
  apply (drule (1) rf_sr_ctes_of_clift)
  apply (clarsimp simp: typ_heap_simps)
  apply (simp add: c_valid_cte_def)
done

     
lemma ccorres_return_cte_mdbnode [corres]:
  fixes ptr' :: "cstate \<Rightarrow> cte_C ptr"
  assumes r1: "\<And>s s' g. (s, s') \<in> rf_sr \<Longrightarrow> (s, xfu g s') \<in> rf_sr"
  and xf_xfu: "\<And>s g. xf (xfu g s) = g s"
  shows "ccorres cmdbnode_relation xf 
         (\<lambda>s. ctes_of s ptr = Some cte) {s. ptr_val (ptr' s) = ptr}  hs 
         (return (cteMDBNode cte))
         (Basic (\<lambda>s. xfu (\<lambda>_. h_val (hrs_mem (t_hrs_' (globals s))) 
           (Ptr &(ptr' s \<rightarrow>[''cteMDBNode_C'']))) s))"
  apply (rule ccorres_from_vcg)
  apply (rule allI, rule conseqPre, vcg)
  apply (clarsimp simp add: return_def xf_xfu)
  apply (frule (1) rf_sr_ctes_of_clift)
  apply (clarsimp simp: typ_heap_simps)
  apply (erule r1)
  done


(* FIXME: MOVE *)
lemma heap_update_field_ext:
  "\<lbrakk>field_ti TYPE('a :: packed_type) f = Some t; c_guard p; 
  export_uinfo t = export_uinfo (typ_info_t TYPE('b :: packed_type))\<rbrakk>
  \<Longrightarrow> heap_update (Ptr &(p\<rightarrow>f) :: 'b ptr) =
  (\<lambda>v hp. heap_update p (update_ti t (to_bytes_p v) (h_val hp p)) hp)"
  apply (rule ext, rule ext)
  apply (erule (2) heap_update_field)
  done

lemma ccorres_updateCap [corres]:
  fixes ptr :: "cstate \<Rightarrow> cte_C ptr" and val :: "cstate \<Rightarrow> cap_C"
  shows "ccorres dc xfdc \<top>
        ({s. ccap_relation cap (val s)} \<inter> {s. ptr s = Ptr dest}) hs
        (updateCap dest cap)
        (Basic 
  (\<lambda>s. globals_update 
   (t_hrs_'_update
     (hrs_mem_update (heap_update (Ptr &(ptr s\<rightarrow>[''cap_C''])) (val s)))) s))"
  unfolding updateCap_def
  apply (cinitlift ptr)
  apply (erule ssubst)
  apply (rule ccorres_guard_imp2)
  apply (rule ccorres_pre_getCTE)
  apply (rule_tac P = "\<lambda>s. ctes_of s dest = Some rva" in
    ccorres_from_vcg [where P' = "{s. ccap_relation cap (val s)}"])
  apply (rule allI)
  apply (rule conseqPre)
  apply vcg
  apply clarsimp
  apply (rule fst_setCTE [OF ctes_of_cte_at], assumption)
   apply (erule bexI [rotated])
   apply (clarsimp simp: cte_wp_at_ctes_of)
   apply (frule (1) rf_sr_ctes_of_clift)
   apply (clarsimp simp add: rf_sr_def cstate_relation_def 
     Let_def cpspace_relation_def
     cvariable_array_map_const_add_map_option[where f="tcb_no_ctes_proj"])
   apply (simp add:typ_heap_simps)
   apply (rule conjI)
    apply (erule (3) cpspace_cte_relation_upd_capI)
   apply (frule_tac f="ksPSpace" in arg_cong)
   apply (erule_tac t = s' in ssubst)
    apply simp
   apply (simp add: heap_to_user_data_def heap_to_device_data_def)
   apply (rule conjI)
    apply (erule (1) setCTE_tcb_case)
   subgoal by (simp add: carch_state_relation_def cmachine_state_relation_def
                         typ_heap_simps)
  by clarsimp

lemma ccorres_updateMDB_const [corres]:
  fixes ptr :: "cstate \<Rightarrow> cte_C ptr" and val :: "cstate \<Rightarrow> mdb_node_C"
  shows "ccorres dc xfdc (\<lambda>_. dest \<noteq> 0)
        ({s. cmdbnode_relation m (val s)} \<inter> {s. ptr s = Ptr dest}) hs
        (updateMDB dest (const m))
        (Basic 
  (\<lambda>s. globals_update 
   (t_hrs_'_update
     (hrs_mem_update (heap_update (Ptr &(ptr s\<rightarrow>[''cteMDBNode_C''])) (val s)))) s))"
  unfolding updateMDB_def
  apply (cinitlift ptr)
  apply (erule ssubst)
  apply (rule ccorres_gen_asm [where G = \<top>, simplified])
  apply (simp only: Let_def)
  apply simp  
  apply (rule ccorres_guard_imp2)
  apply (rule ccorres_pre_getCTE)
  apply (rule_tac P = "\<lambda>s. ctes_of s dest = Some cte" in ccorres_from_vcg [where P' = "{s. cmdbnode_relation m (val s)}"])
  apply (rule allI)
  apply (rule conseqPre)
  apply vcg
  apply clarsimp
   apply (rule fst_setCTE [OF ctes_of_cte_at], assumption )
   apply (erule bexI [rotated])
   apply (frule (1) rf_sr_ctes_of_clift)    
   apply (clarsimp simp add: rf_sr_def cstate_relation_def typ_heap_simps
     Let_def cpspace_relation_def
     cvariable_array_map_const_add_map_option[where f="tcb_no_ctes_proj"])
   apply (rule conjI)
    apply (erule (3) cspace_cte_relation_upd_mdbI)
   apply (erule_tac t = s' in ssubst)
   apply (simp add: heap_to_user_data_def)
   apply (rule conjI)
    apply (erule (1) setCTE_tcb_case)
   apply (simp add: carch_state_relation_def cmachine_state_relation_def
                    typ_heap_simps)
  apply (clarsimp)
  done

lemma cap_lift_capNtfnBadge_mask_eq:
  "cap_lift cap = Some (Cap_notification_cap ec)
  \<Longrightarrow> capNtfnBadge_CL ec && mask 28 = capNtfnBadge_CL ec"
  unfolding cap_lift_def
  by (fastforce simp: Let_def mask_def word_bw_assocs split: if_split_asm)

lemma cap_lift_capEPBadge_mask_eq:
  "cap_lift cap = Some (Cap_endpoint_cap ec)
  \<Longrightarrow> capEPBadge_CL ec && mask 28 = capEPBadge_CL ec"
  unfolding cap_lift_def
  by (fastforce simp: Let_def mask_def word_bw_assocs split: if_split_asm)

lemma revokable_ccorres:
  "\<lbrakk>ccap_relation cap newCap; cmdbnode_relation rva srcMDB;
  ccap_relation rvb srcCap; ret__unsigned = cap_get_tag newCap \<rbrakk> \<Longrightarrow>
  ccorres (\<lambda>a c. from_bool a = c) newCapIsRevocable_'
           (\<lambda>_. capMasterCap cap = capMasterCap rvb \<or> is_simple_cap' cap) UNIV hs
           (return (revokable' rvb cap))
           (IF ret__unsigned = scast cap_endpoint_cap THEN
              \<acute>ret__unsigned :== CALL cap_endpoint_cap_get_capEPBadge(newCap);;
              \<acute>unsigned_eret_2 :== CALL cap_endpoint_cap_get_capEPBadge(srcCap);;
              \<acute>newCapIsRevocable :==
                (if \<acute>ret__unsigned \<noteq> \<acute>unsigned_eret_2 then 1
                 else 0)
            ELSE
              IF ret__unsigned = scast cap_notification_cap THEN
                \<acute>ret__unsigned :== CALL cap_notification_cap_get_capNtfnBadge(newCap);;
                \<acute>unsigned_eret_2 :== CALL cap_notification_cap_get_capNtfnBadge(srcCap);;
                \<acute>newCapIsRevocable :==
                  (if \<acute>ret__unsigned \<noteq> \<acute>unsigned_eret_2 then 1
                   else 0)
              ELSE
                IF ret__unsigned = scast cap_irq_handler_cap THEN
                  \<acute>ret__unsigned :== CALL cap_get_capType(srcCap);;
                  \<acute>newCapIsRevocable :==
                    (if \<acute>ret__unsigned = scast cap_irq_control_cap then 1
                     else 0)
                ELSE
                  IF ret__unsigned = scast cap_untyped_cap THEN
                    \<acute>newCapIsRevocable :== scast true
                  ELSE
                    IF True THEN
                       \<acute>newCapIsRevocable :== scast false
                    FI
                  FI
                FI
              FI
            FI)"
  unfolding revokable'_fold
  apply (rule ccorres_gen_asm [where G = \<top>, simplified])
  apply (cases cap)
	     apply (simp add: cap_get_tag_isCap isCap_simps ccorres_cond_iffs from_bool_def true_def false_def,
	      rule ccorres_return, vcg, fastforce simp: cap_get_tag_isCap isCap_simps)
	    apply (simp add: cap_get_tag_isCap isCap_simps ccorres_cond_iffs from_bool_def true_def false_def,
	     rule ccorres_return, vcg, fastforce simp: cap_get_tag_isCap isCap_simps)
	   apply (simp add: cap_get_tag_isCap isCap_simps ccorres_cond_iffs from_bool_def true_def false_def)
	   apply (rule ccorres_return, vcg)
	   apply (frule cap_get_tag_NotificationCap [where cap' = srcCap, THEN iffD1])
 	    apply (clarsimp simp: cap_get_tag_isCap isCap_simps is_simple_cap'_def)
 	   apply (frule cap_get_tag_NotificationCap [where cap' = newCap, THEN iffD1])
    	    apply (clarsimp simp: cap_get_tag_isCap isCap_simps)
	   apply (fastforce simp: cap_get_tag_isCap isCap_simps)
	 
          apply (clarsimp simp: cap_get_tag_isCap isCap_simps ccorres_cond_iffs from_bool_def true_def false_def,
	  rule ccorres_return, vcg, fastforce simp: cap_get_tag_isCap isCap_simps)
	 apply (clarsimp simp: cap_get_tag_isCap isCap_simps ccorres_cond_iffs from_bool_def true_def false_def)
	 apply (rule ccorres_return, vcg)
	 apply (frule cap_get_tag_EndpointCap [where cap' = srcCap, THEN iffD1])
 	  apply (clarsimp simp: cap_get_tag_isCap isCap_simps is_simple_cap'_def)
	 apply (frule cap_get_tag_EndpointCap [where cap' = newCap, THEN iffD1])
    	  apply (clarsimp simp: cap_get_tag_isCap isCap_simps is_simple_cap'_def)
	 apply (fastforce simp: cap_get_tag_isCap isCap_simps)

	by (clarsimp simp: cap_get_tag_isCap isCap_simps ccorres_cond_iffs from_bool_def true_def false_def,
	  rule ccorres_return, vcg, fastforce simp: cap_get_tag_isCap isCap_simps)+

lemma from_bool_mask_simp [simp]:
  "((from_bool r) :: word32) && mask (Suc 0) = from_bool r"
  unfolding from_bool_def
  apply (rule less_mask_eq)
  apply (clarsimp split: bool.splits)
  done

lemma cteInsert_ccorres_mdb_helper:
  "\<lbrakk>cmdbnode_relation rva srcMDB; from_bool rvc = (newCapIsRevocable :: word32); srcSlot = Ptr src\<rbrakk> 
       \<Longrightarrow> ccorres cmdbnode_relation newMDB_' (K (is_aligned src 3))
           UNIV hs
           (return
             (mdbFirstBadged_update (\<lambda>_. rvc)
               (mdbRevocable_update (\<lambda>_. rvc)
                 (mdbPrev_update (\<lambda>_. src) rva))))
           (\<acute>newMDB :== CALL mdb_node_set_mdbPrev(srcMDB, 
            ptr_val srcSlot);;
            \<acute>newMDB :== CALL mdb_node_set_mdbRevocable(\<acute>newMDB,
            newCapIsRevocable);;
            \<acute>newMDB :== CALL mdb_node_set_mdbFirstBadged(\<acute>newMDB,
            newCapIsRevocable))"
  apply (rule ccorres_from_vcg)
  apply (rule allI)
  apply (rule conseqPre)
  apply vcg
  apply (clarsimp simp: return_def)
  apply (simp add: cmdbnode_relation_def)
  done

lemma ccorres_updateMDB_set_mdbNext [corres]:
  "src=src' \<Longrightarrow>
   ccorres dc xfdc ((\<lambda>_. src \<noteq> 0 \<and> (dest\<noteq>0 \<longrightarrow> is_aligned dest 3))) 
  ({s. mdb_node_ptr_' s = Ptr &((Ptr src' :: cte_C ptr)\<rightarrow>[''cteMDBNode_C''])} \<inter>
   {s. v_' s = dest}) []
  (updateMDB src (mdbNext_update (\<lambda>_. dest)))
  (Call mdb_node_ptr_set_mdbNext_'proc)"
  unfolding updateMDB_def
  apply (hypsubst)
  apply (rule ccorres_gen_asm [where G = \<top>, simplified])
  apply (simp only: Let_def)
  apply simp
  apply (rule ccorres_guard_imp2)
   apply (rule ccorres_pre_getCTE [where P = "\<lambda>cte s. ctes_of s src' = Some cte" and 
     P' = "\<lambda>_. (\<lbrace>\<acute>mdb_node_ptr = Ptr &((Ptr src' :: cte_C ptr)\<rightarrow>[''cteMDBNode_C''])\<rbrace> \<inter> \<lbrace>\<acute>v = dest\<rbrace>)"]) 
   apply (rule ccorres_from_spec_modifies_heap)
        apply (rule mdb_node_ptr_set_mdbNext_spec) 
       apply (rule mdb_node_ptr_set_mdbNext_modifies)
      apply simp
     apply clarsimp
     apply (rule rf_sr_cte_at_valid)
      apply simp
      apply (erule ctes_of_cte_at)
     apply assumption
    apply clarsimp
    apply (frule (1) rf_sr_ctes_of_clift)
    apply (clarsimp simp: typ_heap_simps)
    apply (rule fst_setCTE [OF ctes_of_cte_at], assumption)
    apply (erule bexI [rotated])
    apply (clarsimp simp add: rf_sr_def cstate_relation_def 
      Let_def cpspace_relation_def cte_wp_at_ctes_of heap_to_user_data_def
     cvariable_array_map_const_add_map_option[where f="tcb_no_ctes_proj"]
     typ_heap_simps')
    apply (rule conjI)
     apply (erule (2) cspace_cte_relation_upd_mdbI)
     apply (simp add: cmdbnode_relation_def)
 
     subgoal for _ s' by (cases "v_' s' = 0"; simp)

    apply (erule_tac t = s'a in ssubst)
    apply simp
    apply (rule conjI)
     apply (erule (1) setCTE_tcb_case) 
    subgoal by (simp add: carch_state_relation_def cmachine_state_relation_def
                     typ_heap_simps h_t_valid_clift_Some_iff)
   apply clarsimp
   done

lemma ccorres_updateMDB_set_mdbPrev [corres]:
  "src=src' \<Longrightarrow>
  ccorres dc xfdc ((\<lambda>_. src \<noteq> 0 \<and> (dest\<noteq>0 \<longrightarrow>is_aligned dest 3)) )
  ({s. mdb_node_ptr_' s = Ptr &((Ptr src' :: cte_C ptr)\<rightarrow>[''cteMDBNode_C''])} \<inter>
   {s. v_' s = dest}) []
  (updateMDB src (mdbPrev_update (\<lambda>_. dest)))
  (Call mdb_node_ptr_set_mdbPrev_'proc)"
  unfolding updateMDB_def
  apply (hypsubst)
  apply (rule ccorres_gen_asm [where G = \<top>, simplified])
  apply (simp only: Let_def)
  apply simp
  apply (rule ccorres_guard_imp2)
  apply (rule ccorres_pre_getCTE [where P = "\<lambda>cte s. ctes_of s src' = Some cte" and 
    P' = "\<lambda>_. (\<lbrace>\<acute>mdb_node_ptr = Ptr &((Ptr src' :: cte_C ptr)\<rightarrow>[''cteMDBNode_C''])\<rbrace> \<inter> \<lbrace>\<acute>v = dest\<rbrace>)"])
  apply (rule ccorres_from_spec_modifies_heap)
       apply (rule mdb_node_ptr_set_mdbPrev_spec)  
      apply (rule mdb_node_ptr_set_mdbPrev_modifies)
     apply simp
    apply clarsimp
    apply (rule rf_sr_cte_at_valid)
     apply simp
     apply (erule ctes_of_cte_at)
    apply assumption
   apply (clarsimp simp: cte_wp_at_ctes_of)
   apply (frule (1) rf_sr_ctes_of_clift)
   apply (clarsimp simp: typ_heap_simps)
   apply (rule fst_setCTE [OF ctes_of_cte_at], assumption)
   apply (erule bexI [rotated])
   apply (clarsimp simp add: rf_sr_def cstate_relation_def 
     Let_def cpspace_relation_def cte_wp_at_ctes_of heap_to_user_data_def
     cvariable_array_map_const_add_map_option[where f="tcb_no_ctes_proj"]
     typ_heap_simps')
   apply (rule conjI)   
    apply (erule (2) cspace_cte_relation_upd_mdbI)
    apply (simp add: cmdbnode_relation_def)   

    subgoal for _ s' by (cases "v_' s' = 0"; simp)
   apply (erule_tac t = s'a in ssubst)
   apply (simp add: carch_state_relation_def cmachine_state_relation_def
                    h_t_valid_clift_Some_iff typ_heap_simps')

   apply (erule (1) setCTE_tcb_case)
   apply clarsimp
   done

lemma ccorres_updateMDB_skip:
  "ccorres dc xfdc (\<top> and (\<lambda>_. n = 0)) UNIV hs (updateMDB n f) SKIP"
  unfolding updateMDB_def
  apply (rule ccorres_gen_asm)
  apply simp
  apply (rule ccorres_return)
  apply simp
  apply vcg
  done

definition
  "is_simple_cap_tag (tag :: word32) \<equiv>
      tag \<noteq> scast cap_null_cap \<and> tag \<noteq> scast cap_irq_control_cap
    \<and> tag \<noteq> scast cap_untyped_cap \<and> tag \<noteq> scast cap_reply_cap
    \<and> tag \<noteq> scast cap_endpoint_cap \<and> tag \<noteq> scast cap_notification_cap
    \<and> tag \<noteq> scast cap_thread_cap \<and> tag \<noteq> scast cap_cnode_cap
    \<and> tag \<noteq> scast cap_zombie_cap \<and> tag \<noteq> scast cap_small_frame_cap
    \<and> tag \<noteq> scast cap_frame_cap"

definition 
  "cteInsert_newCapIsRevocable_if newCap srcCap \<equiv> (if (cap_get_tag newCap = scast cap_endpoint_cap)
             then (if (capEPBadge_CL (cap_endpoint_cap_lift newCap) = capEPBadge_CL (cap_endpoint_cap_lift srcCap)) 
                     then 0 else 1)
             else if (cap_get_tag newCap = scast cap_notification_cap)
                  then (if (capNtfnBadge_CL (cap_notification_cap_lift newCap) = capNtfnBadge_CL (cap_notification_cap_lift srcCap)) 
                     then 0 else 1)
             else if (cap_get_tag newCap = scast cap_irq_handler_cap)
                  then (if cap_get_tag srcCap = scast cap_irq_control_cap then 1 else 0)
             else if (cap_get_tag newCap = scast cap_untyped_cap) then 1 else 0)"

lemma cteInsert_if_helper:
  assumes cgt: "rv = cap_get_tag newCap"
  and     rul: "\<And>s g. (s \<in> Q) = (s\<lparr> ret__unsigned_' := undefined,
  unsigned_eret_2_':= undefined \<rparr> \<in> Q')" 
  shows "\<Gamma> \<turnstile>\<^bsub>/UNIV\<^esub> {s. (cap_get_tag srcCap = cap_get_tag newCap 
                          \<or> is_simple_cap_tag (cap_get_tag newCap)) \<and>
            (s\<lparr>newCapIsRevocable_' := cteInsert_newCapIsRevocable_if newCap srcCap\<rparr> \<in> Q)}
          (IF rv = scast cap_endpoint_cap THEN
               \<acute>ret__unsigned :== CALL cap_endpoint_cap_get_capEPBadge(newCap);;
               \<acute>unsigned_eret_2 :== CALL cap_endpoint_cap_get_capEPBadge(srcCap);;
               \<acute>newCapIsRevocable :== (if \<acute>ret__unsigned \<noteq> \<acute>unsigned_eret_2 then 1 else 0)
             ELSE
               IF rv = scast cap_notification_cap THEN
                 \<acute>ret__unsigned :== CALL cap_notification_cap_get_capNtfnBadge(newCap);;
                 \<acute>unsigned_eret_2 :== CALL cap_notification_cap_get_capNtfnBadge(srcCap);;
                 \<acute>newCapIsRevocable :== (if \<acute>ret__unsigned \<noteq> \<acute>unsigned_eret_2 then 1 else 0)
               ELSE
                 IF rv = scast cap_irq_handler_cap THEN
                   \<acute>ret__unsigned :== CALL cap_get_capType(srcCap);;
                   \<acute>newCapIsRevocable :== (if \<acute>ret__unsigned = scast cap_irq_control_cap then 1 else 0)
                 ELSE
                   IF rv = scast cap_untyped_cap THEN
                     \<acute>newCapIsRevocable :== scast true
                   ELSE
                     IF True THEN
                        \<acute>newCapIsRevocable :== scast false
                     FI
                   FI
                 FI
               FI
             FI) Q"
  unfolding cteInsert_newCapIsRevocable_if_def
  apply (unfold cgt)
  apply (rule conseqPre)
  apply vcg
  apply (clarsimp simp: true_def false_def 
                        is_simple_cap_tag_def
                  cong: if_cong)
  apply (simp add: cap_tag_defs)
  apply (intro allI conjI impI)
  		      apply (clarsimp simp: rul)+
  done

lemma forget_Q':
  "(x \<in> Q) = (y \<in> Q) \<Longrightarrow> (x \<in> Q) = (y \<in> Q)" .

lemmas cteInsert_if_helper' = cteInsert_if_helper [OF _ forget_Q']

(* Useful:
  apply (tactic {* let val _ = reset CtacImpl.trace_ceqv; val _ = reset CtacImpl.trace_ctac in all_tac end; *})
  *)
declare word_neq_0_conv [simp del]

schematic_goal ccap_relation_tag_Master:
  "\<And>ccap. \<lbrakk> ccap_relation cap ccap \<rbrakk>
      \<Longrightarrow> cap_get_tag ccap = 
            case_capability ?a ?b ?c ?d ?e ?f ?g
               (case_arch_capability ?aa ?ab
                        (\<lambda>dev ptr rghts sz data. if sz = ARMSmallPage
                                then scast cap_small_frame_cap else scast cap_frame_cap)
                           ?ad ?ae) ?h ?i ?j ?k
            (capMasterCap cap)"
  by (fastforce simp: ccap_relation_def map_option_Some_eq2
                     Let_def cap_lift_def cap_to_H_def
              split: if_split_asm)

lemma ccap_relation_is_derived_tag_equal:
  "\<lbrakk> is_derived' cs p cap cap'; ccap_relation cap ccap; ccap_relation cap' ccap' \<rbrakk> 
  \<Longrightarrow> cap_get_tag ccap' = cap_get_tag ccap"
  unfolding badge_derived'_def is_derived'_def
  by (clarsimp simp: ccap_relation_tag_Master)

lemma ccap_relation_Master_tags_eq:
  "\<lbrakk> capMasterCap cap = capMasterCap cap'; ccap_relation cap ccap; ccap_relation cap' ccap' \<rbrakk> 
  \<Longrightarrow> cap_get_tag ccap' = cap_get_tag ccap"
  by (clarsimp simp: ccap_relation_tag_Master)

lemma is_simple_cap_get_tag_relation:
  "ccap_relation cap ccap
     \<Longrightarrow> is_simple_cap_tag (cap_get_tag ccap) = is_simple_cap' cap"
  apply (simp add: is_simple_cap_tag_def is_simple_cap'_def
                   cap_get_tag_isCap)
  apply (auto simp: isCap_simps)
  done

lemma setUntypedCapAsFull_cte_at_wp [wp]:
  "\<lbrace> cte_at' x \<rbrace> setUntypedCapAsFull rvb cap src \<lbrace> \<lambda>_. cte_at' x \<rbrace>"
  apply (clarsimp simp: setUntypedCapAsFull_def)
  apply wp
  done

lemma setUntypedCapAsFull_cte_at_wp' [wp]:
  "\<lbrace> cte_wp_at' (\<lambda>_. True) x \<rbrace> setUntypedCapAsFull rvb cap src \<lbrace> \<lambda>_. cte_wp_at' (\<lambda>_. True) x \<rbrace>"
  apply (clarsimp simp: setUntypedCapAsFull_def)
  apply wp
  done

lemma valid_cap_untyped_inv:
  "valid_cap' (UntypedCap d r n f) s \<Longrightarrow> n \<ge> 4 \<and> is_aligned (of_nat f :: word32) 4 \<and> n \<le> 30 \<and> n < word_bits"
  apply (clarsimp simp:valid_cap'_def capAligned_def)
  done

lemma and_and_mask_simple: "(y && mask n) = mask n \<Longrightarrow> ((x && y) && mask n) = x && mask n"
  by (simp add: word_bool_alg.conj.assoc)
  
lemma and_and_mask_simple_not: "(y && mask n) = 0 \<Longrightarrow> ((x && y) && mask n) = 0"
  by (simp add: word_bool_alg.conj.assoc)
  
lemma update_freeIndex:
  "ccorres dc xfdc
           (valid_objs' and cte_wp_at' (\<lambda>cte. \<exists>i. cteCap cte = UntypedCap d p sz i) srcSlot 
           and (\<lambda>_. is_aligned (of_nat i' :: word32) 4 \<and> i' \<le> 2 ^ sz))
           (UNIV \<inter> {s. cap_ptr_' s = Ptr &(cte_Ptr srcSlot\<rightarrow>[''cap_C''])} \<inter> {s.  v_' s = (of_nat (i') :: word32)>> 4})
           [] (updateCap srcSlot (UntypedCap d p sz i'))
           (Call cap_untyped_cap_ptr_set_capFreeIndex_'proc)"
  apply (rule ccorres_gen_asm)
  apply (rule ccorres_guard_imp)
     prefer 3
     apply assumption
    apply (rule_tac P = "sz \<le> 29" and G = "cte_wp_at' S srcSlot" for S in ccorres_gen_asm)
   prefer 2
   apply clarsimp
   apply (rule conjI, assumption)
   apply (clarsimp simp:cte_wp_at_ctes_of)
   apply (case_tac cte,clarsimp)
   apply (drule(1) ctes_of_valid_cap')
    apply (simp add:valid_cap'_def)
   apply clarify
proof -
  assume ialign:"is_aligned (of_nat i' :: word32) 4"
  assume szbound:"sz\<le> 29"
  assume ibound:"i'\<le> 2^sz"
  note ibound_concrete = order_trans[OF ibound power_increasing[OF szbound], simplified]
  have ibound_concrete_word:
    "(of_nat i' :: word32) \<le> 2 ^ 29"
    using ibound_concrete
    by (simp add: word_of_nat_le)
  have [simp]:"\<And>x. (x::word32) && 0xFFFFFFC0 = x && ~~ mask 6"
    by (simp add:mask_def)
  have [simp]:"\<And>x. ((x::word32) && ~~ mask 6) && mask 6 = 0"
    by (simp add:is_aligned_mask[THEN iffD1,OF is_aligned_neg_mask])
  have [simp]:"(0x3FFFFFF::word32) = mask 26"
    by (simp add:mask_def)
  have [simp]:"\<And>(n::word32) m. (n && mask 6 || m && ~~ mask 6 >> 6) && mask 26 = (m >> 6) && mask 26"
    apply (rule word_eqI)
    apply (simp add:nth_shiftr)
    apply (simp add:neg_mask_bang word_size)
    done    
  have terrible_word_stuff: "\<And>x1. to_bool
            ((cap_C.words_C x1.[Suc 0] >> 5) && 1) =
           to_bool
            ((cap_C.words_C x1.[Suc 0] && 0x3F ||
              (of_nat i' >> 4 << 6) && ~~ mask 6 >>
              5) &&
             1) \<and>
           cap_C.words_C x1.[Suc 0] && 0x1F =
           (cap_C.words_C x1.[Suc 0] && 0x3F ||
            (of_nat i' >> 4 << 6) && ~~ mask 6) &&
           0x1F \<and>
           i' =
           unat
            ((cap_C.words_C x1.[Suc 0] && 0x3F ||
              (of_nat i' >> 4 << 6) && ~~ mask 6 >>
              6) &&
             mask 26 <<
             4)"
    apply (rule conjI)
     apply (clarsimp simp: to_bool_and_1 nth_shiftr neg_mask_bang)
    apply (clarsimp simp: word_bool_alg.conj_disj_distrib2 mask_def[where n = 5,simplified,symmetric])
    apply (rule conjI)
     apply (subst and_and_mask_simple)
      apply (simp add: mask_def[where n=5, simplified])
     apply (subst and_and_mask_simple_not)
      apply (simp add: mask_def[where n=5, simplified] mask_def[where n=6, simplified])
     apply simp
    apply (rule inj_onD[OF word_unat.Abs_inj_on[where 'a=32]], simp)
      apply (cut_tac ialign ibound_concrete_word)
      apply (simp add: is_aligned_mask)
      apply word_bitwise
      apply (simp add: word_size)
     apply (cut_tac ibound_concrete)
     apply (simp add: unats_def)
    apply (simp add: word_unat.Rep[where 'a=32, simplified])
    done

  note option.case_cong_weak [cong]

show "ccorresG rf_sr \<Gamma> dc xfdc (cte_wp_at' (\<lambda>cte. \<exists>i. cteCap cte = capability.UntypedCap d p sz i) srcSlot)
        (UNIV \<inter> \<lbrace>\<acute>cap_ptr = cap_Ptr &(cte_Ptr srcSlot\<rightarrow>[''cap_C''])\<rbrace> \<inter> \<lbrace>\<acute>v = (of_nat i' :: word32) >> 4\<rbrace>) []
        (updateCap srcSlot (capability.UntypedCap d p sz i')) (Call cap_untyped_cap_ptr_set_capFreeIndex_'proc)"
  apply (cinit lift: cap_ptr_' v_')
   apply (rule ccorres_pre_getCTE)
   apply (rule_tac P = "\<lambda>s. ctes_of s srcSlot = Some rv \<and> (\<exists>i. cteCap rv = UntypedCap d p sz i)" in 
    ccorres_from_vcg[where P' = UNIV])
   apply (rule allI)
   apply (rule conseqPre)
   apply vcg
   apply (clarsimp simp:guard_simps)
   apply (intro conjI)
     apply (frule (1) rf_sr_ctes_of_clift)
     apply (clarsimp simp:typ_heap_simps)
   apply (frule (1) rf_sr_ctes_of_clift)
   apply (clarsimp simp:split_def)
   apply (simp add:hrs_htd_def typ_heap_simps)
   apply (rule fst_setCTE [OF ctes_of_cte_at], assumption)
   apply (erule bexI [rotated])
   apply (clarsimp simp: cte_wp_at_ctes_of)
   apply (frule (1) rf_sr_ctes_of_clift)
   apply (clarsimp simp add: rf_sr_def cstate_relation_def Let_def
     cvariable_array_map_const_add_map_option[where f="tcb_no_ctes_proj"])
   apply (simp add:cpspace_relation_def)
   apply (clarsimp simp:typ_heap_simps')
   apply (rule conjI)
    apply (erule(2) cpspace_cte_relation_upd_capI)
    apply (simp add:cte_lift_def)
    apply (simp split:option.splits )
    apply (simp add:cap_to_H_def Let_def split:cap_CL.splits if_split_asm)
    apply (case_tac y)
    apply (simp add:cap_lift_def Let_def split:if_split_asm)
    apply (case_tac cte',simp)
    apply (clarsimp simp:ccap_relation_def cap_lift_def
      cap_get_tag_def cap_to_H_def)
    subgoal by (rule terrible_word_stuff)
   apply (erule_tac t = s' in ssubst)
   apply clarsimp
   apply (rule conjI)
    apply (erule (1) setCTE_tcb_case)
   subgoal by (simp add: carch_state_relation_def cmachine_state_relation_def
                   typ_heap_simps')
  apply (clarsimp simp:cte_wp_at_ctes_of)
  done
qed

(* FIXME: move *)
lemma ccorres_cases:
  assumes P:    " P \<Longrightarrow> ccorres r xf G G' hs a b"
  assumes notP: "\<not>P \<Longrightarrow> ccorres r xf H H' hs a b"
  shows "ccorres r xf (\<lambda>s. (P \<longrightarrow> G s) \<and> (\<not>P \<longrightarrow> H s))
                      ({s. P \<longrightarrow> s \<in> G'} \<inter> {s. \<not>P \<longrightarrow> s \<in> H'})
                      hs a b"
  apply (cases P, auto simp: P notP)
  done

(* FIXME: move *)
lemma word_and_le': "\<lbrakk> b \<le> c \<rbrakk> \<Longrightarrow> (a :: word32) && b \<le> c"
  apply (metis word_and_le1 order_trans)
  done

(* FIXME: move *)
lemma word_and_less': "\<lbrakk> b < c \<rbrakk> \<Longrightarrow> (a :: word32) && b < c"
  apply (metis word_and_le1 xtr7)
  done

lemma capBlockSize_CL_maxSize:
  " \<lbrakk> cap_get_tag c = scast cap_untyped_cap \<rbrakk> \<Longrightarrow> capBlockSize_CL (cap_untyped_cap_lift c) < 0x20"
  apply (clarsimp simp: cap_untyped_cap_lift_def)
  apply (clarsimp simp: cap_lift_def)
  apply (clarsimp simp: cap_untyped_cap_def cap_null_cap_def)
  apply (rule word_and_less')
  apply simp
  done

lemma t2p_shiftr:
  "\<lbrakk>b\<le> a;a < word_bits \<rbrakk> \<Longrightarrow> (2::word32) ^ a >> b = 2 ^ (a - b)"
  apply (subst shiftr_w2p)
   apply (simp add:word_bits_def)
  apply (subst shiftr_w2p[where x = "a - b"])
   apply (simp add:word_bits_def)
  apply (simp only:word_bits_def[symmetric])
  apply (simp add:shiftr_shiftr)
  done

lemma setUntypedCapAsFull_ccorres [corres]:
  notes if_split [split del]
  notes Collect_const [simp del]
  notes Collect_True [simp] Collect_False [simp]
  shows
  "ccorres dc xfdc
      ((cte_wp_at' (\<lambda>c. (cteCap c) = srcCap) srcSlot) and valid_mdb' and pspace_aligned' and valid_objs'
          and (K (isUntypedCap newCap \<longrightarrow> (4 \<le> (capBlockSize newCap)))) 
          and (K (isUntypedCap srcCap \<longrightarrow> (4 \<le> capBlockSize srcCap))))
      (UNIV \<inter>  {s. ccap_relation srcCap (srcCap_' s)} \<inter> {s. ccap_relation newCap (newCap_' s)} \<inter> {s. srcSlot_' s = Ptr srcSlot})
      []
      (setUntypedCapAsFull srcCap newCap srcSlot)
      (Call setUntypedCapAsFull_'proc)"
  apply (cinit lift: srcCap_' newCap_' srcSlot_')
   apply (rule ccorres_if_lhs)
    apply (clarsimp simp: isCap_simps)
    apply csymbr
    apply csymbr
    apply (simp add: if_then_0_else_1 if_then_1_else_0 cap_get_tag_isCap_unfolded_H_cap)
    apply (rule ccorres_rhs_assoc)+
    apply csymbr
    apply csymbr
    apply (simp add: cap_get_tag_isCap_unfolded_H_cap ccorres_cond_univ_iff)
    apply (rule ccorres_rhs_assoc)+
    apply csymbr
    apply csymbr
    apply csymbr
    apply (frule cap_get_tag_to_H(9))
     apply (simp add: cap_get_tag_isCap_unfolded_H_cap)
    apply (rotate_tac 1)
    apply (frule cap_get_tag_to_H(9))
     apply (simp add: cap_get_tag_isCap_unfolded_H_cap)
    apply simp
    apply (rule ccorres_rhs_assoc)+
    apply csymbr
    apply csymbr
    apply csymbr
    apply (simp add: ccorres_cond_univ_iff)
    apply csymbr+
    apply (rule ccorres_move_c_guard_cte)
    apply (rule ccorres_Guard)
    apply (rule ccorres_call)
       apply (rule update_freeIndex [unfolded dc_def])
      apply simp
     apply simp
    apply simp
   apply clarsimp
   apply (csymbr)
   apply (csymbr)
   apply (simp add: cap_get_tag_isCap)
   apply (rule ccorres_Cond_rhs_Seq)
    apply (rule ccorres_rhs_assoc)+
    apply csymbr
    apply csymbr
    apply (simp add: cap_get_tag_isCap)
    apply (rule ccorres_Cond_rhs)
     apply (rule ccorres_rhs_assoc)+
     apply csymbr
     apply csymbr
     apply csymbr
     apply (rule ccorres_cases [where P="capPtr srcCap = capPtr newCap"])
      apply (clarsimp simp: cap_get_tag_isCap[symmetric] cap_get_tag_UntypedCap split: if_split_asm)
      apply (rule ccorres_rhs_assoc)+
      apply csymbr
      apply csymbr
      apply csymbr
      apply (clarsimp simp: cap_get_tag_to_H cap_get_tag_UntypedCap split: if_split_asm)
      apply (rule ccorres_cond_false)
      apply (rule ccorres_return_Skip [unfolded dc_def])
     apply (clarsimp simp: cap_get_tag_isCap[symmetric] cap_get_tag_UntypedCap split: if_split_asm)
     apply (rule ccorres_cond_false)
     apply (rule ccorres_return_Skip [unfolded dc_def])
    apply (rule ccorres_return_Skip [unfolded dc_def])
   apply clarsimp
   apply (rule ccorres_cond_false)
   apply (rule ccorres_return_Skip [unfolded dc_def])
  apply (clarsimp simp: cap_get_tag_isCap[symmetric] cap_get_tag_UntypedCap)
  apply (frule(1) cte_wp_at_valid_objs_valid_cap')
  apply clarsimp
  apply (intro conjI impI allI)
              apply (erule cte_wp_at_weakenE')
              apply (clarsimp simp: cap_get_tag_isCap[symmetric] cap_get_tag_UntypedCap split: if_split_asm)
             apply clarsimp
             apply (drule valid_cap_untyped_inv,clarsimp simp:max_free_index_def)
             apply (rule is_aligned_weaken)
              apply (rule is_aligned_shiftl_self[unfolded shiftl_t2n,where p = 1,simplified])
             apply assumption
            apply (clarsimp simp: max_free_index_def shiftL_nat valid_cap'_def capAligned_def)
            apply (simp add:power_minus_is_div unat_power_lower unat_sub word_le_nat_alt t2p_shiftr)
           apply clarsimp
          apply (erule cte_wp_at_weakenE', simp)
         apply clarsimp
         apply (drule valid_cap_untyped_inv)
         apply (clarsimp simp:max_free_index_def t2p_shiftr unat_sub word_le_nat_alt)
        apply (clarsimp simp:field_simps)
        apply (rule word_less_imp_diff_less)
        apply (subst (asm) eq_commute, fastforce simp: unat_sub word_le_nat_alt)
        apply (rule capBlockSize_CL_maxSize)
        apply (clarsimp simp: cap_get_tag_UntypedCap)
       apply (clarsimp simp: cap_get_tag_isCap_unfolded_H_cap)
      apply (clarsimp split: if_split_asm)
     apply (clarsimp split: if_split_asm)
    apply (clarsimp split: if_split_asm)
   apply (clarsimp split: if_split_asm)
  apply (clarsimp split: if_split_asm)
  done

lemma ccte_lift:
  "\<lbrakk>(s, s') \<in> rf_sr; cslift s' (cte_Ptr p) = Some cte';
    cte_lift cte' = Some y; c_valid_cte cte'\<rbrakk>
   \<Longrightarrow> ctes_of s p = Some (cte_to_H (the (cte_lift cte')))"
  apply (clarsimp simp:rf_sr_def cstate_relation_def Let_def cpspace_relation_def)
  apply (drule(1) cmap_relation_cs_atD)
   apply simp
  apply (clarsimp simp:ccte_relation_def)
  done

lemma cmdb_node_relation_mdbNext:
  "cmdbnode_relation n n'
         \<Longrightarrow> mdbNext_CL (mdb_node_lift n') = mdbNext n"
 by (simp add:cmdbnode_relation_def)

lemma cslift_ptr_safe:
  "cslift x ptr = Some a
  \<Longrightarrow> ptr_safe ptr (hrs_htd (t_hrs_' (globals x)))"
  apply (rule_tac h = "fst (t_hrs_' (globals x))"
        in lift_t_ptr_safe[where g = c_guard])
  apply (fastforce simp add:typ_heap_simps hrs_htd_def)
  done

thm ccorres_move_c_guard_cte

lemma ccorres_move_ptr_safe:
  "ccorres_underlying rf_sr \<Gamma> r xf arrel axf A C' hs a c \<Longrightarrow>
  ccorres_underlying rf_sr \<Gamma> r xf arrel axf 
  (A and K (dest = cte_Ptr (ptr_val dest)) and cte_wp_at' (\<lambda>_. True) (ptr_val dest)) 
  (C' \<inter> \<lbrace>True\<rbrace>) hs a (Guard MemorySafety \<lbrace>ptr_safe (dest) (hrs_htd \<acute>t_hrs) \<rbrace> c)"
  apply (rule ccorres_guard_imp2)
  apply (rule ccorres_Guard)
   apply simp
  apply (clarsimp simp:cte_wp_at_ctes_of)
  apply (drule(1) rf_sr_ctes_of_clift)
  apply (case_tac dest)
  apply (clarsimp simp:ptr_coerce_def)
  apply (erule cslift_ptr_safe)
  done

lemma ccorres_move_ptr_safe_Seq:
  "ccorres_underlying rf_sr \<Gamma> r xf arrel axf A C' hs a (c;;d) \<Longrightarrow>
  ccorres_underlying rf_sr \<Gamma> r xf arrel axf 
  (A and cte_wp_at' (\<lambda>_. True) (ptr_val dest) and K (dest = cte_Ptr (ptr_val dest)))
  (C' \<inter> \<lbrace>True\<rbrace>) hs a
  (Guard MemorySafety \<lbrace>ptr_safe (dest) (hrs_htd \<acute>t_hrs) \<rbrace> c;;d)"
  apply (rule ccorres_guard_imp2)
  apply (rule ccorres_Guard_Seq)
   apply simp
  apply (clarsimp simp:cte_wp_at_ctes_of)
  apply (drule(1) rf_sr_ctes_of_clift)
  apply clarsimp
  apply (erule cslift_ptr_safe)
  done

lemmas ccorres_move_guard_ptr_safe = ccorres_move_ptr_safe_Seq ccorres_move_ptr_safe

lemma scast_1_32 [simp]: "scast (1 :: 32 signed word) = (1 :: 32 word)"
  by simp

lemma cteInsert_ccorres:
  "ccorres dc xfdc (cte_wp_at' (\<lambda>scte. capMasterCap (cteCap scte) = capMasterCap cap
                                        \<or> is_simple_cap' cap) src
                     and valid_mdb' and valid_objs'
                     and pspace_aligned' and (valid_cap' cap)
                     and (\<lambda>s. cte_wp_at' (\<lambda>c. True) src s))
             (UNIV
                \<inter> {s. destSlot_' s = Ptr dest} \<inter> {s. srcSlot_' s = Ptr src} \<inter> {s. ccap_relation cap (newCap_' s)}
                \<inter> {s. destSlot_' s = Ptr dest} \<inter> {s. srcSlot_' s = Ptr src} \<inter> {s. ccap_relation cap (newCap_' s)}) []
             (cteInsert cap src dest)
             (Call cteInsert_'proc)"
thm cteInsert_body_def
  apply (cinit (no_ignore_call) lift: destSlot_' srcSlot_' newCap_' 
    simp del: return_bind simp add: Collect_const)
   apply (rule ccorres_move_c_guard_cte)
   apply (ctac pre: ccorres_pre_getCTE)
     apply (rule ccorres_move_c_guard_cte)
     apply (ctac pre: ccorres_pre_getCTE)
       apply csymbr
       apply (fold revokable'_fold)
       apply (simp (no_asm) only: if_distrib [where f="scast"] scast_1_32 scast_0)
       apply (ctac add: revokable_ccorres)
         apply (ctac (c_lines 3) add: cteInsert_ccorres_mdb_helper)
           apply (simp del: Collect_const)
           apply (rule ccorres_pre_getCTE ccorres_assert)+
           apply (ctac add: setUntypedCapAsFull_ccorres)
             apply (rule ccorres_move_c_guard_cte)
             apply (ctac)
               apply (rule ccorres_move_c_guard_cte)
               apply ctac
                 apply (rule ccorres_move_c_guard_cte)
                 apply (ctac(no_vcg))
                  apply csymbr
                  apply (erule_tac t = ret__unsigned in ssubst)
                  apply (rule ccorres_cond_both [where R = \<top>, simplified])
                    apply (erule mdbNext_not_zero_eq)
                   apply csymbr
                   apply simp
                   apply (rule ccorres_move_c_guard_cte)
                   apply (simp add:dc_def[symmetric])
                   apply (ctac ccorres:ccorres_updateMDB_set_mdbPrev)
                  apply (simp add:dc_def[symmetric])
                  apply (ctac ccorres: ccorres_updateMDB_skip)
                 apply (wp static_imp_wp)+
               apply (clarsimp simp: Collect_const_mem dc_def split del: if_split)
               apply vcg
              apply (wp static_imp_wp)
             apply (clarsimp simp: Collect_const_mem dc_def split del: if_split)
             apply vcg
            apply (clarsimp simp:cmdb_node_relation_mdbNext)
            apply (wp setUntypedCapAsFull_cte_at_wp static_imp_wp)
           apply (clarsimp simp: Collect_const_mem dc_def split del: if_split)
           apply (vcg exspec=setUntypedCapAsFull_modifies)
          apply wp
         apply vcg
        apply wp
       apply (rule cteInsert_if_helper')
        apply simp
       apply simp
      apply wp
     apply vcg
    apply wp
   apply vcg
  apply (simp add: Collect_const_mem split del: if_split) -- "Takes a while"
  apply (rule conjI)
   apply (clarsimp simp: conj_comms cte_wp_at_ctes_of)
   apply (intro conjI)
      apply clarsimp
     apply simp
    apply simp
   apply clarsimp
   apply (rule conjI)
    apply (clarsimp simp: isUntypedCap_def split: capability.split_asm)
    apply (frule valid_cap_untyped_inv)
    apply clarsimp
   apply (rule conjI)
    apply (case_tac ctea)
    apply (clarsimp simp: isUntypedCap_def split: capability.splits)
    apply (frule valid_cap_untyped_inv[OF ctes_of_valid_cap'])
     apply fastforce
    apply clarsimp+
   apply (drule valid_dlist_nextD)
     apply (simp add:valid_mdb'_def valid_mdb_ctes_def)
    apply simp
   apply clarsimp
  apply (clarsimp simp: map_comp_Some_iff cte_wp_at_ctes_of
             split del: if_split)
  apply (clarsimp simp: typ_heap_simps c_guard_clift split_def)
  apply (clarsimp simp: is_simple_cap_get_tag_relation ccte_relation_ccap_relation cmdb_node_relation_mdbNext[symmetric])
  apply (metis (hide_lams, no_types) ccap_relation_Master_tags_eq ccte_relation_ccap_relation rf_sr_cte_relation)
  done

(****************************************************************************)
(*                                                                          *)
(* Lemmas dealing with updateMDB on Haskell side and IF-THEN-ELSE on C side *)
(*                                                                          *)
(****************************************************************************)

lemma updateMDB_mdbNext_set_mdbPrev:
 "\<lbrakk> slotc = Ptr slota; cmdbnode_relation mdba mdbc\<rbrakk> \<Longrightarrow> 
  ccorres dc xfdc 
     ( \<lambda>s. is_aligned (mdbNext mdba) 3 \<and> (slota\<noteq>0\<longrightarrow>is_aligned slota 3))
     UNIV hs 
      (updateMDB (mdbNext mdba) (mdbPrev_update (\<lambda>_. slota)))

      (IF mdbNext_CL (mdb_node_lift mdbc) \<noteq> 0 
       THEN
          Guard C_Guard \<lbrace>hrs_htd \<acute>t_hrs \<Turnstile>\<^sub>t (Ptr (mdbNext_CL (mdb_node_lift mdbc)) :: cte_C ptr)\<rbrace>
               (call (\<lambda>ta. ta(| mdb_node_ptr_' := Ptr &(Ptr (mdbNext_CL (mdb_node_lift mdbc)):: cte_C ptr
                                                          \<rightarrow>[''cteMDBNode_C'']),
                                 v_' := ptr_val slotc |))
                mdb_node_ptr_set_mdbPrev_'proc (\<lambda>s t. s\<lparr> globals := globals t \<rparr>) (\<lambda>ta s'. Basic (\<lambda>a. a)))
      FI)"
  apply (rule ccorres_guard_imp2) -- "replace preconditions by schematics"
  -- "Main Goal"
   apply (rule ccorres_cond_both [where R="\<lambda>_.True", simplified])  -- "generates 3 subgoals (one for 'then', one for 'else')"
   -- "***instanciate the condition***" 
     apply (rule mdbNext_not_zero_eq)
     apply assumption
   -- "***cond True: ptr \<noteq> 0***"
    apply (rule ccorres_updateMDB_cte_at)
    apply (ctac add: ccorres_updateMDB_set_mdbPrev)
   apply (ctac ccorres: ccorres_updateMDB_skip) 
  -- " instanciate generalized preconditions"
  apply (case_tac "mdbNext_CL (mdb_node_lift mdbc)=0")  

  -- "Next is zero"
  apply (clarsimp simp: cmdbnode_relation_def) 

  -- "Next is not zero"
  apply (clarsimp simp: cmdbnode_relation_def cte_wp_at_ctes_of) 
done

lemma updateMDB_mdbPrev_set_mdbNext:
 "\<lbrakk> slotc = Ptr slota; cmdbnode_relation mdba mdbc\<rbrakk> \<Longrightarrow> 
  ccorres dc xfdc 
     ( \<lambda>s. (is_aligned (mdbPrev mdba) 3 \<and> (slota\<noteq>0\<longrightarrow>is_aligned slota 3)))
      UNIV
     hs
     (updateMDB (mdbPrev mdba) (mdbNext_update (\<lambda>_. slota)))

     (IF mdbPrev_CL (mdb_node_lift mdbc) \<noteq> 0 
      THEN
          Guard C_Guard \<lbrace>hrs_htd \<acute>t_hrs \<Turnstile>\<^sub>t (Ptr (mdbPrev_CL (mdb_node_lift mdbc)):: cte_C ptr)\<rbrace>
               (call (\<lambda>ta. ta(| mdb_node_ptr_' := Ptr &(Ptr (mdbPrev_CL (mdb_node_lift mdbc)):: cte_C ptr
                                                           \<rightarrow>[''cteMDBNode_C'']),
                                 v_' := ptr_val slotc |))
                mdb_node_ptr_set_mdbNext_'proc (\<lambda>s t. s\<lparr> globals := globals t \<rparr>) (\<lambda>ta s'. Basic (\<lambda>a. a)))
      FI)"
  apply (rule ccorres_guard_imp2) -- "replace preconditions by schematics"
  -- "Main Goal"
   apply (rule ccorres_cond_both[where R="\<lambda>_.True", simplified])  -- "generates 3 subgoals (one for 'then', one for 'else')"
   -- "***instanciate the condition***"
     apply (rule mdbPrev_not_zero_eq) 
     apply assumption
   -- "***cond True: ptr \<noteq> 0***"
     apply (rule ccorres_updateMDB_cte_at)
    apply (ctac add: ccorres_updateMDB_set_mdbNext)
                   -- "-- ccorres_call generates 4 subgoals, the 3 last being solved by simp "
   -- "***cond False: ptr = 0***"
   apply (ctac ccorres: ccorres_updateMDB_skip) 

  -- " instanciate generalized preconditions"
  apply (case_tac "mdbPrev_CL (mdb_node_lift mdbc)=0")  

  -- "Next is zero"
  apply (clarsimp simp: cmdbnode_relation_def) 

  -- "Next is not zero"
  apply (clarsimp simp: cte_wp_at_ctes_of cmdbnode_relation_def)
done








(************************************************************************)
(*                                                                      *)
(* cteMove_ccorres ******************************************************)
(*                                                                      *)
(************************************************************************)

lemma is_aligned_3_prev:
  "\<lbrakk> valid_mdb' s; pspace_aligned' s; ctes_of s p = Some cte \<rbrakk>
  \<Longrightarrow> is_aligned (mdbPrev (cteMDBNode cte)) 3"
  apply (cases "mdbPrev (cteMDBNode cte) = 0", simp)
  apply (drule (2) valid_mdb_ctes_of_prev)
  apply (clarsimp simp: cte_wp_at_ctes_of)
  done

lemma is_aligned_3_next:
  "\<lbrakk> valid_mdb' s; pspace_aligned' s; ctes_of s p = Some cte \<rbrakk>
  \<Longrightarrow> is_aligned (mdbNext (cteMDBNode cte)) 3"
  apply (cases "mdbNext (cteMDBNode cte) = 0", simp)
  apply (drule (2) valid_mdb_ctes_of_next)
  apply (clarsimp simp: cte_wp_at_ctes_of)
  done

lemma cteMove_ccorres:
  "ccorres dc xfdc 
       (valid_mdb' and pspace_aligned' ) 
       (UNIV \<inter> {s. destSlot_' s = Ptr dest} \<inter> 
               {s. srcSlot_' s = Ptr src} \<inter>
               {s. ccap_relation cap (newCap_' s)}) [] 
       (cteMove cap src dest) 
       (Call cteMove_'proc)"
  apply (cinit (no_ignore_call) lift: destSlot_' srcSlot_' newCap_' simp del: return_bind)
   apply (ctac pre: ccorres_pre_getCTE ccorres_assert iffD2 [OF ccorres_seq_skip])
          apply (ctac+, csymbr+)+
                 apply (erule_tac t = prev_ptr in ssubst)
                 apply (ctac add: updateMDB_mdbPrev_set_mdbNext)
                   apply csymbr
                   apply (erule_tac t = next_ptr in ssubst)
                   apply (rule updateMDB_mdbNext_set_mdbPrev)
            apply simp+
                  apply (wp, vcg)+
  apply (rule conjI)
   apply (clarsimp simp: cte_wp_at_ctes_of)
   apply (intro conjI, simp+)
   apply (erule (2) is_aligned_3_prev)
   apply (erule (2) is_aligned_3_next)
  apply (clarsimp simp: dc_def split del: if_split)
  apply (simp add: ccap_relation_NullCap_iff)
  apply (clarsimp simp add: cmdbnode_relation_def
    mdb_node_to_H_def nullMDBNode_def 
    false_def to_bool_def)
  done

lemma cteMove_ccorres_verbose:
  "ccorres dc xfdc 
       (valid_mdb' and pspace_aligned' ) 
       (UNIV \<inter> {s. destSlot_' s = Ptr dest} \<inter> 
               {s. srcSlot_' s = Ptr src} \<inter>
               {s. ccap_relation cap (newCap_' s)}) [] 
       (cteMove cap src dest) 
       (Call cteMove_'proc)"

  apply (cinit (no_ignore_call) lift: destSlot_' srcSlot_' newCap_' simp del: return_bind)
(* previous line replaces all the following:  
  unfolding cteMove_def           -- "unfolds Haskell side"
  apply (rule ccorres_Call)       -- "unfolds C side" 
   apply (rule cteMove_impl [unfolded cteMove_body_def]) 
                                  -- "retrieves the C body definition"
  apply (rule ccorres_rhs_assoc)+ -- "re-associates C sequences to the right: i0;(the rest)"
  apply (simp del: return_bind Int_UNIV_left)
                                  -- "gets rid of SKIP and print all haskells instruction as y \<leftarrow> \<dots>"
  apply (cinitlift destSlot_' srcSlot_' newCap_') 
  apply (rule ccorres_guard_imp2) -- "replaces the preconditions by schematics (to be instanciated along the proof)"
                                  -- " \<Rightarrow> creates 2 subgoals (1 for main proof and 1 for ''conjunction of "
                                  -- "    preconditions implies conjunction of generalized (schematics) guards'')"
    
  -- "Start proofs"

  apply csymbr -- "Remove undefined"
  apply csymbr
  apply csymbr  
*)    
  -- "***Main goal***"
  -- "--- instruction: oldCTE \<leftarrow> getCTE dest; ---"
  -- "---              y \<leftarrow> assert (cteCap oldCTE = capability.NullCap); ---"  
  -- "---              y \<leftarrow> assert (mdbPrev (cteMDBNode oldCTE) = nullPointer \<and> mdbNext (...)); ---"
   apply (ctac pre: ccorres_pre_getCTE ccorres_assert iffD2 [OF ccorres_seq_skip])

                                  -- "ccorres_Guard_Seq puts the C guards into the precondition" 
                                  -- "ccorres_getCTE applies the corres proof for getCTE"
                                  -- "ccorres_assert add the asserted proposition to the precondition"
                                  -- "iffD2 [\<dots>] removes the SKIPS"

                                     -- "implicit symbolic execution of return"
                                     -- "\<Rightarrow> 2 new subgoals for return (in addition to Main Goal)"
                                     -- "      1. pre/post for Haskell side of return"
                                     -- "      2. pre/post for C side of return"

                                     -- " (rq: ccorress_getCTE eta expands everything... )"
        -- "***Main Goal of return***"
        -- "--- instruction: y \<leftarrow> updateCap dest cap ---"
          apply ctac
	                             -- "implicit symbolic execution \<Rightarrow> 2 new subgoals for 1st updateCap"

          -- "***Main Goal***" 
	  -- "--- instruction: y \<leftarrow> updateCap src capability.NullCap; (but with CALL on C side)"
            apply csymbr           -- "symb exec of C instruction CALL to create Null Cap"
            -- "--- instruction: y \<leftarrow> updateCap src capability.NullCap; (no CALL on C side)" 
            apply ctac
                                   -- "implicit symbolic execution \<Rightarrow> 2 new subgoals for 2st updateCap"
            -- "***Main Goal***"
            -- "--- instruction: y \<leftarrow> updateMDB dest (const rv); ---"
                                   -- "if not ctac won't work, because of the eta-expansion\<dots>"
             apply ctac
                                   -- "implicit symbolic execution \<Rightarrow> 2 new subgoals for 1st updateMDB"
             -- "***Main Goal***" 
             -- "--- instruction: y \<leftarrow> updateMDB dest (const nullMDBNode); (but with CALL on C side) ---" 
               apply csymbr       -- "symb exec of C instruction CALL to create Null MDB"
               -- "--- instruction: y \<leftarrow> updateMDB dest (const nullMDBNode); (no CALL on C side) ---"
               apply ctac
                                  -- "implicit symbolic execution \<Rightarrow> 2 new subgoals for 2nd updateMDB"
               -- "***Main Goal***"
               -- "--- instruction: y <- updateMDB (mdbPrev rv) (mdbNext_update (%_. dest); (but with CALL on C side) ---"
                 apply csymbr    -- "symb exec of C instruction CALL to mdbPrev"
                 -- "--- instruction: y <- updateMDB (mdbPrev rv) (mdbNext_update (%_. dest); (no CALL on C side) ---"
                 -- "--- (IF instruction in the C side) ---" 
                 apply (erule_tac t = prev_ptr in ssubst)
                 apply (ctac add: updateMDB_mdbPrev_set_mdbNext) 

                 -- "***the correspondance proof for the rest***"
                 -- "--- instruction: updateMDB (mdbNext rv) (mdbPrev_update (%_. dest)) (but with CALL on C side) ---"
                   apply csymbr -- "symb exec of C instruction CALL to mdbNext"
                   -- "--- instruction: updateMDB (mdbNext rv) (mdbPrev_update (%_. dest)) (no CALL on C side) ---"
                   -- "--- (IF instruction in the C side) ---"

                   apply (erule_tac t = next_ptr in ssubst) 
                   apply (rule updateMDB_mdbNext_set_mdbPrev) 
		    apply simp
		   apply simp
		   

                 -- "***the pre/post for Haskell side"
                  apply wp
                 -- "***the pre/post for C side"
                 apply vcg
               -- "***pre/post for Haskell side of 2nd updateMDB***"
                apply wp
               -- "***pre/post for C side of 2nd updateMDB***"
               apply vcg
             -- "***pre/post for Haskell side of 1st updateMDB***" 
              apply wp
             -- "***pre/post for C side of 1st updateMDB***" 
             apply vcg
            -- "***pre/post for Haskell side of 2st updateCap***"
            apply wp
            -- "***pre/post for C side of 2st updateCap***"
            apply vcg
          -- "***pre/post for Haskell side of 1st updateCap***"
           apply wp
          -- "***pre/post for C side of 1st updateCap***"
          apply vcg 
        -- "***pre/post for Haskell side of return***"
         apply wp                   
        -- "***pre/post for C side of return***" 
        apply vcg

  -- "********************"
  -- "*** LAST SUBGOAL ***"
  -- "********************"
  -- "***conjunction of generalised precondition ***" 
  apply (rule conjI)
  
  -- "***--------------------------------***"
  -- "***Haskell generalised precondition***"
  -- "***--------------------------------***"
  -- " (complicated conjunction with many cte_at' and src\<noteq>0 \<dots>)"
   apply (clarsimp simp: cte_wp_at_ctes_of)
                                     -- "cte_wp_at_ctes_of replaces (cte_at' p s) in the goal by "
                                     -- "(\<exists>cte.ctes_of s p = Some cte) which is in the hypotheses "
   -- " ctes_of s (?ptr908 ...) = Some scte \<and> ..."
   apply (rule conjI, assumption)   -- "instanciates the schematic with src"
   -- "  (mdbPrev \<dots> \<noteq> 0 \<longrightarrow> (\<exists>cte. ctes_of s (mdbPrev \<dots>) = Some cte) \<and> is_aligned (mdbPrev \<dots>) 3)"
   -- "\<and> (mdbNext \<dots> \<noteq> 0 \<longrightarrow> (\<exists>cte. ctes_of s (mdbNext \<dots>) = Some cte) \<and> is_aligned (mdbNext \<dots>) 3)"
   apply (rule conjI)
   apply (erule (2) is_aligned_3_prev)
   apply (erule (2) is_aligned_3_next)
   
  -- "***--------------------------***"
  -- "***C generalised precondition***"
  -- "***--------------------------***"
  apply (unfold dc_def)
  apply (clarsimp simp: ccap_relation_NullCap_iff split del: if_split)
  -- "cmdbnode_relation nullMDBNode va"
  apply (simp add: cmdbnode_relation_def) 
  apply (simp add: mdb_node_to_H_def) 
  apply (simp add: nullMDBNode_def) 
  apply (simp add: false_def to_bool_def)
  done

(************************************************************************)
(*                                                                      *)
(* lemmas used in cteSwap_ccorres ***************************************)
(*                                                                      *)
(************************************************************************)



(*---------------------------------------------------------------------------------------*)
(* corres lemma for return of mdbnode but 'safer' than ccorres_return_cte_mdbnode ------ *)
(*---------------------------------------------------------------------------------------*)

lemma ccorres_return_cte_mdbnode_safer:
  fixes ptr' :: "cstate \<Rightarrow> cte_C ptr"
  assumes r1: "\<And>s s' g. (s, s') \<in> rf_sr \<Longrightarrow> (s, xfu g s') \<in> rf_sr"
  and xf_xfu: "\<And>s g. xf (xfu g s) = g s"
  shows "ccorres cmdbnode_relation xf 
         (\<lambda>s. \<exists> cte'. ctes_of s ptr = Some cte' \<and> cteMDBNode cte = cteMDBNode cte') {s. ptr_val (ptr' s) = ptr}  hs 
         (return (cteMDBNode cte))
         (Basic (\<lambda>s. xfu (\<lambda>_. h_val  (hrs_mem (t_hrs_' (globals s))) 
           (Ptr &(ptr' s \<rightarrow>[''cteMDBNode_C'']))) s))"
  apply (rule ccorres_from_vcg)
  apply (rule allI, rule conseqPre, vcg)
  apply (clarsimp simp add: return_def)
  apply rule
  apply (erule r1)
  apply (simp add: xf_xfu)
  apply (drule (1) rf_sr_ctes_of_clift)
  apply (clarsimp simp: typ_heap_simps)
  done






(*-----------------------------------------------------------------------*)
(* lemmas about map and hrs_mem -----------------------------------------*)
(*-----------------------------------------------------------------------*)

declare modify_map_exists_cte[simp]







(*------------------------------------------------------------------------------*)
(* lemmas about pointer equality given valid_mdb (prev\<noteq>next, prev\<noteq>myself, etc) *)
(*------------------------------------------------------------------------------*)

lemma valid_mdb_Prev_neq_Next: 
    "\<lbrakk> valid_mdb' s; ctes_of s p = Some cte; mdbPrev (cteMDBNode cte) \<noteq> 0  \<rbrakk> \<Longrightarrow> 
     (mdbNext (cteMDBNode cte)) \<noteq> (mdbPrev (cteMDBNode cte))"
  apply (simp add: valid_mdb'_def)
  apply (simp add: valid_mdb_ctes_def) 
  apply (elim conjE)
  apply (drule (1) mdb_chain_0_no_loops)
  apply (simp add: valid_dlist_def)
  apply (erule_tac x=p in allE)
  apply (erule_tac x=cte in allE)
  apply (simp add: Let_def)  
  apply clarsimp 
  apply (drule_tac s="mdbNext (cteMDBNode cte)" in sym)
  apply simp  
  apply (simp add: no_loops_def) 
  apply (erule_tac x= "(mdbNext (cteMDBNode cte))" in allE) 
  apply (erule notE, rule trancl_trans)
    apply (rule r_into_trancl)
    apply (simp add: mdb_next_unfold)
  apply (rule r_into_trancl)
  apply (simp add: mdb_next_unfold)
done

lemma valid_mdb_Prev_neq_itself: 
    "\<lbrakk> valid_mdb' s; ctes_of s p = Some cte  \<rbrakk> \<Longrightarrow> 
     (mdbPrev (cteMDBNode cte)) \<noteq>  p"
  apply (unfold valid_mdb'_def)
  apply (simp add: CSpace_I.no_self_loop_prev)
done

lemma valid_mdb_Next_neq_itself: 
    "\<lbrakk> valid_mdb' s; ctes_of s p = Some cte  \<rbrakk> \<Longrightarrow> 
     (mdbNext (cteMDBNode cte)) \<noteq>  p"
  apply (unfold valid_mdb'_def)
  apply (simp add: CSpace_I.no_self_loop_next)
done

lemma valid_mdb_not_same_Next :
    "\<lbrakk> valid_mdb' s; p\<noteq>p'; ctes_of s p = Some cte; ctes_of s p' = Some cte'; 
       (mdbNext (cteMDBNode cte))\<noteq>0 \<or> (mdbNext (cteMDBNode cte'))\<noteq>0 \<rbrakk> \<Longrightarrow> 
     (mdbNext (cteMDBNode cte)) \<noteq>  (mdbNext (cteMDBNode cte'))  "
  apply (clarsimp)
  apply (case_tac cte, clarsimp)
  apply (rename_tac capability mdbnode)
  apply (case_tac cte', clarsimp)
  apply (subgoal_tac "mdb_ptr (ctes_of s) p capability mdbnode")
   apply (drule (2) mdb_ptr.p_nextD)
   apply clarsimp
  apply (unfold mdb_ptr_def vmdb_def mdb_ptr_axioms_def valid_mdb'_def, simp)
  done

lemma valid_mdb_not_same_Prev :
    "\<lbrakk> valid_mdb' s; p\<noteq>p'; ctes_of s p = Some cte; ctes_of s p' = Some cte';
       (mdbPrev (cteMDBNode cte))\<noteq>0 \<or> (mdbPrev (cteMDBNode cte'))\<noteq>0 \<rbrakk> \<Longrightarrow> 
     (mdbPrev (cteMDBNode cte)) \<noteq>  (mdbPrev (cteMDBNode cte'))  "
  apply (clarsimp)
  apply (case_tac cte, clarsimp)
  apply (rename_tac capability mdbnode)
  apply (case_tac cte', clarsimp)
  apply (subgoal_tac "mdb_ptr (ctes_of s) p capability mdbnode")
   apply (drule (2) mdb_ptr.p_prevD)
   apply clarsimp
  apply (unfold mdb_ptr_def vmdb_def mdb_ptr_axioms_def valid_mdb'_def, simp)
  done




(*---------------------------------------------------------------------------------*)
(* lemmas to simplify the big last goal on C side to avoid proving things twice ---*)
(*---------------------------------------------------------------------------------*)

lemma c_guard_and_h_t_valid_eq_h_t_valid:
     "(POINTER \<noteq> 0 \<longrightarrow>
         c_guard ((Ptr &(Ptr POINTER ::cte_C ptr \<rightarrow>[''cteMDBNode_C''])) ::mdb_node_C ptr)  \<and>
         s' \<Turnstile>\<^sub>c (Ptr (POINTER)::cte_C ptr)) =
      (POINTER \<noteq> 0 \<longrightarrow>
         s' \<Turnstile>\<^sub>c (Ptr (POINTER)::cte_C ptr))" 
  apply (rule iffI, clarsimp+)
  apply (rule c_guard_field_lvalue)
  apply (rule c_guard_h_t_valid, assumption) 
  apply (fastforce simp: typ_uinfo_t_def)+
done


lemma c_guard_and_h_t_valid_and_rest_eq_h_t_valid_and_rest:
     "(POINTER \<noteq> 0 \<longrightarrow>
         c_guard ((Ptr &(Ptr POINTER ::cte_C ptr \<rightarrow>[''cteMDBNode_C''])) ::mdb_node_C ptr)  \<and>
         s' \<Turnstile>\<^sub>c (Ptr (POINTER)::cte_C ptr) \<and> REST) =
      (POINTER \<noteq> 0 \<longrightarrow>
         s' \<Turnstile>\<^sub>c (Ptr (POINTER)::cte_C ptr) \<and> REST)" 
  apply (rule iffI, clarsimp+)
  apply (rule c_guard_field_lvalue)
  apply (rule c_guard_h_t_valid, assumption) 
  apply (fastforce simp: typ_uinfo_t_def)+
done










(************************************************************************)
(*                                                                      *)
(* cteSwap_ccorres ******************************************************)
(*                                                                      *)
(************************************************************************)

(* FIXME: the cte_ats aren't required here, can be shown using ccorres_guard_from_wp *)
lemma cteSwap_ccorres:
  "ccorres dc xfdc 
          (cte_at' slot  and cte_at' slot' and valid_mdb' and pspace_aligned' and (\<lambda>_. slot \<noteq> slot'))
          (UNIV \<inter> {s. slot1_' s = Ptr slot} 
              \<inter> {s. slot2_' s = Ptr slot'}
              \<inter> {s. ccap_relation cap1 (cap1_' s)}
              \<inter> {s. ccap_relation cap2 (cap2_' s)})
          []
          (cteSwap cap1 slot cap2 slot')
          (Call cteSwap_'proc)"
  apply (cinit (no_ignore_call) lift: slot1_' slot2_' cap1_' cap2_' simp del: return_bind)
  (* the previous line stands for all the following:
  unfolding cteSwap_def
  apply (rule ccorres_Call)
  apply (rule cteSwap_impl [unfolded cteSwap_body_def])
  apply (rule ccorres_rhs_assoc)+ 
  apply (simp del: return_bind Int_UNIV_left)
  apply (cinitlift slot1_' slot2_' cap1_' cap2_')  
 
  apply (erule ssubst)+
  apply (rule ccorres_guard_imp2) -- "We will need the abstract guards to solve the conc. guard obligations"
*)
    
  -- "Start proofs"

  -- "***Main goal***" 
  -- "--- instruction: cte1 \<leftarrow> getCTE slot;              ---"
  -- "---              y \<leftarrow> updateCap slot cap2          ---"
  -- "---              y \<leftarrow> updateCap slot' cap1;        ---"
  -- "---              mdb1 \<leftarrow> return (cteMDBNode cte1); ---"


  -- "Start proofs"

   apply (ctac (no_vcg) pre: ccorres_pre_getCTE ccorres_move_guard_ptr_safe
     add: ccorres_return_cte_mdbnode_safer [where ptr="slot"])+

     -- "generates maingoal + 2 subgoals (Haskell pre/post and C pre/post) for each instruction (except getCTE)"

   -- "***Main Goal***"  
   -- "--- instruction: y <- updateMDB (mdbPrev rvc) (mdbNext_update (%_. slot')) ---" 
         apply csymbr
	 -- "added by sjw \<dots>"
         apply (erule_tac t = prev_ptr in ssubst)
	 apply (ctac (no_vcg) add: updateMDB_mdbPrev_set_mdbNext)
	 apply csymbr
         apply (erule_tac t = next_ptr in ssubst)	 
	 apply (ctac (no_vcg) add: updateMDB_mdbNext_set_mdbPrev)
             apply (rule ccorres_move_c_guard_cte)
	     apply (ctac (no_vcg) pre: ccorres_getCTE
               ccorres_move_guard_ptr_safe
               add: ccorres_return_cte_mdbnode [where ptr = slot']
               ccorres_move_guard_ptr_safe )+
	     apply csymbr
	     apply (erule_tac t = prev_ptr in ssubst)	 
	     apply (ctac (no_vcg) add: updateMDB_mdbPrev_set_mdbNext)
	     apply csymbr
             apply (erule_tac t = next_ptr in ssubst)	 
	     apply (ctac (no_vcg) add: updateMDB_mdbNext_set_mdbPrev)
(*	 
         apply (rule ccorres_split_nothrow [where xf'=xfdc])
         -- "***the correspondance proof for 1st instruction***"  
             apply (erule_tac t = prev_ptr in ssubst)
             apply (rule updateMDB_mdbPrev_set_mdbNext, rule refl, assumption) 

         -- "***the ceqv proof***"
	     apply ceqv

         -- "***the correspondance proof for the rest***" 
         -- "--- instruction: updateMDB (mdbNext rvc) (mdbPrev_update (%_. slot'))  ---" 
           apply csymbr 
           apply (rule ccorres_split_nothrow [where xf'=xfdc]) 
           -- "***the correspondance proof for 1st instruction***"   
               apply (erule_tac t = next_ptr in ssubst)		
               apply (rule updateMDB_mdbNext_set_mdbPrev, rule refl, assumption)
  
           -- "***the ceqv proof***" 
	       apply ceqv 
 
           -- "***the correspondance proof for the rest***"  
           -- "--- instruction: cte2 \<leftarrow> getCTE slot';              ---" 
           -- "---              mdb2 \<leftarrow> return (cteMDBNode cte2);  ---" 
           -- "---              y <- updateMDB slot (const mdb2);  ---"
           -- "---              y <- updateMDB slot' (const rvc);  ---"
             apply (ctac pre: ccorres_getCTE)+ 
                        -- "generates maingoal + 2 subgoals (Haskell pre/post and C pre/post) for each instruction (except getCTE)"
             -- "Main Goal" 
             -- "---instruction:  y <- updateMDB (mdbPrev mdb2) (mdbNext_update (%_. slot)) --"
                   apply csymbr
                   apply (rule ccorres_split_nothrow [where xf'=xfdc])
                   -- "***the correspondance proof for 1st instruction***"  
                       apply (erule_tac t = prev_ptr in ssubst)
                       apply (rule updateMDB_mdbPrev_set_mdbNext, rule refl, assumption) 
          
                   -- "***the ceqv proof***"
          	      apply ceqv
          
                   -- "***the correspondance proof for the rest***"
                   -- "--- instruction: updateMDB (mdbNext rvg) (mdbPrev_update (%_. slot)) ---"
                     apply csymbr
                     apply (erule_tac t = next_ptr in ssubst)		
                     apply (rule updateMDB_mdbNext_set_mdbPrev, rule refl, assumption) 
*)
                    -- "***Haskell pre/post for updateMDB (mdbPrev rvg) (mdbNext_update (%_. slot)) "
                    apply wp
                   -- "***C       pre/post for updateMDB (mdbPrev rvg) (mdbNext_update (%_. slot)) "
                   apply simp
                  -- "***Haskell pre/post for updateMDB slot' (const rvc)"
                  apply wp
                 -- "***C       pre/post for updateMDB slot' (const rvc)"
                  apply simp
                -- "***Haskell pre/post for updateMDB slot (const mdb2)"
                apply wp
               -- "***C       pre/post for updateMDB slot (const mdb2)"
               apply simp
              -- "***Haskell pre/post for return (cteMDBNode cte2) ***"
              apply wp
             -- "***C       pre/post for return (cteMDBNode cte2) ***"
             apply simp
           -- "***Haskell pre/post for updateMDB (mdbPrev rvc) (mdbPrev_update (%_. slot'))"
            apply (clarsimp simp : cte_wp_at_ctes_of)
            apply wp
           -- "***C       pre/post for updateMDB (mdbPrev rvc) (mdbPrev_update (%_. slot'))"
           apply simp
         -- "***Haskell pre/post for updateMDB (mdbPrev rvc) (mdbNext_update (%_. slot'))"
          apply wp
         -- "***C       pre/post for updateMDB (mdbPrev rvc) (mdbNext_update (%_. slot'))"
         apply simp
   -- "***Haskell pre/post for return (cteMDBNode cte1) ***"
        apply wp
   -- "***C       pre/post for return (cteMDBNode cte1) ***"
       apply simp
   -- "***Haskell pre/post for (updateCap slot' cap1) ***"
      apply (clarsimp simp : cte_wp_at_ctes_of)
      apply (wp updateCap_ctes_of_wp)




   -- "***C       pre/post for (updateCap slot' cap1) ***"
     apply simp
   -- "***Haskell pre/post for (updateCap slot cap2) ***"
      apply (clarsimp simp : cte_wp_at_ctes_of) 
      apply (wp updateCap_ctes_of_wp)
   -- "***C       pre/post for (updateCap slot cap2) ***"
   apply simp



  -- "********************"
  -- "*** LAST SUBGOAL ***"
  -- "********************"
  -- "***conjunction of generalised precondition ***" 
  apply (rule conjI)

  -- "***--------------------------------***"
  -- "***Haskell generalised precondition***"
  -- "***--------------------------------***"
  apply (clarsimp simp: cte_wp_at_ctes_of)
  apply (frule (2) is_aligned_3_prev [where p = slot])
  apply (frule (2) is_aligned_3_next [where p = slot])
  apply simp
  apply (intro conjI impI) 
  
  --  "\<exists>cte'. modify_map (\<dots>) slot = Some cte' \<and> cteMDBNode ctea = cteMDBNode cte'"
             apply (simp add: modify_map_if)
	     apply (case_tac ctea)
	     apply simp
	     apply (cases "(slot'=slot)", simp+) 
    -- "no_0 (ctes_of s)"
	   apply (simp add: valid_mdb'_def) -- "yuck"
      apply (erule valid_mdb_ctesE)
      apply assumption

  -- "\<forall>cte. modify_map (modify_map \<dots>) slot' = Some cte \<longrightarrow> \<dots>"
  apply (rule allI)
  apply (rule impI)
   -- "modify_map (modify_map \<dots>) (?P3540 \<dots>) = Some cte"
   -- "\<dots>\<longrightarrow> (\<exists>ctea. ctes_of s (mdbPrev (cteMDBNode cte)) = Some ctea) \<and> is_aligned (mdbPrev (cteMDBNode cte)) 3"
   -- "   Important: we need the first part to prove the second \<Longrightarrow> we need conj_cong"      
      apply (clarsimp simp: modify_map_if cong: if_cong split: if_split_asm)
      apply (erule disjE)
       apply clarsimp      
      apply clarsimp
      apply (drule (2) is_aligned_3_next)
      apply simp
     apply (erule disjE)
      apply clarsimp
      apply (drule (2) is_aligned_3_prev)
      apply simp
     apply clarsimp
     apply (frule (2) is_aligned_3_prev)
     apply (frule (2) is_aligned_3_next)
     apply simp

  -- "***--------------------------***"
  -- "***C generalised precondition***"
  -- "***--------------------------***"
     apply clarsimp
done






(* todo change in cteMove (\<lambda>s. ctes_of s src = Some scte) *)











(************************************************************************)
(*                                                                      *)
(* lemmas used in emptySlot_ccorres *************************************)
(*                                                                      *)
(************************************************************************)


declare if_split [split del]


(* rq CALL mdb_node_ptr_set_mdbNext_'proc \<dots>) is a printing bug
   one should write  CALL mdb_node_ptr_set_mdbNext
*)





lemma not_NullCap_eq_not_cap_null_cap:
  " \<lbrakk>ccap_relation cap cap' ; (s, s') \<in> rf_sr \<rbrakk> \<Longrightarrow>
   (cap \<noteq> NullCap) = (s' \<in> {_. (cap_get_tag cap' \<noteq> scast cap_null_cap)})"
  apply (rule iffI)
   apply (case_tac "cap_get_tag cap' \<noteq> scast cap_null_cap", clarsimp+)
   apply (erule notE)
   apply (simp add: cap_get_tag_NullCap)
  apply (case_tac "cap_get_tag cap' \<noteq> scast cap_null_cap")
   apply (rule notI)
   apply (erule notE)
   apply (simp add: cap_get_tag_NullCap)
  apply clarsimp
done


lemma mdbPrev_CL_mdb_node_lift_mask [simp]:
 "mdbPrev_CL (mdb_node_lift mdbNode) && ~~ mask 3
 = mdbPrev_CL (mdb_node_lift mdbNode)"
  apply (simp add: mdb_node_lift_def mask_def  word_bw_assocs)
done

lemma emptySlot_helper:
  fixes mdbNode
  defines "nextmdb \<equiv> Ptr &(Ptr ((mdbNext_CL (mdb_node_lift mdbNode)))::cte_C ptr\<rightarrow>[''cteMDBNode_C'']) :: mdb_node_C ptr"
  defines "nextcte \<equiv> Ptr ((mdbNext_CL (mdb_node_lift mdbNode)))::cte_C ptr"
  shows "\<lbrakk>cmdbnode_relation rva mdbNode\<rbrakk>
    \<Longrightarrow> ccorres dc xfdc \<top> UNIV hs
           (updateMDB (mdbNext rva) 
             (\<lambda>mdb. mdbFirstBadged_update (\<lambda>_. mdbFirstBadged mdb \<or> mdbFirstBadged rva) (mdbPrev_update (\<lambda>_. mdbPrev rva) mdb)))
           (IF mdbNext_CL (mdb_node_lift mdbNode) \<noteq> 0 THEN
              Guard C_Guard \<lbrace>hrs_htd \<acute>t_hrs \<Turnstile>\<^sub>t  nextcte\<rbrace>
               (CALL mdb_node_ptr_set_mdbPrev(nextmdb,
                ptr_val (Ptr (mdbPrev_CL (mdb_node_lift mdbNode)))))
            FI;;
            IF mdbNext_CL (mdb_node_lift mdbNode) \<noteq> 0 THEN
              Guard C_Guard \<lbrace>hrs_htd \<acute>t_hrs \<Turnstile>\<^sub>t  nextcte\<rbrace>
               (\<acute>ret__unsigned :== CALL mdb_node_get_mdbFirstBadged(h_val (hrs_mem \<acute>t_hrs)
               nextmdb));;
              \<acute>ret__int :== (if \<acute>ret__unsigned \<noteq> 0 then 1 else 0);;
              IF \<acute>ret__int \<noteq> 0 THEN
                SKIP
              ELSE
                \<acute>ret__unsigned :== CALL mdb_node_get_mdbFirstBadged(mdbNode);;
                \<acute>ret__int :== (if \<acute>ret__unsigned \<noteq> 0 then 1 else 0)
              FI;;
              Guard C_Guard \<lbrace>hrs_htd \<acute>t_hrs \<Turnstile>\<^sub>t  nextcte\<rbrace>
               (CALL mdb_node_ptr_set_mdbFirstBadged(nextmdb,scast \<acute>ret__int))
            FI)"
  apply (rule ccorres_guard_imp2)
  apply (rule ccorres_updateMDB_cte_at)
  apply (subgoal_tac "mdbNext rva=(mdbNext_CL (mdb_node_lift mdbNode))")
   prefer 2
   apply (simp add: cmdbnode_relation_def)

  apply (case_tac "mdbNext rva \<noteq> 0")
   apply (case_tac "mdbNext_CL (mdb_node_lift mdbNode) = 0", simp)

   -- "case where mdbNext rva \<noteq> 0 and mdbNext_CL (mdb_node_lift mdbNode) \<noteq> 0"
   apply (unfold updateMDB_def)
   apply (clarsimp simp: Let_def)
   apply (rule ccorres_pre_getCTE [where P = "\<lambda>cte s. ctes_of s (mdbNext rva) = Some cte" and P' = "\<lambda>_. UNIV"])
   apply (rule ccorres_from_vcg)
   apply (rule allI)
   apply (rule conseqPre, vcg)
   apply clarsimp

   apply (frule(1) rf_sr_ctes_of_clift)
   apply (clarsimp simp: typ_heap_simps' nextmdb_def if_1_0_0 nextcte_def)
   apply (intro conjI impI allI)

     -- "\<dots> \<exists>x\<in>fst \<dots>" 
     apply clarsimp
     apply (rule fst_setCTE [OF ctes_of_cte_at], assumption )
     apply (erule bexI [rotated])
     apply (frule (1) rf_sr_ctes_of_clift)
     apply (clarsimp simp add: rf_sr_def cstate_relation_def typ_heap_simps
                Let_def cpspace_relation_def)
     apply (rule conjI)
      prefer 2
      apply (erule_tac t = s' in ssubst)
      apply (simp add: carch_state_relation_def cmachine_state_relation_def h_t_valid_clift_Some_iff
                       cvariable_array_map_const_add_map_option[where f="tcb_no_ctes_proj"]
                       typ_heap_simps'
                  cong: lifth_update)
      apply (erule (1) setCTE_tcb_case)
   
     apply (erule (2)  cspace_cte_relation_upd_mdbI) 
     apply (simp add: cmdbnode_relation_def)
     apply (simp add: mdb_node_to_H_def)
    
     apply (subgoal_tac "mdbFirstBadged_CL (mdb_node_lift mdbNode) && mask (Suc 0) = 
                         mdbFirstBadged_CL (mdb_node_lift mdbNode)")
      prefer 2
      subgoal by (simp add: mdb_node_lift_def mask_def word_bw_assocs)
     apply (subgoal_tac "mdbFirstBadged_CL (cteMDBNode_CL y) && mask (Suc 0) = 
                         mdbFirstBadged_CL (cteMDBNode_CL y)")
      prefer 2 
      apply (drule cteMDBNode_CL_lift [symmetric])
      subgoal by (simp add: mdb_node_lift_def mask_def word_bw_assocs)
     subgoal by (simp add: to_bool_def mask_def)
   -- "\<dots> \<exists>x\<in>fst \<dots>" 
   apply clarsimp
   apply (rule fst_setCTE [OF ctes_of_cte_at], assumption )
   apply (erule bexI [rotated])
   apply (frule (1) rf_sr_ctes_of_clift)
   apply (clarsimp simp add: rf_sr_def cstate_relation_def typ_heap_simps
              Let_def cpspace_relation_def)
   apply (rule conjI)
    prefer 2
    apply (erule_tac t = s' in ssubst)
    apply (simp add: carch_state_relation_def cmachine_state_relation_def 
                     h_t_valid_clift_Some_iff
                     cvariable_array_map_const_add_map_option[where f="tcb_no_ctes_proj"]
                     typ_heap_simps'
                cong: lifth_update)
    apply (erule (1) setCTE_tcb_case)
 
   apply (erule (2)  cspace_cte_relation_upd_mdbI) 
   apply (simp add: cmdbnode_relation_def)
   apply (simp add: mdb_node_to_H_def)
    
   apply (subgoal_tac "mdbFirstBadged_CL (mdb_node_lift mdbNode) && mask (Suc 0) = 
                       mdbFirstBadged_CL (mdb_node_lift mdbNode)")
    prefer 2
    subgoal by (simp add: mdb_node_lift_def mask_def word_bw_assocs)
   apply (subgoal_tac "mdbFirstBadged_CL (cteMDBNode_CL y) && mask (Suc 0) = 
                       mdbFirstBadged_CL (cteMDBNode_CL y)")
    prefer 2 
    apply (drule cteMDBNode_CL_lift [symmetric])
    subgoal by (simp add: mdb_node_lift_def mask_def word_bw_assocs)
   apply (simp add: to_bool_def mask_def split: if_split)

  -- "trivial case where mdbNext rva = 0"
   apply (simp add:ccorres_cond_empty_iff)
   apply (rule ccorres_guard_imp2)
   apply (rule ccorres_return_Skip)
   apply simp
  apply (clarsimp simp: cmdbnode_relation_def)
done



(************************************************************************)
(*                                                                      *)
(* emptySlot_ccorres ****************************************************)
(*                                                                      *)
(************************************************************************)


(* ML "set CtacImpl.trace_ctac"*)


lemma mdbNext_CL_mdb_node_lift_eq_mdbNext:
  "cmdbnode_relation n n' \<Longrightarrow>  (mdbNext_CL (mdb_node_lift n')) =(mdbNext n)"
  by (erule cmdbnode_relationE, fastforce simp: mdbNext_to_H)

lemma mdbPrev_CL_mdb_node_lift_eq_mdbPrev:
  "cmdbnode_relation n n' \<Longrightarrow>  (mdbPrev_CL (mdb_node_lift n')) =(mdbPrev n)"
  by (erule cmdbnode_relationE, fastforce simp: mdbNext_to_H)


lemma mdbNext_not_zero_eq_simpler:
  "cmdbnode_relation n n' \<Longrightarrow> (mdbNext n \<noteq> 0) = (mdbNext_CL (mdb_node_lift n') \<noteq> 0)"
  apply clarsimp 
  apply (erule cmdbnode_relationE)
  apply (fastforce simp: mdbNext_to_H)
  done



lemma mdbPrev_not_zero_eq_simpler:
  "cmdbnode_relation n n' \<Longrightarrow> (mdbPrev n \<noteq> 0) = (mdbPrev_CL (mdb_node_lift n') \<noteq> 0)"
  apply clarsimp 
  apply (erule cmdbnode_relationE)
  apply (fastforce simp: mdbPrev_to_H)
  done

lemma h_t_valid_and_cslift_and_c_guard_field_mdbPrev_CL:
      " \<lbrakk>(s, s') \<in> rf_sr; cte_at' slot s;  valid_mdb' s; cslift s' (Ptr slot) = Some cte'\<rbrakk>
       \<Longrightarrow> (mdbPrev_CL (mdb_node_lift (cteMDBNode_C cte')) \<noteq> 0) \<longrightarrow>
           s' \<Turnstile>\<^sub>c ( Ptr (mdbPrev_CL (mdb_node_lift (cteMDBNode_C cte'))) :: cte_C ptr) \<and>
           (\<exists> cten. cslift s' (Ptr (mdbPrev_CL (mdb_node_lift (cteMDBNode_C cte'))) :: cte_C ptr) = Some cten)  \<and>
           c_guard (Ptr &(Ptr (mdbPrev_CL (mdb_node_lift (cteMDBNode_C cte')))::cte_C ptr\<rightarrow>[''cteMDBNode_C'']) :: mdb_node_C ptr)"
  apply (clarsimp simp: cte_wp_at_ctes_of) 
  apply (drule (1) valid_mdb_ctes_of_prev)
  apply (frule (2) rf_sr_cte_relation)
  apply (drule ccte_relation_cmdbnode_relation)
  apply (simp add: mdbPrev_not_zero_eq_simpler)
  apply (clarsimp simp: cte_wp_at_ctes_of)
  apply (drule (1) rf_sr_ctes_of_clift [rotated])+
  apply (clarsimp simp: typ_heap_simps)

  apply (rule c_guard_field_lvalue [rotated])
  apply (fastforce simp: typ_uinfo_t_def)+
  apply (rule c_guard_clift)
  apply (simp add: typ_heap_simps)
done

lemma h_t_valid_and_cslift_and_c_guard_field_mdbNext_CL:
      " \<lbrakk>(s, s') \<in> rf_sr; cte_at' slot s;  valid_mdb' s; cslift s' (Ptr slot) = Some cte'\<rbrakk>
       \<Longrightarrow> (mdbNext_CL (mdb_node_lift (cteMDBNode_C cte')) \<noteq> 0) \<longrightarrow>
           s' \<Turnstile>\<^sub>c ( Ptr (mdbNext_CL (mdb_node_lift (cteMDBNode_C cte'))) :: cte_C ptr) \<and>
           (\<exists> cten. cslift s' (Ptr (mdbNext_CL (mdb_node_lift (cteMDBNode_C cte'))) :: cte_C ptr) = Some cten)  \<and>
           c_guard (Ptr &(Ptr (mdbNext_CL (mdb_node_lift (cteMDBNode_C cte')))::cte_C ptr\<rightarrow>[''cteMDBNode_C'']) :: mdb_node_C ptr)"
  apply (clarsimp simp: cte_wp_at_ctes_of) 
  apply (drule (1) valid_mdb_ctes_of_next)
  apply (frule (2) rf_sr_cte_relation)
  apply (drule ccte_relation_cmdbnode_relation)
  apply (simp add: mdbNext_not_zero_eq_simpler)
  apply (clarsimp simp: cte_wp_at_ctes_of)
  apply (drule (1) rf_sr_ctes_of_clift [rotated])+
  apply (clarsimp simp: typ_heap_simps)

  apply (rule c_guard_field_lvalue [rotated])
  apply (fastforce simp: typ_uinfo_t_def)+
  apply (rule c_guard_clift)
  apply (simp add: typ_heap_simps)
done


lemma valid_mdb_Prev_neq_Next_better: 
    "\<lbrakk> valid_mdb' s; ctes_of s p = Some cte \<rbrakk> \<Longrightarrow>  mdbPrev (cteMDBNode cte) \<noteq> 0   \<longrightarrow>
     (mdbNext (cteMDBNode cte)) \<noteq> (mdbPrev (cteMDBNode cte))"
  apply (rule impI)
  apply (simp add: valid_mdb'_def)
  apply (simp add: valid_mdb_ctes_def) 
  apply (elim conjE)
  apply (drule (1) mdb_chain_0_no_loops)
  apply (simp add: valid_dlist_def)
  apply (erule_tac x=p in allE)
  apply (erule_tac x=cte in allE)
  apply (simp add: Let_def)  
  apply clarsimp 
  apply (drule_tac s="mdbNext (cteMDBNode cte)" in sym)
  apply simp  
  apply (simp add: no_loops_def) 
  apply (erule_tac x= "(mdbNext (cteMDBNode cte))" in allE) 
  apply (erule notE, rule trancl_trans)
    apply (rule r_into_trancl)
    apply (simp add: mdb_next_unfold)
  apply (rule r_into_trancl)
  apply (simp add: mdb_next_unfold)
done

(* TODO: move *)

definition
  irq_opt_relation_def:
  "irq_opt_relation (airq :: (10 word) option) (cirq :: word16) \<equiv>
       case airq of
         Some irq \<Rightarrow> (cirq = ucast irq \<and>
                      irq \<noteq> scast irqInvalid \<and>
                      ucast irq \<le> (scast Kernel_C.maxIRQ :: word16))
       | None \<Rightarrow> cirq = scast irqInvalid"


declare unat_ucast_up_simp[simp]


lemma setIRQState_ccorres:
  "ccorres dc xfdc
          (\<top> and (\<lambda>s. ucast irq \<le> (scast Kernel_C.maxIRQ :: word16)))
          (UNIV \<inter> {s. irqState_' s = irqstate_to_C irqState} 
                \<inter> {s. irq_' s = (ucast irq :: word16)}  )
          []
         (setIRQState irqState irq)
         (Call setIRQState_'proc )"
proof -
  have is_up_8_16[simp]: "is_up (ucast :: word8 \<Rightarrow> word16)"
  by (simp add: is_up_def source_size_def target_size_def word_size)


show ?thesis
  apply (rule ccorres_gen_asm)
  apply (cinit simp del: return_bind)
   apply (rule ccorres_symb_exec_l)
      apply simp
      apply (rule_tac r'="dc" and xf'="xfdc" in ccorres_split_nothrow)

          apply (rule_tac P= "\<lambda>s. st = (ksInterruptState s)"
                      and P'= "(UNIV \<inter> {s. irqState_' s = irqstate_to_C irqState} 
                                     \<inter> {s. irq_' s = ucast irq}  )" 
                   in ccorres_from_vcg)
          apply (rule allI, rule conseqPre, vcg)
          apply (clarsimp simp: setInterruptState_def)
          apply (clarsimp simp: simpler_modify_def) 
          apply (clarsimp simp: rf_sr_def cstate_relation_def Let_def
                                carch_state_relation_def cmachine_state_relation_def)
          apply (simp add: cinterrupt_relation_def Kernel_C.maxIRQ_def)
          apply (clarsimp simp:  word_sless_msb_less order_le_less_trans
                            unat_ucast_no_overflow_le word_le_nat_alt ucast_ucast_b 
                         split: if_split )
          apply (rule word_0_sle_from_less)

          apply (rule order_less_le_trans[where y = 160])
           apply (simp add: unat_ucast_no_overflow_le)
          apply simp
         apply ceqv
 
        apply (ctac add:  maskInterrupt_ccorres)

       apply wp
      apply vcg

     apply wp  
    apply (simp add: getInterruptState_def gets_def) 
    apply wp
   apply (simp add: empty_fail_def getInterruptState_def simpler_gets_def) 

  apply clarsimp
  apply (simp add: from_bool_def)
  apply (cases irqState, simp_all)
  apply (simp add: Kernel_C.IRQSignal_def Kernel_C.IRQInactive_def) 
  apply (simp add: Kernel_C.IRQTimer_def Kernel_C.IRQInactive_def)
  apply (simp add: Kernel_C.IRQInactive_def Kernel_C.IRQReserved_def)
  done
qed


lemma deletedIRQHandler_ccorres:
  "ccorres dc xfdc
         (\<lambda>s. ucast irq \<le> (scast Kernel_C.maxIRQ :: 16 word))
         (UNIV\<inter> {s. irq_' s = ucast irq}) []
         (deletedIRQHandler irq)
         (Call deletedIRQHandler_'proc )"
  apply (cinit simp del: return_bind)
  apply (ctac add: setIRQState_ccorres)
  apply clarsimp
done

lemma deletedIRQHandler_opt_ccorres:
  "irq_opt_relation irq cirq \<Longrightarrow>
    ccorres dc xfdc \<top> UNIV [SKIP] 
     (case irq of None \<Rightarrow> return () | Some a \<Rightarrow> deletedIRQHandler a) 
     (IF ucast cirq \<noteq> irqInvalid THEN CALL deletedIRQHandler (cirq)  FI) "
  apply (simp only: irq_opt_relation_def)
  apply (cases irq)
   apply (clarsimp simp:irqInvalid_def)
   apply (simp add: ccorres_cond_iffs)
   apply (rule ccorres_return_Skip )
  apply clarsimp
  apply (subgoal_tac " ucast cirq \<noteq> irqInvalid")
   prefer 2
   apply (clarsimp simp: irqInvalid_def Kernel_C.maxIRQ_def)
   apply (word_bitwise,simp) (* So annoy that signed word ucast mixed with word ucast *)
  apply (simp add: ccorres_cond_iffs)
  apply (rule ccorres_guard_imp2)
   apply (ctac add: deletedIRQHandler_ccorres)
  apply simp
done

(* for long printing: switch off printing of abbreviation :

ML {*fun show_abbrevs true = (PrintMode.print_mode := List.filter
                           ((curry op<>) "no_abbrevs")
                           (!PrintMode.print_mode))
  | show_abbrevs false = (PrintMode.print_mode := "no_abbrevs"::
                            (!PrintMode.print_mode))

val () = show_abbrevs false;

*}

then 
ML {*show_abbrevs true*}
ML {*show_abbrevs false*}

or if within proof mode:

ML_command {*show_abbrevs true*}
ML_command {*show_abbrevs false*}

*)
lemmas ccorres_split_noop_lhs
  = ccorres_split_nothrow[where c=Skip, OF _ ceqv_refl _ _ hoarep.Skip,
    simplified ccorres_seq_skip]

(* FIXME: to SR_Lemmas *)
lemma region_is_bytes_subset:
  "region_is_bytes' ptr sz htd
    \<Longrightarrow> {ptr' ..+ sz'} \<subseteq> {ptr ..+ sz}
    \<Longrightarrow> region_is_bytes' ptr' sz' htd"
  by (auto simp: region_is_bytes'_def)

lemma region_actually_is_bytes_subset:
  "region_actually_is_bytes' ptr sz htd
    \<Longrightarrow> {ptr' ..+ sz'} \<subseteq> {ptr ..+ sz}
    \<Longrightarrow> region_actually_is_bytes' ptr' sz' htd"
  by (auto simp: region_actually_is_bytes'_def)

lemma intvl_both_le:
  "\<lbrakk> a \<le> x; unat x + y \<le> unat a + b \<rbrakk>
    \<Longrightarrow>  {x ..+ y} \<le> {a ..+ b}"
  apply (rule order_trans[OF _ intvl_sub_offset[where x="x - a"]])
   apply (simp, rule order_refl)
  apply unat_arith
  done

lemma untypedZeroRange_idx_forward_helper:
  "isUntypedCap cap
    \<Longrightarrow> capFreeIndex cap \<le> idx
    \<Longrightarrow> idx \<le> 2 ^ capBlockSize cap
    \<Longrightarrow> valid_cap' cap s
    \<Longrightarrow> (case (untypedZeroRange cap, untypedZeroRange (capFreeIndex_update (\<lambda>_. idx) cap))
       of (Some (a, b), Some (a', b')) \<Rightarrow> {a' ..+ unat (b' + 1 - a')} \<subseteq> {a ..+ unat (b + 1 - a)}
        | _ \<Rightarrow> True)"
  apply (clarsimp split: option.split)
  apply (clarsimp simp: untypedZeroRange_def max_free_index_def Let_def
                        isCap_simps valid_cap_simps' capAligned_def
                 split: if_split_asm)
  apply (erule subsetD[rotated], rule intvl_both_le)
   apply (clarsimp simp: getFreeRef_def)
   apply (rule word_plus_mono_right)
    apply (rule PackedTypes.of_nat_mono_maybe_le)
     apply (erule order_le_less_trans, rule power_strict_increasing, simp_all)
   apply (erule is_aligned_no_wrap')
   apply (rule word_of_nat_less, simp)
  apply (simp add: getFreeRef_def)
  apply (simp add: unat_plus_simple[THEN iffD1, OF is_aligned_no_wrap']
                   word_of_nat_less)
  apply (simp add: word_of_nat_le unat_sub
                   order_le_less_trans[OF _ power_strict_increasing]
                   unat_of_nat_eq[where 'a=32, folded word_bits_def])
  done

lemma intvl_close_Un:
  "y = x + of_nat n
    \<Longrightarrow> ({x ..+ n} \<union> {y ..+ m}) = {x ..+ n + m}"
  apply ((simp add: intvl_def, safe, simp_all,
    simp_all only: of_nat_add[symmetric]); (rule exI, strengthen refl))
  apply simp_all
  apply (rule ccontr)
  apply (drule_tac x="k - n" in spec)
  apply simp
  done

lemma untypedZeroRange_idx_backward_helper:
  "isUntypedCap cap
    \<Longrightarrow> idx \<le> capFreeIndex cap
    \<Longrightarrow> idx \<le> 2 ^ capBlockSize cap
    \<Longrightarrow> valid_cap' cap s
    \<Longrightarrow> (case untypedZeroRange (capFreeIndex_update (\<lambda>_. idx) cap)
       of None \<Rightarrow> True | Some (a', b') \<Rightarrow>
        {a' ..+ unat (b' + 1 - a')} \<subseteq> {capPtr cap + of_nat idx ..+ (capFreeIndex cap - idx)}
            \<union> (case untypedZeroRange cap
               of Some (a, b) \<Rightarrow> {a ..+ unat (b + 1 - a)}
                | None \<Rightarrow> {})
  )"
  apply (clarsimp split: option.split, intro impI conjI allI)
   apply (rule intvl_both_le; clarsimp simp: untypedZeroRange_def
                         max_free_index_def Let_def
                         isCap_simps valid_cap_simps' capAligned_def
                  split: if_split_asm)
    apply (clarsimp simp: getFreeRef_def)
   apply (clarsimp simp: getFreeRef_def)
   apply (simp add: word_of_nat_le unat_sub
                    order_le_less_trans[OF _ power_strict_increasing]
                    unat_of_nat_eq[where 'a=32, folded word_bits_def])
  apply (subst intvl_close_Un)
   apply (clarsimp simp: untypedZeroRange_def
                         max_free_index_def Let_def
                         getFreeRef_def
                  split: if_split_asm)
  apply (clarsimp simp: untypedZeroRange_def
                        max_free_index_def Let_def
                        getFreeRef_def isCap_simps valid_cap_simps'
                 split: if_split_asm)
  apply (simp add: word_of_nat_le unat_sub capAligned_def
                   order_le_less_trans[OF _ power_strict_increasing]
                   order_le_less_trans[where x=idx]
                   unat_of_nat_eq[where 'a=32, folded word_bits_def])
  done

lemma ctes_of_untyped_zero_rf_sr_case:
  "\<lbrakk> ctes_of s p = Some cte; (s, s') \<in> rf_sr;
      untyped_ranges_zero' s \<rbrakk>
    \<Longrightarrow> case untypedZeroRange (cteCap cte)
               of None \<Rightarrow> True
    | Some (start, end) \<Rightarrow> region_actually_is_zero_bytes start (unat ((end + 1) - start)) s'"
  by (simp split: option.split add: ctes_of_untyped_zero_rf_sr)

lemma gsUntypedZeroRanges_update_helper:
  "(\<sigma>, s) \<in> rf_sr
    \<Longrightarrow> (zero_ranges_are_zero (gsUntypedZeroRanges \<sigma>) (t_hrs_' (globals s))
            \<longrightarrow> zero_ranges_are_zero (f (gsUntypedZeroRanges \<sigma>)) (t_hrs_' (globals s)))
    \<Longrightarrow> (gsUntypedZeroRanges_update f \<sigma>, s) \<in> rf_sr"
  by (clarsimp simp: rf_sr_def cstate_relation_def Let_def)

lemma heap_list_zero_Ball_intvl:
  "heap_list_is_zero hmem ptr n = (\<forall>x \<in> {ptr ..+ n}. hmem x = 0)"
  apply safe
   apply (erule heap_list_h_eq_better)
   apply (simp add: heap_list_rpbs)
  apply (rule trans[OF heap_list_h_eq2 heap_list_rpbs])
  apply simp
  done

lemma untypedZeroRange_not_device:
  "untypedZeroRange cap = Some r
    \<Longrightarrow> \<not> capIsDevice cap"
  by (clarsimp simp: untypedZeroRange_def)

lemma updateTrackedFreeIndex_noop_ccorres:
  "ccorres dc xfdc (cte_wp_at' ((\<lambda>cap. isUntypedCap cap
              \<and> idx \<le> 2 ^ capBlockSize cap
              \<and> (capFreeIndex cap \<le> idx \<or> cap' = cap)) o cteCap) slot
          and valid_objs' and untyped_ranges_zero')
      {s. \<not> capIsDevice cap' \<longrightarrow> region_actually_is_zero_bytes (capPtr cap' + of_nat idx) (capFreeIndex cap' - idx) s} hs
      (updateTrackedFreeIndex slot idx) Skip"
  (is "ccorres dc xfdc ?P ?P' _ _ _")
  apply (simp add: updateTrackedFreeIndex_def getSlotCap_def)
  apply (rule ccorres_guard_imp)
    apply (rule ccorres_pre_getCTE[where P="\<lambda>rv.
        cte_wp_at' (op = rv) slot and ?P" and P'="K ?P'"])
    apply (rule ccorres_from_vcg)
    apply (rule allI, rule conseqPre, vcg)
    apply (clarsimp simp: cte_wp_at_ctes_of)
    apply (frule(1) ctes_of_valid')
    apply (frule(2) ctes_of_untyped_zero_rf_sr_case)
    apply (clarsimp simp: simpler_modify_def bind_def cte_wp_at_ctes_of)
    apply (erule gsUntypedZeroRanges_update_helper)
    apply (clarsimp simp: zero_ranges_are_zero_def
                   split: if_split)
    apply (case_tac "(a, b) \<in> gsUntypedZeroRanges \<sigma>")
     apply (drule(1) bspec, simp)
    apply (erule disjE_L)
     apply (frule(3) untypedZeroRange_idx_forward_helper)
     apply (clarsimp simp: isCap_simps valid_cap_simps')
     apply (case_tac "untypedZeroRange (cteCap cte)")
      apply (clarsimp simp: untypedZeroRange_def
                       valid_cap_simps'
                       max_free_index_def Let_def
                     split: if_split_asm)
     apply clarsimp
     apply (thin_tac "\<not> capIsDevice cap' \<longrightarrow> P" for P)
     apply (clarsimp split: option.split_asm)
     apply (subst region_actually_is_bytes_subset, simp+)
     apply (subst heap_list_is_zero_mono2, simp+)
    apply (frule untypedZeroRange_idx_backward_helper[where idx=idx],
      simp+)
    apply (clarsimp simp: isCap_simps valid_cap_simps')
    apply (clarsimp split: option.split_asm)
     apply (clarsimp dest!: untypedZeroRange_not_device)
     apply (subst region_actually_is_bytes_subset, simp+)
     apply (subst heap_list_is_zero_mono2, simp+)
    apply (simp add: region_actually_is_bytes'_def heap_list_zero_Ball_intvl)
    apply (clarsimp dest!: untypedZeroRange_not_device)
    apply blast
   apply (clarsimp simp: cte_wp_at_ctes_of)
  apply clarsimp
  done

lemma updateTrackedFreeIndex_forward_noop_ccorres:
  "ccorres dc xfdc (cte_wp_at' ((\<lambda>cap. isUntypedCap cap
              \<and> capFreeIndex cap \<le> idx \<and> idx \<le> 2 ^ capBlockSize cap) o cteCap) slot
          and valid_objs' and untyped_ranges_zero') UNIV hs
      (updateTrackedFreeIndex slot idx) Skip"
  (is "ccorres dc xfdc ?P UNIV _ _ _")
  apply (rule ccorres_name_pre)
   apply (rule ccorres_guard_imp2,
     rule_tac cap'="cteCap (the (ctes_of s slot))" in updateTrackedFreeIndex_noop_ccorres)
  apply (clarsimp simp: cte_wp_at_ctes_of region_actually_is_bytes'_def)
  done

lemma clearUntypedFreeIndex_noop_ccorres:
  "ccorres dc xfdc (valid_objs' and untyped_ranges_zero') UNIV hs
      (clearUntypedFreeIndex p) Skip"
  apply (simp add: clearUntypedFreeIndex_def getSlotCap_def)
  apply (rule ccorres_guard_imp)
    apply (rule ccorres_pre_getCTE[where P="\<lambda>rv. cte_wp_at' (op = rv) p
        and valid_objs' and untyped_ranges_zero'" and P'="K UNIV"])
    apply (case_tac "cteCap cte", simp_all add: ccorres_guard_imp[OF ccorres_return_Skip])[1]
    apply (rule ccorres_guard_imp, rule updateTrackedFreeIndex_forward_noop_ccorres)
     apply (clarsimp simp: cte_wp_at_ctes_of max_free_index_def)
     apply (frule(1) Finalise_R.ctes_of_valid')
     apply (clarsimp simp: valid_cap_simps')
    apply simp
   apply (clarsimp simp: cte_wp_at_ctes_of)
  apply simp
  done

lemma emptySlot_ccorres:
  "ccorres dc xfdc 
          (valid_mdb' and valid_objs' and pspace_aligned'
                      and untyped_ranges_zero')
          (UNIV \<inter> {s. slot_' s = Ptr slot} 
                \<inter> {s. irq_opt_relation irq (irq_' s)}  )
          []
          (emptySlot slot irq)
          (Call emptySlot_'proc)"
  apply (cinit lift: slot_' irq_' simp: case_Null_If)

  -- "--- handle the clearUntypedFreeIndex"
   apply (rule ccorres_split_noop_lhs, rule clearUntypedFreeIndex_noop_ccorres)

  -- "--- instruction: newCTE \<leftarrow> getCTE slot;                 ---"
    apply (rule ccorres_pre_getCTE) 
  -- "--- instruction: CALL on C side"
    apply (rule ccorres_move_c_guard_cte)
    apply csymbr
    apply (rule ccorres_abstract_cleanup)
    apply (rename_tac cap_tag)
    apply (rule_tac P="(cap_tag = scast cap_null_cap)
          = (cteCap newCTE = NullCap)" in ccorres_gen_asm2)
    apply (simp del: Collect_const)

   -- "--- instruction: if-then-else / IF-THEN-ELSE "
    apply (rule ccorres_cond2'[where R=\<top>])

    -- "*** link between abstract and concrete conditionals ***"
      apply (clarsimp split: if_split)

    -- "*** proof for the 'else' branch (return () and SKIP) ***"
     prefer 2
     apply (ctac add: ccorres_return_Skip[unfolded dc_def])

    -- "*** proof for the 'then' branch ***"

    -- "---instructions: multiple on C side, including mdbNode fetch"
    apply (rule ccorres_rhs_assoc)+   
              -- "we have to do it here because the first assoc did not apply inside the then block"
    apply (rule ccorres_move_c_guard_cte | csymbr)+
    apply (rule ccorres_symb_exec_r)
      apply (rule_tac xf'="mdbNode_'" in ccorres_abstract, ceqv)
      apply (rename_tac "cmdbNode")
      apply (rule_tac P="cmdbnode_relation (cteMDBNode newCTE) cmdbNode"
        in ccorres_gen_asm2)
      apply csymbr+

      -- "--- instruction: updateMDB (mdbPrev rva) (mdbNext_update \<dots>) but with Ptr\<dots>\<noteq> NULL on C side"
      apply (simp only:Ptr_not_null_pointer_not_zero) --"replaces Ptr p \<noteq> NULL with p\<noteq>0"

      -- "--- instruction: y \<leftarrow> updateMDB (mdbPrev rva) (mdbNext_update (\<lambda>_. mdbNext rva)) "
      apply (ctac (no_simp, no_vcg) pre:ccorres_move_guard_ptr_safe
        add: updateMDB_mdbPrev_set_mdbNext)
            -- "here ctac alone does not apply because the subgoal generated 
                by the rule are not solvable by simp"
            -- "so we have to use (no_simp) (or apply (rule ccorres_split_nothrow))"
          apply (simp add: cmdbnode_relation_def)
         apply assumption
      -- "*** Main goal ***"
      -- "--- instruction: updateMDB (mdbNext rva)
                    (\<lambda>mdb. mdbFirstBadged_update (\<lambda>_. mdbFirstBadged mdb \<or> mdbFirstBadged rva)
                            (mdbPrev_update (\<lambda>_. mdbPrev rva) mdb));"
        apply (rule ccorres_rhs_assoc2 )  -- " to group the 2 first C instrutions together"
        apply (ctac (no_vcg) add: emptySlot_helper)

      -- "--- instruction:  y \<leftarrow> updateCap slot capability.NullCap;"
          apply (simp del: Collect_const)
          apply csymbr
            apply (ctac (no_vcg) pre:ccorres_move_guard_ptr_safe)
            apply csymbr
            apply (rule ccorres_move_c_guard_cte)
                -- "--- instruction y \<leftarrow> updateMDB slot (\<lambda>a. nullMDBNode);"
                apply (ctac (no_vcg) pre: ccorres_move_guard_ptr_safe
                  add: ccorres_updateMDB_const [unfolded const_def])

                  -- "the case irq "

                  apply (erule deletedIRQHandler_opt_ccorres [unfolded dc_def]) 

                -- "Haskell pre/post for y \<leftarrow> updateMDB slot (\<lambda>a. nullMDBNode);"
                 apply wp
                -- "C       pre/post for y \<leftarrow> updateMDB slot (\<lambda>a. nullMDBNode);"
                apply simp
              -- "C pre/post for the 2nd CALL "
            -- "Haskell pre/post for y \<leftarrow> updateCap slot capability.NullCap;"
             apply wp
            -- "C       pre/post for y \<leftarrow> updateCap slot capability.NullCap;"
            apply (simp add: Collect_const_mem cmdbnode_relation_def mdb_node_to_H_def nullMDBNode_def false_def)
        -- "Haskell pre/post for the two nested updates "
         apply wp
        -- "C       pre/post for the two nested updates "
        apply (simp add: Collect_const_mem ccap_relation_NullCap_iff)
      -- "Haskell pre/post for  (updateMDB (mdbPrev rva) (mdbNext_update (\<lambda>_. mdbNext rva)))"
       apply (simp, wp)
      -- "C       pre/post for  (updateMDB (mdbPrev rva) (mdbNext_update (\<lambda>_. mdbNext rva)))"
      apply simp+
     apply vcg
    apply (rule conseqPre, vcg)
    apply clarsimp
   apply simp
   apply (wp hoare_vcg_all_lift hoare_vcg_imp_lift)

  -- "final precondition proof"
  apply (clarsimp simp: typ_heap_simps Collect_const_mem
                        cte_wp_at_ctes_of
             split del: if_split)

  apply (rule conjI)
   -- "Haskell side"
   apply (simp add: is_aligned_3_prev is_aligned_3_next)

  -- "C side"
  apply (clarsimp simp: map_comp_Some_iff typ_heap_simps)
  apply (subst cap_get_tag_isCap)
   apply (rule ccte_relation_ccap_relation)
   apply (simp add: ccte_relation_def c_valid_cte_def
                    cl_valid_cte_def c_valid_cap_def)
  apply simp
  done


(************************************************************************)
(*                                                                      *)
(* capSwapForDelete_ccorres *********************************************)
(*                                                                      *)
(************************************************************************)

lemma ccorres_return_void_C:
  "ccorres dc xfdc \<top> UNIV (SKIP # hs) (return rv) (return_void_C)"
  apply (rule ccorres_from_vcg_throws)
  apply (simp add: return_def)
  apply (rule allI, rule conseqPre)
  apply vcg
  apply simp
  done

declare Collect_const [simp del]

lemma capSwapForDelete_ccorres:
  "ccorres dc xfdc 
          (valid_mdb' and pspace_aligned')
          (UNIV \<inter> {s. slot1_' s = Ptr slot1} \<inter> {s. slot2_' s = Ptr slot2})
          []
          (capSwapForDelete slot1 slot2)
          (Call capSwapForDelete_'proc)"
  apply (cinit lift: slot1_' slot2_' simp del: return_bind)
  -- "***Main goal***" 
  -- "--- instruction: when (slot1 \<noteq> slot2) \<dots> / IF Ptr slot1 = Ptr slot2 THEN \<dots>" 
   apply (simp add:when_def)
   apply (rule ccorres_if_cond_throws2 [where Q = \<top> and Q' = \<top>]) 
      apply (case_tac "slot1=slot2", simp+)
     apply (rule ccorres_return_void_C [simplified dc_def])

  -- "***Main goal***"
  -- "--- ccorres goal with 2 affectations (cap1 and cap2) on both on Haskell and C "
  -- "---   \<Longrightarrow> execute each part independently"
    apply (simp add: liftM_def cong: call_ignore_cong)
    apply (rule ccorres_pre_getCTE)+
    apply (rule ccorres_move_c_guard_cte, rule ccorres_symb_exec_r)+
  -- "***Main goal***"
        apply (ctac (no_vcg) add: cteSwap_ccorres [unfolded dc_def] )
       -- "C Hoare triple for \<acute>cap2 :== \<dots>"
       apply vcg
       -- "C existential Hoare triple for \<acute>cap2 :== \<dots>"
      apply simp
      apply (rule conseqPre)
       apply vcg
      apply simp
     -- "C Hoare triple for \<acute>cap1 :== \<dots>"
     apply vcg
     -- "C existential Hoare triple for \<acute>cap1 :== \<dots>"
    apply simp
    apply (rule conseqPre)
     apply vcg
    apply simp

  -- "Hoare triple for return_void"
   apply vcg

  -- "***Generalized preconditions***" 
  apply simp
  apply (clarsimp simp: cte_wp_at_ctes_of map_comp_Some_iff 
    typ_heap_simps ccap_relation_def)
  apply (simp add: cl_valid_cte_def c_valid_cap_def)
done



declare Collect_const [simp add]

(************************************************************************)
(*                                                                      *)
(* Arch_sameRegionAs_ccorres ********************************************)
(*                                                                      *)
(************************************************************************)
lemma cap_get_tag_PageCap_small_frame:
  "ccap_relation cap cap' \<Longrightarrow>
   (cap_get_tag cap' = scast cap_small_frame_cap) =
   (cap =
    capability.ArchObjectCap
     (PageCap (to_bool ((cap_small_frame_cap_CL.capFIsDevice_CL (cap_small_frame_cap_lift cap')))) (cap_small_frame_cap_CL.capFBasePtr_CL (cap_small_frame_cap_lift cap'))
              (vmrights_to_H (cap_small_frame_cap_CL.capFVMRights_CL (cap_small_frame_cap_lift cap')))
              vmpage_size.ARMSmallPage
   (if cap_small_frame_cap_CL.capFMappedASIDHigh_CL (cap_small_frame_cap_lift cap') = 0
        \<and> cap_small_frame_cap_CL.capFMappedASIDLow_CL (cap_small_frame_cap_lift cap') = 0
    then None else
     Some ((cap_small_frame_cap_CL.capFMappedASIDHigh_CL (cap_small_frame_cap_lift cap') << asid_low_bits) +
          cap_small_frame_cap_CL.capFMappedASIDLow_CL (cap_small_frame_cap_lift cap'),
          cap_small_frame_cap_CL.capFMappedAddress_CL (cap_small_frame_cap_lift cap')))))"
  apply (rule iffI)
   apply (erule ccap_relationE)  
   apply (clarsimp simp add: cap_lifts cap_to_H_def Let_def split: if_split)
  apply (simp add: cap_get_tag_isCap isCap_simps pageSize_def)
done


lemma cap_get_tag_PageCap_frame:
  "ccap_relation cap cap' \<Longrightarrow>
   (cap_get_tag cap' = scast cap_frame_cap) =
   (cap =
    capability.ArchObjectCap
     (PageCap (to_bool (cap_frame_cap_CL.capFIsDevice_CL (cap_frame_cap_lift cap'))) (cap_frame_cap_CL.capFBasePtr_CL (cap_frame_cap_lift cap'))
              (vmrights_to_H (cap_frame_cap_CL.capFVMRights_CL (cap_frame_cap_lift cap')))
              (framesize_to_H (capFSize_CL (cap_frame_cap_lift cap')))
    (if cap_frame_cap_CL.capFMappedASIDHigh_CL (cap_frame_cap_lift cap') = 0
          \<and> cap_frame_cap_CL.capFMappedASIDLow_CL (cap_frame_cap_lift cap') = 0
     then None else
     Some ((cap_frame_cap_CL.capFMappedASIDHigh_CL (cap_frame_cap_lift cap') << asid_low_bits) +
          cap_frame_cap_CL.capFMappedASIDLow_CL (cap_frame_cap_lift cap'),
          cap_frame_cap_CL.capFMappedAddress_CL (cap_frame_cap_lift cap')))))"
  apply (rule iffI)   
   apply (erule ccap_relationE)  
   apply (clarsimp simp add: cap_lifts cap_to_H_def Let_def  split: if_split)
  apply (simp add: cap_get_tag_isCap isCap_simps pageSize_def)
done




lemma is_aligned_small_frame_cap_lift:
   "cap_get_tag cap = scast cap_small_frame_cap \<Longrightarrow>
    is_aligned (cap_small_frame_cap_CL.capFBasePtr_CL 
                        (cap_small_frame_cap_lift cap)) 12"
  apply (simp add: cap_small_frame_cap_lift_def
                   cap_lift_small_frame_cap)
  apply (rule is_aligned_andI2)
  apply (simp add: is_aligned_def)
  done

lemma fff_is_pageBits:
  "(0xFFF :: word32) = 2 ^ pageBits - 1" 
  by (simp add: pageBits_def)


(* used? *)
lemma valid_cap'_PageCap_is_aligned:
  "valid_cap' (ArchObjectCap (arch_capability.PageCap d w r sz option)) t  \<Longrightarrow>
  is_aligned w (pageBitsForSize sz)"
  apply (simp add: valid_cap'_def capAligned_def) 
done



lemma gen_framesize_to_H_is_framesize_to_H_if_not_ARMSmallPage:
  " c\<noteq>scast Kernel_C.ARMSmallPage \<Longrightarrow>gen_framesize_to_H c =  framesize_to_H c"
  by (simp add: gen_framesize_to_H_def framesize_to_H_def)



lemma Arch_sameRegionAs_spec:
  "\<forall>capa capb. \<Gamma> \<turnstile> \<lbrace>  ccap_relation (ArchObjectCap capa) \<acute>cap_a \<and>
                 ccap_relation (ArchObjectCap capb) \<acute>cap_b  \<rbrace>
  Call Arch_sameRegionAs_'proc
  \<lbrace>  \<acute>ret__unsigned_long = from_bool (Arch.sameRegionAs capa capb) \<rbrace>"
  apply vcg
  apply clarsimp

  apply (simp add: ARM_H.sameRegionAs_def)
  subgoal for capa capb cap_b cap_a  
  apply (cases capa; simp add: cap_get_tag_isCap_unfolded_H_cap isCap_simps)

  -- "capa is ASIDPoolCap"
      apply (cases capb; simp add: cap_get_tag_isCap_unfolded_H_cap 
                         isCap_simps cap_tag_defs from_bool_def false_def)
      -- "capb is also ASIDPoolCap"
       apply (frule cap_get_tag_isCap_unfolded_H_cap(13)[where cap'=cap_a])
       apply (frule cap_get_tag_isCap_unfolded_H_cap(13)[where cap'=cap_b])
       apply (frule cap_get_tag_isCap_unfolded_H_cap)
       apply (simp add: ccap_relation_def  map_option_case)
       apply (simp add: cap_asid_pool_cap_lift)
       apply (simp add: cap_to_H_def)
       apply (cases "capASIDPool_CL (cap_asid_pool_cap_lift cap_a) = 
                        capASIDPool_CL (cap_asid_pool_cap_lift cap_b)"; simp)

      -- "capb is ASIDControlCap"
      subgoal for \<dots> vmpage_size option
      apply clarsimp
      apply (cases "vmpage_size=ARMSmallPage")
       apply (frule cap_get_tag_isCap_unfolded_H_cap(16)[where cap'=cap_b], 
              assumption, simp add: cap_tag_defs)
      apply (frule cap_get_tag_isCap_unfolded_H_cap(17)[where cap'=cap_b], 
             assumption, simp add: cap_tag_defs)
      done
     
  -- "capa is ASIDControlCap"
     apply (cases capb; simp add: cap_get_tag_isCap_unfolded_H_cap 
                        isCap_simps cap_tag_defs from_bool_def false_def true_def)
     -- " capb is PageCap"
     subgoal for \<dots> vmpage_size option
     apply (case_tac "vmpage_size=ARMSmallPage")
      apply (frule_tac cap'=cap_b in cap_get_tag_isCap_unfolded_H_cap(16), 
             assumption, simp add: cap_tag_defs)
     apply (frule_tac cap'=cap_b in cap_get_tag_isCap_unfolded_H_cap(17), 
             assumption, simp add: cap_tag_defs)
     done

  -- "capa is PageCap"
    subgoal for \<dots> vmpage_size option
    apply (cases "vmpage_size=ARMSmallPage")
    -- "capa is a small frame"
     apply (frule cap_get_tag_isCap_unfolded_H_cap(16)[where cap' = cap_a], assumption)
     apply (cases capb; simp add: cap_get_tag_isCap_unfolded_H_cap 
                        isCap_simps cap_tag_defs from_bool_def false_def true_def)
   -- " capb is PageCap"

     subgoal for \<dots> vmpage_sizea optiona
     apply (cases "vmpage_sizea=ARMSmallPage")
      -- "capb is a small frame"
      apply (frule cap_get_tag_isCap_unfolded_H_cap(16)[where cap'=cap_b], 
             assumption, simp add: cap_tag_defs)
      apply (intro conjI)
          apply (simp add:Kernel_C.ARMSmallPage_def)
         apply (simp add: gen_framesize_to_H_def)
        apply (simp add:Kernel_C.ARMSmallPage_def)
       apply (simp add: gen_framesize_to_H_def)
      
      apply (simp add: Let_def) 
      apply (clarsimp simp: if_distrib [where f="scast"])
      apply (simp add: cap_get_tag_PageCap_small_frame [unfolded cap_tag_defs, simplified])
      apply (thin_tac "ccap_relation x cap_b" for x)
      apply (frule_tac cap'=cap_a in cap_get_tag_isCap_unfolded_H_cap(16)[simplified], simp)
      apply (simp add: cap_get_tag_PageCap_small_frame) 
      apply (thin_tac "ccap_relation x cap_a" for x)
      apply clarsimp
  
      apply (simp add: if_0_1_eq)
      apply (simp add: Kernel_C.ARMSmallPage_def gen_framesize_to_H_def)
      apply (simp add: field_simps)

     -- "capb is a frame"
     apply (frule_tac cap'=cap_b in cap_get_tag_isCap_unfolded_H_cap(17), 
            assumption, simp add: cap_tag_defs)
     apply (intro conjI)
         apply (simp add:Kernel_C.ARMSmallPage_def)
        apply (simp add: gen_framesize_to_H_def)
       subgoal by (simp add:cap_frame_cap_lift_def cap_lift_def cap_tag_defs mask_def word_bw_assocs)
      apply (simp add: pageBitsForSize_def)
      apply (cases "gen_framesize_to_H (capFSize_CL (cap_frame_cap_lift cap_b))"; simp)


      apply (subgoal_tac "capFSize_CL (cap_frame_cap_lift cap_b) \<noteq> scast Kernel_C.ARMSmallPage")
       prefer 2
       apply (drule ccap_relation_c_valid_cap[where c'= cap_b])
       apply (simp add: cap_frame_cap_lift [unfolded cap_tag_defs, simplified])
       apply (simp add: c_valid_cap_def cl_valid_cap_def)

     apply (simp add: Let_def) 
     apply (clarsimp simp: if_distrib [where f=scast])
     apply (simp add: cap_get_tag_PageCap_frame [unfolded cap_tag_defs, simplified]) 
     apply (thin_tac "ccap_relation x cap_b" for x)
     apply (frule cap_get_tag_isCap_unfolded_H_cap(16)[simplified, where cap'=cap_a], simp)
     apply (simp add: cap_get_tag_PageCap_small_frame) 
     apply (thin_tac "ccap_relation x cap_a" for x)
     apply clarsimp
  
     apply (simp add: if_0_1_eq)
     apply (cut_tac x="(pageBitsForSize (gen_framesize_to_H (capFSize_CL (cap_frame_cap_lift cap_b))))" 
              in unat_of_nat32)
      apply (simp add: pageBitsForSize_def)
      apply (case_tac "gen_framesize_to_H (capFSize_CL (cap_frame_cap_lift cap_b))", simp_all add: word_bits_def)[1]
     apply clarsimp
     apply (thin_tac "unat x = y" for x y)

     apply (simp add: gen_framesize_to_H_is_framesize_to_H_if_not_ARMSmallPage)
     apply (simp add: Kernel_C.ARMSmallPage_def gen_framesize_to_H_def)
     by (simp add: field_simps)

    -- "capa is a frame"
    apply (frule cap_get_tag_isCap_unfolded_H_cap(17)[where cap' = cap_a], assumption)
    apply (subgoal_tac "capFSize_CL (cap_frame_cap_lift cap_a) && mask 2 = capFSize_CL (cap_frame_cap_lift cap_a)")
     prefer 2 subgoal by (simp add:cap_frame_cap_lift_def cap_lift_def cap_tag_defs mask_def word_bw_assocs)

     apply (frule_tac cap'=cap_a in cap_get_tag_isCap_unfolded_H_cap(17)[simplified], simp)

      apply (subgoal_tac "capFSize_CL (cap_frame_cap_lift cap_a) \<noteq> scast Kernel_C.ARMSmallPage")
       prefer 2
       apply (drule_tac c'=cap_a in ccap_relation_c_valid_cap)
       apply (simp add: cap_frame_cap_lift)
       apply (simp add: c_valid_cap_def cl_valid_cap_def)
  
    apply (cases capb; simp add: cap_get_tag_isCap_unfolded_H_cap 
                       isCap_simps cap_tag_defs from_bool_def false_def true_def)
    -- " capb is PageCap"
    subgoal for \<dots> vmpage_sizea optiona
  
    apply (cases "vmpage_sizea=ARMSmallPage")
     -- "capb is a small frame"
     apply (frule cap_get_tag_isCap_unfolded_H_cap(16)[where cap'=cap_b], 
            assumption, simp add: cap_tag_defs)
     apply (simp add: Let_def)

     apply (intro conjI)
        apply (simp add: pageBitsForSize_def)
        apply (cases "gen_framesize_to_H (capFSize_CL (cap_frame_cap_lift cap_a))"; simp)
       apply (simp add: mask_def Kernel_C.ARMSmallPage_def)
      apply (simp add: Kernel_C.ARMSmallPage_def gen_framesize_to_H_def)

     apply (frule cap_get_tag_isCap_unfolded_H_cap(17)[simplified, where cap'=cap_a], simp)
     apply (simp add: cap_tag_defs)
     apply (simp add: cap_get_tag_PageCap_small_frame [unfolded cap_tag_defs, simplified]) 
     apply (simp add: cap_get_tag_PageCap_frame [unfolded cap_tag_defs, simplified]) 
     apply (clarsimp simp: if_distrib [where f=scast])
     apply (thin_tac "ccap_relation x y" for x y)+
     
     apply (simp add: if_0_1_eq)

     apply (cut_tac x="(pageBitsForSize (gen_framesize_to_H (capFSize_CL (cap_frame_cap_lift cap_a))))" 
              in unat_of_nat32)
      apply (simp add: pageBitsForSize_def)
      apply (cases "gen_framesize_to_H (capFSize_CL (cap_frame_cap_lift cap_a))"; simp add: word_bits_def)
     apply clarsimp
     apply (thin_tac "unat x = y" for x y)

     apply (simp add: gen_framesize_to_H_is_framesize_to_H_if_not_ARMSmallPage)
     apply (simp add: Kernel_C.ARMSmallPage_def gen_framesize_to_H_def)
     apply (simp add: field_simps)

    -- "capb is a frame"
    apply (frule cap_get_tag_isCap_unfolded_H_cap(17)[where cap'=cap_b], 
           assumption, simp add: cap_tag_defs)

    apply (subgoal_tac "capFSize_CL (cap_frame_cap_lift cap_b) \<noteq> scast Kernel_C.ARMSmallPage")
     prefer 2
     apply (drule ccap_relation_c_valid_cap [unfolded cap_tag_defs, where c'=cap_b])
     apply (simp add: cap_frame_cap_lift [unfolded cap_tag_defs, simplified])
     apply (simp add: c_valid_cap_def cl_valid_cap_def)


    apply (frule cap_get_tag_isCap_unfolded_H_cap(17)[simplified, where cap'=cap_a], simp)
    apply (simp add: cap_tag_defs)
    apply (drule (1) iffD1 [OF cap_get_tag_PageCap_frame [unfolded cap_tag_defs, simplified]])+
    apply clarify

    apply (intro conjI)
        apply (simp add: pageBitsForSize_def)
        apply (cases "gen_framesize_to_H (capFSize_CL (cap_frame_cap_lift cap_a))"; simp)
       subgoal by (simp add:cap_frame_cap_lift_def cap_lift_def cap_tag_defs mask_def word_bw_assocs)
      apply (simp add: pageBitsForSize_def)
      apply (case_tac "gen_framesize_to_H (capFSize_CL (cap_frame_cap_lift cap_b))"; simp)
    apply (simp add: Let_def) 
    apply (simp add: if_0_1_eq if_distrib [where f=scast])


    apply (cut_tac x="(pageBitsForSize (gen_framesize_to_H (capFSize_CL (cap_frame_cap_lift cap_a))))" 
             in unat_of_nat32)
     apply (simp add: pageBitsForSize_def)
     apply (cases "gen_framesize_to_H (capFSize_CL (cap_frame_cap_lift cap_a))"; simp add: word_bits_def)
    apply clarsimp
    apply (cut_tac x="(pageBitsForSize (gen_framesize_to_H (capFSize_CL (cap_frame_cap_lift cap_b))))" 
             in unat_of_nat32)
     apply (simp add: pageBitsForSize_def)
     apply (cases "gen_framesize_to_H (capFSize_CL (cap_frame_cap_lift cap_b))"; simp add: word_bits_def)
    apply clarsimp

    apply (simp add: gen_framesize_to_H_is_framesize_to_H_if_not_ARMSmallPage)
    by (simp add: field_simps)
   done

  -- "capa is PageTableCap"
   apply (cases capb; simp_all add: cap_get_tag_isCap_unfolded_H_cap 
                      isCap_simps cap_tag_defs from_bool_def false_def true_def)
    -- " capb is PageCap"
    subgoal for \<dots> vmpage_size option
    apply (cases "vmpage_size=ARMSmallPage")
     apply (frule cap_get_tag_isCap_unfolded_H_cap(16)[where cap'=cap_b],   
                      assumption, simp add: cap_tag_defs)
    by (frule cap_get_tag_isCap_unfolded_H_cap(17)[where cap'=cap_b], 
            assumption, simp add: cap_tag_defs)
   -- " capb is a PageTableCap"
   subgoal
   apply (frule_tac cap'=cap_a in cap_get_tag_isCap_unfolded_H_cap(14))
   apply (frule_tac cap'=cap_b in cap_get_tag_isCap_unfolded_H_cap(14))
   apply (frule cap_get_tag_isCap_unfolded_H_cap)
   apply (simp add: ccap_relation_def  map_option_case)
   apply (simp add: cap_page_table_cap_lift)
   apply (simp add: cap_to_H_def)
   by (cases "capPTBasePtr_CL (cap_page_table_cap_lift cap_a) = 
                    capPTBasePtr_CL (cap_page_table_cap_lift cap_b)"; simp)

  -- "capa is PageDirectoryCap"
  apply (cases capb; simp add: cap_get_tag_isCap_unfolded_H_cap 
                      isCap_simps cap_tag_defs from_bool_def false_def true_def)
   -- " capb is PageCap"
   subgoal for \<dots> vmpage_size option
   apply (cases "vmpage_size=ARMSmallPage")
    apply (frule cap_get_tag_isCap_unfolded_H_cap(16)[where cap'=cap_b], 
            assumption, simp add: cap_tag_defs)
   by (frule cap_get_tag_isCap_unfolded_H_cap(17)[where cap'=cap_b], 
           assumption, simp add: cap_tag_defs)
  -- " capb is a PageDirectoryCap"
  subgoal
  apply (frule_tac cap'=cap_a in cap_get_tag_isCap_unfolded_H_cap(15))
  apply (frule_tac cap'=cap_b in cap_get_tag_isCap_unfolded_H_cap(15))
  apply (frule cap_get_tag_isCap_unfolded_H_cap)
  apply (simp add: ccap_relation_def  map_option_case)
  apply (simp add: cap_page_directory_cap_lift)
  apply (simp add: cap_to_H_def)
  by (cases "capPDBasePtr_CL (cap_page_directory_cap_lift cap_a) = 
                   capPDBasePtr_CL (cap_page_directory_cap_lift cap_b)"; simp)
  done
done

definition
  generic_frame_cap_get_capFSize_CL :: "cap_CL option \<Rightarrow> word32" where
  "generic_frame_cap_get_capFSize_CL \<equiv> \<lambda>cap. case cap of
      Some (Cap_small_frame_cap c) \<Rightarrow> scast Kernel_C.ARMSmallPage
    | Some (Cap_frame_cap c) \<Rightarrow> cap_frame_cap_CL.capFSize_CL c
    | Some _ \<Rightarrow> 0"

lemma generic_frame_cap_get_capFSize_spec:
  "\<forall>s. \<Gamma> \<turnstile> \<lbrace>s. cap_get_tag \<acute>cap = scast cap_small_frame_cap \<or>
                cap_get_tag \<acute>cap = scast cap_frame_cap\<rbrace>
       \<acute>ret__unsigned_long :== PROC generic_frame_cap_get_capFSize(\<acute>cap)
       \<lbrace>\<acute>ret__unsigned_long = generic_frame_cap_get_capFSize_CL (cap_lift \<^bsup>s\<^esup>cap)\<rbrace>"
  apply vcg
  apply (clarsimp simp: generic_frame_cap_get_capFSize_CL_def)
  apply (intro conjI impI)
    apply (clarsimp simp: cap_lift_small_frame_cap cap_small_frame_cap_lift_def)
   apply (clarsimp simp: cap_lift_frame_cap cap_frame_cap_lift_def)
  apply (clarsimp simp: cap_lifts [THEN sym])
  done

definition
  generic_frame_cap_get_capFBasePtr_CL :: "cap_CL option \<Rightarrow> word32" where
  "generic_frame_cap_get_capFBasePtr_CL \<equiv> \<lambda>cap. case cap of
      Some (Cap_small_frame_cap c) \<Rightarrow> cap_small_frame_cap_CL.capFBasePtr_CL c
    | Some (Cap_frame_cap c) \<Rightarrow> cap_frame_cap_CL.capFBasePtr_CL c
    | Some _ \<Rightarrow> 0"

lemma generic_frame_cap_get_capFBasePtr_spec:
  "\<forall>s. \<Gamma> \<turnstile> \<lbrace>s. cap_get_tag \<acute>cap = scast cap_small_frame_cap \<or>
                cap_get_tag \<acute>cap = scast cap_frame_cap\<rbrace>
       \<acute>ret__unsigned_long :== PROC generic_frame_cap_get_capFBasePtr(\<acute>cap)
       \<lbrace>\<acute>ret__unsigned_long = generic_frame_cap_get_capFBasePtr_CL (cap_lift \<^bsup>s\<^esup>cap)\<rbrace>"
  apply vcg
  apply (clarsimp simp: generic_frame_cap_get_capFBasePtr_CL_def)
  apply (intro conjI impI)
    apply (clarsimp simp: cap_lift_small_frame_cap cap_small_frame_cap_lift_def)
   apply (clarsimp simp: cap_lift_frame_cap cap_frame_cap_lift_def)
  apply (clarsimp simp: cap_lifts [THEN sym])
  done
  
definition
  "generic_frame_cap_get_capFIsDevice_CL \<equiv> \<lambda>cap. case cap of
      Some (Cap_small_frame_cap c) \<Rightarrow> cap_small_frame_cap_CL.capFIsDevice_CL c
    | Some (Cap_frame_cap c) \<Rightarrow> cap_frame_cap_CL.capFIsDevice_CL c
    | Some _ \<Rightarrow> 0 | None \<Rightarrow> 0"
    
lemma generic_frame_cap_get_capFIsDevice_spec:
  "\<forall>s. \<Gamma> \<turnstile> \<lbrace>s. cap_get_tag \<acute>cap = scast cap_small_frame_cap \<or>
                cap_get_tag \<acute>cap = scast cap_frame_cap\<rbrace>
       \<acute>ret__unsigned_long :== PROC generic_frame_cap_get_capFIsDevice(\<acute>cap)
       \<lbrace>\<acute>ret__unsigned_long = generic_frame_cap_get_capFIsDevice_CL (cap_lift \<^bsup>s\<^esup>cap)\<rbrace>"
  apply (rule allI, rule conseqPre, vcg)
  apply (clarsimp simp: generic_frame_cap_get_capFIsDevice_CL_def)
  apply (intro conjI impI)
    apply (clarsimp simp: cap_lift_small_frame_cap cap_small_frame_cap_lift_def)
   apply (clarsimp simp: cap_lift_frame_cap cap_frame_cap_lift_def)
  apply (clarsimp simp: cap_lifts [THEN sym])
  by (clarsimp simp: generic_frame_cap_get_capFIsDevice_CL_def
                        cap_lift_small_frame_cap cap_lift_frame_cap
                        cap_small_frame_cap_lift_def cap_frame_cap_lift_def)
  
definition
 "generic_frame_cap_get_capFVMRights_CL \<equiv> \<lambda>cap. case cap of
      Some (Cap_small_frame_cap c) \<Rightarrow> cap_small_frame_cap_CL.capFVMRights_CL c
    | Some (Cap_frame_cap c) \<Rightarrow> cap_frame_cap_CL.capFVMRights_CL c
    | Some _ \<Rightarrow> 0 | None \<Rightarrow> 0"

lemma generic_frame_cap_get_capFVMRights_spec:
  "\<forall>s. \<Gamma> \<turnstile> {s} Call generic_frame_cap_get_capFVMRights_'proc
     {t. ret__unsigned_long_' t = generic_frame_cap_get_capFVMRights_CL (cap_lift (cap_' s))}"
  apply (rule allI, rule conseqPre, vcg)
  apply (clarsimp simp: generic_frame_cap_get_capFVMRights_CL_def
                        cap_lift_small_frame_cap cap_lift_frame_cap
                        cap_small_frame_cap_lift_def cap_frame_cap_lift_def)
  by (simp add: cap_lift_def Let_def Kernel_C.VMNoAccess_def split: if_split)

definition
  get_capSizeBits_CL :: "cap_CL option \<Rightarrow> nat" where
  "get_capSizeBits_CL \<equiv> \<lambda>cap. case cap of
      Some (Cap_untyped_cap c) \<Rightarrow> unat (cap_untyped_cap_CL.capBlockSize_CL c)
    | Some (Cap_endpoint_cap c) \<Rightarrow> 4
    | Some (Cap_notification_cap c) \<Rightarrow> 4
    | Some (Cap_cnode_cap c) \<Rightarrow> unat (capCNodeRadix_CL c) + 4
    | Some (Cap_thread_cap c) \<Rightarrow> 9
    | Some (Cap_small_frame_cap c) \<Rightarrow> 12
    | Some (Cap_frame_cap c) \<Rightarrow> pageBitsForSize (gen_framesize_to_H $ generic_frame_cap_get_capFSize_CL cap)
    | Some (Cap_page_table_cap c) \<Rightarrow> 10
    | Some (Cap_page_directory_cap c) \<Rightarrow> 14
    | Some (Cap_asid_pool_cap c) \<Rightarrow> asidLowBits + 2
    | Some (Cap_zombie_cap c) \<Rightarrow>
        let type = cap_zombie_cap_CL.capZombieType_CL c in
        if isZombieTCB_C type then 9 else unat (type && mask 5) + 4
    | _ \<Rightarrow> 0"

lemma frame_cap_size [simp]:
  "cap_get_tag cap = scast cap_frame_cap
  \<Longrightarrow> cap_frame_cap_CL.capFSize_CL (cap_frame_cap_lift cap) && mask 2 =
     cap_frame_cap_CL.capFSize_CL (cap_frame_cap_lift cap)"
  apply (simp add: cap_frame_cap_lift_def)
  by (simp add: cap_lift_def cap_tag_defs mask_def word_bw_assocs)

lemma generic_frame_cap_size[simp]:
  "cap_get_tag cap = scast cap_frame_cap \<or> cap_get_tag cap = scast cap_small_frame_cap
  \<Longrightarrow> generic_frame_cap_get_capFSize_CL (cap_lift cap) && mask 2 =
     generic_frame_cap_get_capFSize_CL (cap_lift cap)"
  apply (simp add: generic_frame_cap_get_capFSize_CL_def)
  apply (erule disjE)
   subgoal by (simp add: cap_lift_def cap_tag_defs mask_def word_bw_assocs)
  by (simp add: cap_lift_def cap_tag_defs mask_def Kernel_C.ARMSmallPage_def)
 
lemma cap_get_capSizeBits_spec:
  "\<forall>s. \<Gamma> \<turnstile> {s}
       \<acute>ret__unsigned_long :== PROC cap_get_capSizeBits(\<acute>cap)
       \<lbrace>\<acute>ret__unsigned_long = of_nat (get_capSizeBits_CL (cap_lift \<^bsup>s\<^esup>cap))\<rbrace>"
  apply vcg
  apply (clarsimp simp: get_capSizeBits_CL_def)
  apply (intro conjI impI)
                        apply (clarsimp simp: cap_lifts gen_framesize_to_H_def
                                              generic_frame_cap_get_capFSize_CL_def
                                              cap_lift_asid_control_cap
                                              cap_lift_irq_control_cap cap_lift_null_cap
                                              Kernel_C.asidLowBits_def asid_low_bits_def
                                              word_sle_def Let_def mask_def
                                              isZombieTCB_C_def ZombieTCB_C_def
                                              cap_lift_domain_cap
                                       dest!: sym [where t = "cap_get_tag cap" for cap])+
  (* slow *)
  by (case_tac "cap_lift cap", simp_all, case_tac "a",
               auto simp: cap_lift_def cap_tag_defs Let_def
                  cap_small_frame_cap_lift_def cap_frame_cap_lift_def
                  cap_endpoint_cap_lift_def cap_notification_cap_lift_def
                  cap_cnode_cap_lift_def cap_thread_cap_lift_def
                  cap_zombie_cap_lift_def cap_page_table_cap_lift_def
                  cap_page_directory_cap_lift_def cap_asid_pool_cap_lift_def
                  Let_def cap_untyped_cap_lift_def  split: if_split_asm)

lemma ccap_relation_get_capSizeBits_physical:
  notes unfolds = ccap_relation_def get_capSizeBits_CL_def cap_lift_def
                  cap_tag_defs cap_to_H_def objBits_def objBitsKO_simps
                  Let_def field_simps mask_def asid_low_bits_def ARM_H.capUntypedSize_def
  shows
  "\<lbrakk> ccap_relation hcap ccap; capClass hcap = PhysicalClass;
            capAligned hcap \<rbrakk> \<Longrightarrow>
   2 ^ get_capSizeBits_CL (cap_lift ccap) = capUntypedSize hcap"
  apply (case_tac hcap, simp_all)
        defer 4 (* zombie caps second last *)
        defer 4 (* arch caps last *)
        apply ((frule cap_get_tag_isCap_unfolded_H_cap,
                     clarsimp simp: unfolds
                             split: if_split_asm)+)[5] (* SOMEONE FIX SUBGOAL PLZ *)
   apply (frule cap_get_tag_isCap_unfolded_H_cap)
   apply (clarsimp simp: unfolds split: if_split_asm)
   apply (rule arg_cong [OF less_mask_eq[where n=5, unfolded mask_def, simplified]])
   apply (simp add: capAligned_def objBits_simps word_bits_conv word_less_nat_alt)
  subgoal for arch_capability
  apply (cases arch_capability; simp)
     defer 2 (* page caps last *)
     apply (fold_subgoals (prefix))[3]
     subgoal premises prems by ((frule cap_get_tag_isCap_unfolded_H_cap,
               clarsimp simp: unfolds
                       split: if_split_asm)+)
  apply (rename_tac vmpage_size option)
  apply (case_tac "vmpage_size = ARMSmallPage", simp_all)
   apply (frule cap_get_tag_isCap_unfolded_H_cap(16), simp)
   subgoal by (clarsimp simp: unfolds split: if_split_asm)
  by (frule cap_get_tag_isCap_unfolded_H_cap(17), simp,
         clarsimp simp: unfolds
                        pageBitsForSize_spec gen_framesize_to_H_def
                        c_valid_cap_def cl_valid_cap_def framesize_to_H_def
                        generic_frame_cap_get_capFSize_CL_def
                 split: if_split_asm)+
  done

lemma ccap_relation_get_capSizeBits_untyped:
  "\<lbrakk> ccap_relation (UntypedCap d word bits idx) ccap \<rbrakk> \<Longrightarrow>
   get_capSizeBits_CL (cap_lift ccap) = bits"
  apply (frule cap_get_tag_isCap_unfolded_H_cap)
  by (clarsimp simp: get_capSizeBits_CL_def ccap_relation_def
                        map_option_case cap_to_H_def cap_lift_def cap_tag_defs)

definition
  get_capZombieBits_CL :: "cap_zombie_cap_CL \<Rightarrow> word32" where
  "get_capZombieBits_CL \<equiv> \<lambda>cap.
      let type = cap_zombie_cap_CL.capZombieType_CL cap in
      if isZombieTCB_C type then 4 else type && mask 5"

lemma get_capSizeBits_valid_shift:
  "\<lbrakk> ccap_relation hcap ccap; capAligned hcap \<rbrakk> \<Longrightarrow>
   get_capSizeBits_CL (cap_lift ccap) < 32"
  unfolding get_capSizeBits_CL_def
  apply (cases hcap;
         simp add: cap_get_tag_isCap_unfolded_H_cap cap_lift_def cap_tag_defs)
     (* zombie *)
     apply (clarsimp simp: Let_def split: if_split)
     apply (frule cap_get_tag_isCap_unfolded_H_cap)
     apply (clarsimp simp: ccap_relation_def map_option_Some_eq2
                           cap_lift_zombie_cap cap_to_H_def
                           Let_def capAligned_def objBits_simps
                           word_bits_conv)
     apply (subst less_mask_eq, simp add: word_less_nat_alt, assumption)
    (* arch *)
    apply (rename_tac arch_capability)
    apply (case_tac arch_capability,
           simp_all add: cap_get_tag_isCap_unfolded_H_cap cap_lift_def
                         cap_tag_defs asid_low_bits_def)
    apply (rename_tac vmpage_size option)
    apply (case_tac vmpage_size,
           simp_all add: cap_get_tag_isCap_unfolded_H_cap cap_lift_def
                         cap_tag_defs pageBitsForSize_def)
      apply (clarsimp split: vmpage_size.split)+
   (* untyped *)
   apply (frule cap_get_tag_isCap_unfolded_H_cap)
   apply (clarsimp simp: cap_lift_def cap_tag_defs)
   apply (subgoal_tac "index (cap_C.words_C ccap) 1 && 0x1F \<le> 0x1F")
    apply (simp add: unat_arith_simps)
   apply (simp add: word_and_le1)
  (* cnode *)
  apply (frule cap_get_tag_isCap_unfolded_H_cap)
  apply (clarsimp simp: ccap_relation_def map_option_Some_eq2
                        cap_lift_cnode_cap cap_to_H_def
                        Let_def capAligned_def objBits_simps
                        word_bits_conv)
  done

lemma get_capSizeBits_valid_shift_word:
  "\<lbrakk> ccap_relation hcap ccap; capAligned hcap \<rbrakk> \<Longrightarrow>
   of_nat (get_capSizeBits_CL (cap_lift ccap)) < (0x20::word32)"
  apply (subgoal_tac "of_nat (get_capSizeBits_CL (cap_lift ccap)) < (of_nat 32::word32)", simp)
  apply (rule of_nat_mono_maybe, simp+)
  apply (simp add: get_capSizeBits_valid_shift)
  done

lemma cap_zombie_cap_get_capZombieBits_spec:
  "\<forall>s. \<Gamma> \<turnstile> \<lbrace>s. cap_get_tag \<acute>cap = scast cap_zombie_cap \<rbrace>
       \<acute>ret__unsigned_long :== PROC cap_zombie_cap_get_capZombieBits(\<acute>cap)
       \<lbrace>\<acute>ret__unsigned_long = get_capZombieBits_CL (cap_zombie_cap_lift \<^bsup>s\<^esup>cap)\<rbrace>"
  apply vcg
  apply (clarsimp simp: get_capZombieBits_CL_def word_sle_def mask_def
                        isZombieTCB_C_def ZombieTCB_C_def Let_def)
  done

definition
  get_capZombiePtr_CL :: "cap_zombie_cap_CL \<Rightarrow> word32" where
  "get_capZombiePtr_CL \<equiv> \<lambda>cap.
      let radix = unat (get_capZombieBits_CL cap) in
      cap_zombie_cap_CL.capZombieID_CL cap && ~~ (mask (radix+1))"

lemma cap_zombie_cap_get_capZombiePtr_spec:
  "\<forall>s. \<Gamma> \<turnstile> \<lbrace>s. cap_get_tag \<acute>cap = scast cap_zombie_cap
                \<and> get_capZombieBits_CL (cap_zombie_cap_lift \<acute>cap) < 0x1F \<rbrace>
       \<acute>ret__unsigned_long :== PROC cap_zombie_cap_get_capZombiePtr(\<acute>cap)
       \<lbrace>\<acute>ret__unsigned_long = get_capZombiePtr_CL (cap_zombie_cap_lift \<^bsup>s\<^esup>cap)\<rbrace>"
  apply vcg
  apply (clarsimp simp: get_capZombiePtr_CL_def word_sle_def mask_def
                        isZombieTCB_C_def ZombieTCB_C_def Let_def)
  apply (intro conjI)
   apply (simp add: word_add_less_mono1[where k=1 and j="0x1F", simplified])
  apply (subst unat_plus_if_size)
  apply (clarsimp split: if_split)
  apply (clarsimp simp: get_capZombieBits_CL_def Let_def word_size
                 split: if_split if_split_asm)
  apply (subgoal_tac "unat (capZombieType_CL (cap_zombie_cap_lift cap) && mask 5)
                      < unat ((2::word32) ^ 5)")
   apply clarsimp
  apply (rule unat_mono)
  apply (rule and_mask_less_size)
  apply (clarsimp simp: word_size)
  done

definition
  get_capPtr_CL :: "cap_CL option \<Rightarrow> unit ptr" where
  "get_capPtr_CL \<equiv> \<lambda>cap. Ptr (case cap of
      Some (Cap_untyped_cap c) \<Rightarrow> cap_untyped_cap_CL.capPtr_CL c
    | Some (Cap_endpoint_cap c) \<Rightarrow> cap_endpoint_cap_CL.capEPPtr_CL c
    | Some (Cap_notification_cap c) \<Rightarrow> cap_notification_cap_CL.capNtfnPtr_CL c
    | Some (Cap_cnode_cap c) \<Rightarrow> cap_cnode_cap_CL.capCNodePtr_CL c
    | Some (Cap_thread_cap c) \<Rightarrow> (cap_thread_cap_CL.capTCBPtr_CL c && ~~ mask (objBits (undefined :: tcb)))
    | Some (Cap_small_frame_cap c) \<Rightarrow> cap_small_frame_cap_CL.capFBasePtr_CL c
    | Some (Cap_frame_cap c) \<Rightarrow> cap_frame_cap_CL.capFBasePtr_CL c
    | Some (Cap_page_table_cap c) \<Rightarrow> cap_page_table_cap_CL.capPTBasePtr_CL c
    | Some (Cap_page_directory_cap c) \<Rightarrow> cap_page_directory_cap_CL.capPDBasePtr_CL c
    | Some (Cap_asid_pool_cap c) \<Rightarrow> cap_asid_pool_cap_CL.capASIDPool_CL c
    | Some (Cap_zombie_cap c) \<Rightarrow> get_capZombiePtr_CL c
    | _ \<Rightarrow> 0)"

lemma cap_get_capPtr_spec: 
  "\<forall>s. \<Gamma> \<turnstile> \<lbrace>s. (cap_get_tag \<acute>cap = scast cap_zombie_cap
                   \<longrightarrow> get_capZombieBits_CL (cap_zombie_cap_lift \<acute>cap) < 0x1F)\<rbrace>
       \<acute>ret__ptr_to_void :== PROC cap_get_capPtr(\<acute>cap)
       \<lbrace>\<acute>ret__ptr_to_void = get_capPtr_CL (cap_lift \<^bsup>s\<^esup>cap)\<rbrace>"
  apply vcg
  apply (clarsimp simp: get_capPtr_CL_def generic_frame_cap_get_capFBasePtr_CL_def)
  apply (intro impI conjI)
                    apply (clarsimp simp: cap_lifts pageBitsForSize_def 
                                          cap_lift_asid_control_cap word_sle_def
                                          cap_lift_irq_control_cap cap_lift_null_cap
                                          mask_def objBits_simps cap_lift_domain_cap
                                          ptr_add_assertion_positive
                                   dest!: sym [where t = "cap_get_tag cap" for cap]
                                   split: vmpage_size.splits)+
  (* XXX: slow. there should be a rule for this *)
  by (case_tac "cap_lift cap", simp_all, case_tac "a",
               auto simp: cap_lift_def cap_tag_defs Let_def
                  cap_small_frame_cap_lift_def cap_frame_cap_lift_def
                  cap_endpoint_cap_lift_def cap_notification_cap_lift_def
                  cap_cnode_cap_lift_def cap_thread_cap_lift_def
                  cap_zombie_cap_lift_def cap_page_table_cap_lift_def
                  cap_page_directory_cap_lift_def cap_asid_pool_cap_lift_def
                  Let_def cap_untyped_cap_lift_def  split: if_split_asm)

definition get_capIsPhysical_CL :: "cap_CL option \<Rightarrow> bool"
where
  "get_capIsPhysical_CL \<equiv> \<lambda>cap. (case cap of
  Some (Cap_untyped_cap c) \<Rightarrow> True
    | Some (Cap_endpoint_cap c) \<Rightarrow> True
    | Some (Cap_notification_cap c) \<Rightarrow> True
    | Some (Cap_cnode_cap c) \<Rightarrow> True
    | Some (Cap_thread_cap c) \<Rightarrow> True
    | Some (Cap_small_frame_cap c) \<Rightarrow> True
    | Some (Cap_frame_cap c) \<Rightarrow> True
    | Some (Cap_page_table_cap c) \<Rightarrow> True
    | Some (Cap_page_directory_cap c) \<Rightarrow> True
    | Some (Cap_asid_pool_cap c) \<Rightarrow> True
    | Some (Cap_zombie_cap c) \<Rightarrow> True
    | _ \<Rightarrow> False)"
    
lemma cap_get_capIsPhysical_spec:
  "\<forall>s. \<Gamma> \<turnstile> {s}
       Call cap_get_capIsPhysical_'proc
       \<lbrace>\<acute>ret__unsigned_long = from_bool (get_capIsPhysical_CL (cap_lift \<^bsup>s\<^esup>cap))\<rbrace>"
  apply vcg
  apply (clarsimp simp: get_capIsPhysical_CL_def)
  apply (intro impI conjI)
                    apply (clarsimp simp: cap_lifts pageBitsForSize_def 
                                          cap_lift_asid_control_cap word_sle_def
                                          cap_lift_irq_control_cap cap_lift_null_cap
                                          mask_def objBits_simps cap_lift_domain_cap
                                          ptr_add_assertion_positive from_bool_def
                                          true_def false_def
                                   dest!: sym [where t = "cap_get_tag cap" for cap]
                                   split: vmpage_size.splits)+
  (* XXX: slow. there should be a rule for this *)
  by (case_tac "cap_lift cap", simp_all, case_tac a, auto simp: cap_lift_def cap_tag_defs Let_def
                  cap_small_frame_cap_lift_def cap_frame_cap_lift_def
                  cap_endpoint_cap_lift_def cap_notification_cap_lift_def
                  cap_cnode_cap_lift_def cap_thread_cap_lift_def
                  cap_zombie_cap_lift_def cap_page_table_cap_lift_def
                  cap_page_directory_cap_lift_def cap_asid_pool_cap_lift_def
                  Let_def cap_untyped_cap_lift_def  split: if_split_asm)

lemma ccap_relation_get_capPtr_not_physical:
  "\<lbrakk> ccap_relation hcap ccap; capClass hcap \<noteq> PhysicalClass \<rbrakk> \<Longrightarrow>
   get_capPtr_CL (cap_lift ccap) = Ptr 0"
  by (clarsimp simp: ccap_relation_def get_capPtr_CL_def cap_to_H_def Let_def
              split: option.split cap_CL.split_asm if_split_asm)
  
lemma ccap_relation_get_capIsPhysical:
  "ccap_relation hcap ccap \<Longrightarrow> isPhysicalCap hcap = get_capIsPhysical_CL (cap_lift ccap)"
  apply (case_tac hcap; clarsimp simp: cap_lifts cap_lift_domain_cap cap_lift_null_cap 
                                       cap_lift_irq_control_cap cap_to_H_def 
                                       get_capIsPhysical_CL_def 
                       dest!: cap_get_tag_isCap_unfolded_H_cap)
  apply (rename_tac arch_cap)
  apply (case_tac arch_cap; clarsimp simp: cap_lifts cap_lift_asid_control_cap                                        
                      dest!: cap_get_tag_isCap_unfolded_H_cap)
  apply (rename_tac p R sz asid)
  apply (case_tac sz)
  apply (drule (1) cap_get_tag_isCap_unfolded_H_cap(16), clarsimp simp: cap_lifts)
  apply (drule cap_get_tag_isCap_unfolded_H_cap(17), simp, clarsimp simp: cap_lifts)+
  done

lemma ctcb_ptr_to_tcb_ptr_mask':
  "is_aligned (ctcb_ptr_to_tcb_ptr (tcb_Ptr x)) (objBits (undefined :: tcb)) \<Longrightarrow>
     ctcb_ptr_to_tcb_ptr (tcb_Ptr x) = x && ~~ mask (objBits (undefined :: tcb))"
  apply (simp add: ctcb_ptr_to_tcb_ptr_def)
  apply (drule_tac d=ctcb_offset in is_aligned_add_helper)
   apply (simp add: objBits_simps ctcb_offset_def)
  apply simp
  done

lemmas ctcb_ptr_to_tcb_ptr_mask
    = ctcb_ptr_to_tcb_ptr_mask'[simplified objBits_simps, simplified]

lemma ccap_relation_get_capPtr_physical:
  notes unfolds = ccap_relation_def get_capPtr_CL_def cap_lift_def
                  cap_tag_defs cap_to_H_def get_capZombiePtr_CL_def
                  get_capZombieBits_CL_def Let_def objBits_simps
                  capAligned_def
  shows
  "\<lbrakk> ccap_relation hcap ccap; capClass hcap = PhysicalClass; capAligned hcap \<rbrakk> \<Longrightarrow>
     get_capPtr_CL (cap_lift ccap)
        = Ptr (capUntypedPtr hcap)"
  apply (cases hcap; simp add: isCap_simps)
        defer 4
        defer 4
        apply ((frule cap_get_tag_isCap_unfolded_H_cap,
                    clarsimp simp: unfolds
                    split: if_split_asm dest!: ctcb_ptr_to_tcb_ptr_mask)+)[5]
   apply (frule cap_get_tag_isCap_unfolded_H_cap)
   apply (clarsimp simp: unfolds split: if_split_asm dest!: ctcb_ptr_to_tcb_ptr_mask)
   apply (rule arg_cong [OF less_mask_eq])
   apply (simp add: capAligned_def word_bits_conv objBits_simps
                    word_less_nat_alt)
  subgoal for arch_capability
  apply (cases arch_capability; simp)
     defer 2 (* page caps last *)
     apply (fold_subgoals (prefix))[3]
     subgoal by ((frule cap_get_tag_isCap_unfolded_H_cap,
                  clarsimp simp: unfolds split: if_split_asm)+)
  defer
   subgoal for \<dots> vmpage_size option
   apply (cases "vmpage_size = ARMSmallPage"; simp?)
    apply (frule cap_get_tag_isCap_unfolded_H_cap(16), simp)
    subgoal by (clarsimp simp: unfolds split: if_split_asm)
   by (frule cap_get_tag_isCap_unfolded_H_cap(17), simp,
          clarsimp simp: unfolds
                         cap_tag_defs cap_to_H_def
                  split: if_split_asm)+
  done
  done

lemma ccap_relation_get_capPtr_untyped:
  "\<lbrakk> ccap_relation (UntypedCap d word bits idx) ccap \<rbrakk> \<Longrightarrow>
   get_capPtr_CL (cap_lift ccap) = Ptr word"
  apply (frule cap_get_tag_isCap_unfolded_H_cap)
  by (clarsimp simp: get_capPtr_CL_def ccap_relation_def
                        map_option_case cap_to_H_def cap_lift_def cap_tag_defs)

lemma cap_get_tag_isArchCap_unfolded_H_cap:
  "ccap_relation (capability.ArchObjectCap a_cap) cap' \<Longrightarrow>
   (isArchCap_tag (cap_get_tag cap'))"
  apply (frule cap_get_tag_isCap(11), simp) 
  done

lemma ucast_ucast_mask_eq:
  "\<lbrakk> (ucast :: ('a :: len) word \<Rightarrow> ('b :: len) word) x = y;
        x && mask (len_of TYPE('b)) = x \<rbrakk>
    \<Longrightarrow> x = ucast y"
  apply (drule_tac f="ucast :: 'b word \<Rightarrow> 'a word" in arg_cong)
  apply (simp add: ucast_ucast_mask)
  done

lemma ucast_up_eq:
  "\<lbrakk> ucast x = (ucast y::'b::len word); 
    len_of TYPE('a) \<le> len_of TYPE ('b) \<rbrakk>
  \<Longrightarrow> ucast x = (ucast y::'a::len word)"
  apply (subst (asm) bang_eq)
  apply (fastforce simp: nth_ucast word_size intro: word_eqI)
  done

lemma ucast_up_neq:
  "\<lbrakk> ucast x \<noteq> (ucast y::'b::len word); 
    len_of TYPE('b) \<le> len_of TYPE ('a) \<rbrakk>
  \<Longrightarrow> ucast x \<noteq> (ucast y::'a::len word)"
  apply (clarsimp)
  apply (drule ucast_up_eq)
    apply simp+
  done

lemma sameRegionAs_spec:
  "\<forall>capa capb. \<Gamma> \<turnstile> \<lbrace>ccap_relation capa \<acute>cap_a \<and>
                     ccap_relation capb \<acute>cap_b \<and>
                     capAligned capb \<and> (\<exists>s. s \<turnstile>' capa)\<rbrace>
  Call sameRegionAs_'proc
  \<lbrace> \<acute>ret__unsigned_long = from_bool (sameRegionAs capa capb) \<rbrace>"
  apply vcg
  apply clarsimp
  apply (simp add: sameRegionAs_def isArchCap_tag_def2)
  apply (case_tac capa, simp_all add: cap_get_tag_isCap_unfolded_H_cap isCap_simps)
            -- "capa is a ThreadCap"
             apply (case_tac capb, simp_all add: cap_get_tag_isCap_unfolded_H_cap 
                          isCap_simps cap_tag_defs from_bool_def false_def)[1]
              apply (frule_tac cap'=cap_a in cap_get_tag_isCap_unfolded_H_cap(1))
              apply (frule_tac cap'=cap_b in cap_get_tag_isCap_unfolded_H_cap(1))
              apply (simp add: ccap_relation_def map_option_case)
              apply (simp add: cap_thread_cap_lift)
              apply (simp add: cap_to_H_def)
             apply (clarsimp simp: case_bool_If ctcb_ptr_to_tcb_ptr_def if_distrib
                              cong: if_cong)
             apply (frule_tac cap'=cap_b in cap_get_tag_isArchCap_unfolded_H_cap)
             apply (clarsimp simp: isArchCap_tag_def2)
           -- "capa is a NullCap"
            apply (simp add: cap_tag_defs from_bool_def false_def)
          -- "capa is an NotificationCap"
           apply (case_tac capb, simp_all add: cap_get_tag_isCap_unfolded_H_cap 
                        isCap_simps cap_tag_defs from_bool_def false_def)[1]
            apply (frule_tac cap'=cap_a in cap_get_tag_isCap_unfolded_H_cap(3))
            apply (frule_tac cap'=cap_b in cap_get_tag_isCap_unfolded_H_cap(3))
            apply (simp add: ccap_relation_def map_option_case)
            apply (simp add: cap_notification_cap_lift)
            apply (simp add: cap_to_H_def)
            apply (clarsimp split: if_split)
           apply (frule_tac cap'=cap_b in cap_get_tag_isArchCap_unfolded_H_cap)
           apply (clarsimp simp: isArchCap_tag_def2)
          -- "capa is an IRQHandlerCap"
          apply (case_tac capb, simp_all add: cap_get_tag_isCap_unfolded_H_cap 
                      isCap_simps cap_tag_defs from_bool_def false_def)[1]
           apply (frule_tac cap'=cap_a in cap_get_tag_isCap_unfolded_H_cap(5))
           apply (frule_tac cap'=cap_b in cap_get_tag_isCap_unfolded_H_cap(5))
           apply (simp add: ccap_relation_def map_option_case)
           apply (simp add: cap_irq_handler_cap_lift)
           apply (simp add: cap_to_H_def)
           apply (clarsimp simp: up_ucast_inj_eq c_valid_cap_def
                                 cl_valid_cap_def mask_twice
                          split: if_split bool.split
                          | intro impI conjI
                          | simp )+
               apply (drule ucast_ucast_mask_eq, simp)
               apply (simp add: ucast_ucast_mask)
              apply (erule ucast_up_neq,simp)
          apply (frule_tac cap'=cap_b in cap_get_tag_isArchCap_unfolded_H_cap)
          apply (clarsimp simp: isArchCap_tag_def2)
         -- "capa is an EndpointCap"
         apply (case_tac capb, simp_all add: cap_get_tag_isCap_unfolded_H_cap 
                      isCap_simps cap_tag_defs from_bool_def false_def)[1]
          apply (frule_tac cap'=cap_a in cap_get_tag_isCap_unfolded_H_cap(4))
          apply (frule_tac cap'=cap_b in cap_get_tag_isCap_unfolded_H_cap(4))
          apply (simp add: ccap_relation_def map_option_case)
          apply (simp add: cap_endpoint_cap_lift)
          apply (simp add: cap_to_H_def)
          apply (clarsimp split: if_split)
         apply (frule_tac cap'=cap_b in cap_get_tag_isArchCap_unfolded_H_cap)
         apply (clarsimp simp: isArchCap_tag_def2)
        -- "capa is a DomainCap"
        apply (case_tac capb, simp_all add: cap_get_tag_isCap_unfolded_H_cap
                     isCap_simps cap_tag_defs from_bool_def false_def true_def)[1]
        apply (frule_tac cap'=cap_b in cap_get_tag_isArchCap_unfolded_H_cap)
        apply (fastforce simp: isArchCap_tag_def2 split: if_split)
       -- "capa is a Zombie"
       apply (simp add: cap_tag_defs from_bool_def false_def)
      -- "capa is an Arch object cap"
      apply (frule_tac cap'=cap_a in cap_get_tag_isArchCap_unfolded_H_cap)
      apply (clarsimp simp: isArchCap_tag_def2 cap_tag_defs linorder_not_less [THEN sym])
      apply (rule conjI, clarsimp, rule impI)+
      apply (case_tac capb, simp_all add: cap_get_tag_isCap_unfolded_H_cap
                   isCap_simps cap_tag_defs from_bool_def false_def)[1]
      -- "capb is an Arch object cap"
      apply (frule_tac cap'=cap_b in cap_get_tag_isArchCap_unfolded_H_cap)
      apply (fastforce simp: isArchCap_tag_def2 cap_tag_defs linorder_not_less [THEN sym])
     -- "capa is a ReplyCap"
     apply (case_tac capb, simp_all add: cap_get_tag_isCap_unfolded_H_cap 
                  isCap_simps cap_tag_defs from_bool_def false_def)[1]
      apply (frule_tac cap'=cap_b in cap_get_tag_isArchCap_unfolded_H_cap)
      apply (clarsimp simp: isArchCap_tag_def2)     
     apply (frule_tac cap'=cap_a in cap_get_tag_isCap_unfolded_H_cap(8))
     apply (frule_tac cap'=cap_b in cap_get_tag_isCap_unfolded_H_cap(8))
     apply (simp add: ccap_relation_def map_option_case)
     apply (simp add: cap_reply_cap_lift)
     apply (simp add: cap_to_H_def ctcb_ptr_to_tcb_ptr_def)
     apply (clarsimp split: if_split)
    -- "capa is an UntypedCap"
    apply (frule_tac cap'=cap_a in cap_get_tag_isCap_unfolded_H_cap(9))
    apply (intro conjI)
     apply (rule impI, intro conjI)
        apply (rule impI, drule(1) cap_get_tag_to_H)+
        apply (clarsimp simp: capAligned_def word_bits_conv
                              objBits_simps get_capZombieBits_CL_def
                              Let_def word_less_nat_alt
                              less_mask_eq true_def
                       split: if_split_asm)
       apply (subgoal_tac "capBlockSize_CL (cap_untyped_cap_lift cap_a) \<le> 0x1F")
        apply (simp add: word_le_make_less)
       apply (simp add: cap_untyped_cap_lift_def cap_lift_def
                        cap_tag_defs word_and_le1)
      apply (clarsimp simp: get_capSizeBits_valid_shift_word)
     apply (clarsimp simp: from_bool_def Let_def split: if_split bool.splits)
     apply (subst unat_of_nat32,
              clarsimp simp: unat_of_nat32 word_bits_def
                      dest!: get_capSizeBits_valid_shift)+
     apply (clarsimp simp: ccap_relation_get_capPtr_physical
                           ccap_relation_get_capPtr_untyped
                           ccap_relation_get_capIsPhysical[symmetric]
                           ccap_relation_get_capSizeBits_physical
                           ccap_relation_get_capSizeBits_untyped)
     apply (intro conjI impI)
        apply ((clarsimp simp: ccap_relation_def map_option_case
                               cap_untyped_cap_lift cap_to_H_def
                               field_simps valid_cap'_def)+)[4]
    apply (rule impI, simp add: from_bool_0 ccap_relation_get_capIsPhysical[symmetric])
    apply (simp add: from_bool_def false_def)
   -- "capa is a CNodeCap"
   apply (case_tac capb, simp_all add: cap_get_tag_isCap_unfolded_H_cap 
                isCap_simps cap_tag_defs from_bool_def false_def)[1]
    apply (frule_tac cap'=cap_b in cap_get_tag_isArchCap_unfolded_H_cap)
    apply (clarsimp simp: isArchCap_tag_def2)     
   apply (frule_tac cap'=cap_a in cap_get_tag_isCap_unfolded_H_cap(10))
   apply (frule_tac cap'=cap_b in cap_get_tag_isCap_unfolded_H_cap(10))
   apply (simp add: ccap_relation_def map_option_case)
   apply (simp add: cap_cnode_cap_lift)
   apply (simp add: cap_to_H_def)
   apply (clarsimp split: if_split bool.split)
  -- "capa is an IRQControlCap"
  apply (case_tac capb, simp_all add: cap_get_tag_isCap_unfolded_H_cap 
               isCap_simps cap_tag_defs from_bool_def false_def true_def)[1]
  apply (frule_tac cap'=cap_b in cap_get_tag_isArchCap_unfolded_H_cap)
  apply (fastforce simp: isArchCap_tag_def2 split: if_split)
  done

lemma gen_framesize_to_H_eq:
  "\<lbrakk> a \<le> 3; b \<le> 3 \<rbrakk> \<Longrightarrow>
   (gen_framesize_to_H a = gen_framesize_to_H b) = (a = b)"
  by (fastforce simp: gen_framesize_to_H_def Kernel_C.ARMSmallPage_def
                     Kernel_C.ARMLargePage_def Kernel_C.ARMSection_def
                     word_le_make_less
              split: if_split
               dest: word_less_cases)

lemma framesize_to_H_eq:
  "\<lbrakk> a \<le> 3; b \<le> 3; a \<noteq> 0; b \<noteq> 0 \<rbrakk> \<Longrightarrow>
   (framesize_to_H a = framesize_to_H b) = (a = b)"
  by (fastforce simp: framesize_to_H_def Kernel_C.ARMSmallPage_def
                     Kernel_C.ARMLargePage_def Kernel_C.ARMSection_def
                     word_le_make_less
              split: if_split
               dest: word_less_cases)

lemma capFSize_range:
  "\<And>cap. cap_get_tag cap = scast cap_frame_cap \<Longrightarrow>
   capFSize_CL (cap_frame_cap_lift cap) \<le> 3"
  apply (simp add: cap_frame_cap_lift_def)
  apply (simp add: cap_lift_def cap_tag_defs word_and_le1)
  done

lemma Arch_sameObjectAs_spec:
  "\<forall>capa capb. \<Gamma> \<turnstile> \<lbrace>ccap_relation (ArchObjectCap capa) \<acute>cap_a \<and>
                     ccap_relation (ArchObjectCap capb) \<acute>cap_b \<and>
                     capAligned (ArchObjectCap capa) \<and>
                     capAligned (ArchObjectCap capb) \<rbrace>
  Call Arch_sameObjectAs_'proc
  \<lbrace> \<acute>ret__unsigned_long = from_bool (Arch.sameObjectAs capa capb) \<rbrace>"
  apply vcg
  apply (clarsimp simp: ARM_H.sameObjectAs_def)
  apply (case_tac capa, simp_all add: cap_get_tag_isCap_unfolded_H_cap
                                      isCap_defs cap_tag_defs)
      apply fastforce+
    apply (case_tac capb, simp_all add: cap_get_tag_isCap_unfolded_H_cap
                                        isCap_defs cap_tag_defs)
        apply fastforce+
      apply (rename_tac vmpage_size opt d w r vmpage_sizea opt')
      apply (case_tac "vmpage_size = ARMSmallPage",
             simp_all add: cap_get_tag_isCap_unfolded_H_cap cap_tag_defs)[1]
       apply (rename_tac vmpage_sizea optiona)
       apply (case_tac "vmpage_sizea = ARMSmallPage",
              simp_all add: cap_get_tag_isCap_unfolded_H_cap cap_tag_defs
                            false_def from_bool_def)[1]
       apply (frule_tac cap'=cap_a in cap_get_tag_isCap_unfolded_H_cap(16), simp)
       apply (frule_tac cap'=cap_b in cap_get_tag_isCap_unfolded_H_cap(16), simp)
       apply (simp add: ccap_relation_def map_option_case)
       apply (simp add: cap_small_frame_cap_lift)
       apply (clarsimp simp: cap_to_H_def capAligned_def to_bool_def from_bool_def 
                      split: if_split bool.split
                      dest!: is_aligned_no_overflow)
      apply (case_tac "vmpage_sizea = ARMSmallPage",
             simp_all add: cap_get_tag_isCap_unfolded_H_cap cap_tag_defs
                           false_def from_bool_def)[1]
      apply (frule_tac cap'=cap_a in cap_get_tag_isCap_unfolded_H_cap(17), simp)
      apply (frule_tac cap'=cap_b in cap_get_tag_isCap_unfolded_H_cap(17), simp)
      apply (simp add: ccap_relation_def map_option_case)
      apply (simp add: cap_frame_cap_lift)
      apply (clarsimp simp: cap_to_H_def capAligned_def from_bool_def
                            c_valid_cap_def cl_valid_cap_def
                            Kernel_C.ARMSmallPage_def
                     split: if_split bool.split vmpage_size.split_asm
                     dest!: is_aligned_no_overflow)
      apply (simp add: framesize_to_H_eq capFSize_range to_bool_def
                       cap_frame_cap_lift [symmetric])
     apply fastforce+
  done

lemma sameObjectAs_spec:
  "\<forall>capa capb. \<Gamma> \<turnstile> \<lbrace>ccap_relation capa \<acute>cap_a \<and>
                     ccap_relation capb \<acute>cap_b \<and>
                     capAligned capa \<and> capAligned capb \<and> (\<exists>s. s \<turnstile>' capa)\<rbrace>
  Call sameObjectAs_'proc
  \<lbrace> \<acute>ret__unsigned_long = from_bool (sameObjectAs capa capb) \<rbrace>"
  apply vcg
  apply (clarsimp simp: sameObjectAs_def isArchCap_tag_def2)
  apply (case_tac capa, simp_all add: cap_get_tag_isCap_unfolded_H_cap
                                      isCap_simps cap_tag_defs
                                      from_bool_def false_def)
            apply fastforce+
     -- "capa is an arch cap"
     apply (frule cap_get_tag_isArchCap_unfolded_H_cap)
     apply (simp add: isArchCap_tag_def2)
     apply (simp add: if_1_0_0)
     apply (rule conjI, rule impI, clarsimp, rule impI)+
     apply (case_tac capb, simp_all add: cap_get_tag_isCap_unfolded_H_cap
                                         isCap_simps cap_tag_defs)[1]
                apply ((fastforce)+)[7]
         -- "capb is an arch cap"
         apply (frule_tac cap'=cap_b in cap_get_tag_isArchCap_unfolded_H_cap)
         apply (fastforce simp: isArchCap_tag_def2 linorder_not_less [symmetric])+
  -- "capa is an irq handler cap"
  apply (case_tac capb, simp_all add: cap_get_tag_isCap_unfolded_H_cap
                                      isCap_simps cap_tag_defs if_1_0_0)
           apply fastforce+
      -- "capb is an arch cap"
      apply (frule cap_get_tag_isArchCap_unfolded_H_cap)
      apply (fastforce simp: isArchCap_tag_def2)+
  done

lemma sameRegionAs_EndpointCap:
  shows "\<lbrakk>ccap_relation capa capc;
          RetypeDecls_H.sameRegionAs (capability.EndpointCap x y z  u v) capa\<rbrakk>
         \<Longrightarrow> cap_get_tag capc = scast cap_endpoint_cap"
  apply (simp add: sameRegionAs_def Let_def)
  apply (case_tac capa;
         simp add: isUntypedCap_def isEndpointCap_def isNotificationCap_def
             isCNodeCap_def isThreadCap_def isReplyCap_def isIRQControlCap_def
             isIRQHandlerCap_def isArchObjectCap_def)
  apply (clarsimp simp: ccap_relation_def map_option_case)
  apply (case_tac "cap_lift capc"; simp)
  apply (simp add: cap_to_H_def)
  apply (case_tac a; simp)
   apply (simp add:cap_endpoint_cap_lift cap_endpoint_cap_lift_def)
  apply (rename_tac zombie_cap)
  apply (case_tac "isZombieTCB_C (capZombieType_CL zombie_cap)"; simp add: Let_def)
  done

lemma sameRegionAs_NotificationCap:
  shows "\<lbrakk>ccap_relation capa capc;
          RetypeDecls_H.sameRegionAs
            (capability.NotificationCap x y z  u ) capa\<rbrakk>
         \<Longrightarrow> cap_get_tag capc = scast cap_notification_cap"
  apply (simp add: sameRegionAs_def  Let_def)
  apply (case_tac capa;
         simp add: isUntypedCap_def isEndpointCap_def isNotificationCap_def
             isCNodeCap_def isThreadCap_def isReplyCap_def isIRQControlCap_def
             isIRQHandlerCap_def isArchObjectCap_def)
  apply (clarsimp simp: ccap_relation_def map_option_case)
  apply (case_tac "cap_lift capc"; simp)
  apply (simp add: cap_to_H_def)
  apply (case_tac a; simp)
   apply (simp add: cap_notification_cap_lift cap_notification_cap_lift_def)
  apply (rename_tac zombie_cap)
  apply (case_tac "isZombieTCB_C (capZombieType_CL zombie_cap)"; simp add: Let_def)
  done

lemma isMDBParentOf_spec:
  notes option.case_cong_weak [cong]
  shows "\<forall>ctea cte_a cteb cte_b.
   \<Gamma> \<turnstile> {s. cslift s (cte_a_' s) = Some cte_a \<and>
            ccte_relation ctea cte_a \<and>
            cslift s (cte_b_' s) = Some cte_b \<and>
            ccte_relation cteb cte_b \<and>
            capAligned (cteCap cteb) \<and>
            (\<exists>s. s \<turnstile>' (cteCap ctea)) }
   Call isMDBParentOf_'proc
   \<lbrace> \<acute>ret__unsigned_long = from_bool (isMDBParentOf ctea cteb) \<rbrace>"
  apply (intro allI, rule conseqPre)
   apply vcg
  apply (clarsimp simp: isMDBParentOf_def)

  apply (frule_tac cte=ctea in ccte_relation_ccap_relation)
  apply (frule_tac cte=cteb in ccte_relation_ccap_relation)

  apply (rule conjI, clarsimp simp: typ_heap_simps dest!: lift_t_g)
  apply (intro conjI impI)
     apply (simp add: ccte_relation_def map_option_case)
     apply (simp add: cte_lift_def)
     apply (clarsimp simp: cte_to_H_def mdb_node_to_H_def split: option.split_asm)
     apply (clarsimp simp: Let_def false_def from_bool_def to_bool_def
                    split: if_split bool.splits)
     apply ((clarsimp simp: typ_heap_simps dest!: lift_t_g)+)[3]
  apply (rule_tac x="cteCap ctea" in exI, rule conjI)
   apply (clarsimp simp: ccte_relation_ccap_relation typ_heap_simps
                  dest!: lift_t_g)
  apply (rule_tac x="cteCap cteb" in exI, rule conjI)
   apply (clarsimp simp: ccte_relation_ccap_relation typ_heap_simps
                  dest!: lift_t_g)
  apply (clarsimp simp: ccte_relation_def map_option_case)
  apply (simp add: cte_lift_def)
  apply (clarsimp simp: cte_to_H_def mdb_node_to_H_def
                 split: option.split_asm)

  apply (rule conjI, fastforce) -- "Ex (valid_cap' (cteCap ctea))"

  apply (rule impI, rule conjI)
   -- "sameRegionAs = 0"
   apply (rule impI)
   apply (clarsimp simp: from_bool_def false_def
                  split: if_split bool.splits)

  -- "sameRegionAs \<noteq> 0"
  apply (clarsimp simp: from_bool_def false_def)
  apply (case_tac "RetypeDecls_H.sameRegionAs (cap_to_H x2b) (cap_to_H x2c)")
   prefer 2 apply clarsimp
  apply (clarsimp cong:bool.case_cong if_cong simp: typ_heap_simps)

  apply (rule conjI)
    --" cap_get_tag of cte_a is an endpoint"
   apply clarsimp
   apply (frule cap_get_tag_EndpointCap)
   apply simp
   apply (clarsimp simp: to_bool_def isNotificationCap_def isEndpointCap_def true_def) -- "badge of A is not 0 now"


   apply (subgoal_tac "cap_get_tag (cte_C.cap_C cte_b) = scast cap_endpoint_cap") --"needed also after"
    prefer 2
    apply (rule sameRegionAs_EndpointCap, assumption+)

   apply (clarsimp simp: if_1_0_0 typ_heap_simps'   Let_def case_bool_If)
   apply (frule_tac cap="(cap_to_H x2c)" in cap_get_tag_EndpointCap)
   apply (clarsimp split: if_split_asm simp: if_distrib [where f=scast])

  apply (clarsimp, rule conjI)
  --" cap_get_tag of cte_a is an notification"
   apply clarsimp
   apply (frule cap_get_tag_NotificationCap)
   apply simp
   apply (clarsimp simp: to_bool_def isNotificationCap_def isEndpointCap_def true_def) -- "badge of A is not 0 now"


   apply (subgoal_tac "cap_get_tag (cte_C.cap_C cte_b) = scast cap_notification_cap") --"needed also after"
    prefer 2
    apply (rule sameRegionAs_NotificationCap, assumption+)

   apply (rule conjI, simp)
   apply clarsimp
   apply (simp add: Let_def case_bool_If)
   apply (frule_tac cap="(cap_to_H x2c)" in cap_get_tag_NotificationCap)
   apply (simp add: if_1_0_0 if_distrib [where f=scast])

  -- " main goal"
  apply clarsimp
  apply (simp add: to_bool_def)
  apply (subgoal_tac "(\<not> (isEndpointCap (cap_to_H x2b))) \<and> ( \<not> (isNotificationCap (cap_to_H x2b)))")
   apply (clarsimp simp: true_def)
  apply (rule conjI)
   apply (clarsimp simp: cap_get_tag_isCap [symmetric])+
done


lemma updateCapData_spec:
  "\<forall>cap. \<Gamma> \<turnstile> \<lbrace> ccap_relation cap \<acute>cap \<and> preserve = to_bool (\<acute>preserve) \<and> newData = \<acute>newData\<rbrace>
  Call updateCapData_'proc
  \<lbrace>  ccap_relation (updateCapData preserve newData cap) \<acute>ret__struct_cap_C \<rbrace>"
  apply (rule allI, rule conseqPre)
  apply vcg
  apply (clarsimp simp: if_1_0_0)

  apply (simp add: updateCapData_def)

  apply (case_tac cap, simp_all add: cap_get_tag_isCap_unfolded_H_cap 
                        isCap_simps from_bool_def isArchCap_tag_def2 cap_tag_defs Let_def)
  -- "NotificationCap"
     apply clarsimp
     apply (frule cap_get_tag_isCap_unfolded_H_cap(3))
     apply (frule (1) iffD1[OF cap_get_tag_NotificationCap])
     apply clarsimp

     apply (intro conjI impI)
     -- "preserve is zero and capNtfnBadge_CL \<dots> = 0"
       apply clarsimp 
       apply (clarsimp simp:cap_notification_cap_lift_def cap_lift_def cap_tag_defs)
       apply (simp add: ccap_relation_def cap_lift_def cap_tag_defs cap_to_H_def)
     -- "preserve is zero and capNtfnBadge_CL \<dots> \<noteq> 0"
      apply clarsimp 
      apply (simp add: ccap_relation_NullCap_iff cap_tag_defs)
     -- "preserve is not zero"
     apply clarsimp
     apply (simp add: to_bool_def)
     apply (case_tac "preserve_' x = 0 \<and> capNtfnBadge_CL (cap_notification_cap_lift (cap_' x))= 0", 
            clarsimp)
     apply (simp add: if_not_P) 
     apply (simp add: ccap_relation_NullCap_iff cap_tag_defs)

  -- "EndpointCap"
    apply clarsimp
    apply (frule cap_get_tag_isCap_unfolded_H_cap(4))
    apply (frule (1) iffD1[OF cap_get_tag_EndpointCap])
    apply clarsimp

    apply (intro impI conjI)
    -- "preserve is zero and capNtfnBadge_CL \<dots> = 0"
      apply clarsimp
      apply (clarsimp simp:cap_endpoint_cap_lift_def cap_lift_def cap_tag_defs)
      apply (simp add: ccap_relation_def cap_lift_def cap_tag_defs cap_to_H_def)
    -- "preserve is zero and capNtfnBadge_CL \<dots> \<noteq> 0"
     apply clarsimp 
     apply (simp add: ccap_relation_NullCap_iff cap_tag_defs)
    -- "preserve is not zero"
    apply clarsimp
    apply (simp add: to_bool_def)
    apply (case_tac "preserve_' x = 0 \<and> capEPBadge_CL (cap_endpoint_cap_lift (cap_' x))= 0", clarsimp)
    apply (simp add: if_not_P) 
    apply (simp add: ccap_relation_NullCap_iff cap_tag_defs)

  -- "ArchObjectCap"
   apply clarsimp
   apply (frule cap_get_tag_isArchCap_unfolded_H_cap)
   apply (simp add: isArchCap_tag_def2)
   apply (simp add: ARM_H.updateCapData_def) 

  -- "CNodeCap"
  apply clarsimp
  apply (frule cap_get_tag_isCap_unfolded_H_cap(10))
  apply (frule (1) iffD1[OF cap_get_tag_CNodeCap])
  apply clarsimp

  apply (thin_tac "ccap_relation x y" for x y)
  apply (thin_tac "ret__unsigned_long_' t = v" for t v)+

  apply (simp add: cnode_capdata_lift_def fupdate_def word_size word_less_nat_alt mask_def
             cong: if_cong)
  apply (simp only: unat_word_ariths(1))
  apply (rule ssubst [OF nat_mod_eq' [where n = "2 ^ len_of TYPE(32)"]])
   -- " unat (\<dots> && 0x1F) +  unat (\<dots> mod 0x20) < 2 ^ len_of TYPE(32)"
   apply (rule order_le_less_trans, rule add_le_mono)
     apply (rule word_le_nat_alt[THEN iffD1])
     apply (rule word_and_le1)
    apply (simp add: cap_cnode_cap_lift_def cap_lift_cnode_cap)
    apply (rule word_le_nat_alt[THEN iffD1])
    apply (rule word_and_le1)
   apply simp

  apply (simp add: word_sle_def)
  apply (rule conjI, clarsimp simp:  ccap_relation_NullCap_iff cap_tag_defs)
  apply clarsimp
  apply (rule conjI)
   apply (rule unat_less_power[where sz=5, simplified], simp add: word_bits_def)
   apply (rule and_mask_less'[where n=5, unfolded mask_def, simplified], simp)

  apply clarsimp
  apply (simp add: ccap_relation_def c_valid_cap_def cl_valid_cap_def
                   cap_lift_cnode_cap cap_tag_defs cap_to_H_simps
                   cap_cnode_cap_lift_def)
  apply (simp add: word_bw_assocs word_bw_comms word_bw_lcs)
  done


abbreviation
  "deriveCap_xf \<equiv> liftxf errstate deriveCap_ret_C.status_C deriveCap_ret_C.cap_C ret__struct_deriveCap_ret_C_'"


lemma ensureNoChildren_ccorres:
  "ccorres (syscall_error_rel \<currency> dc) (liftxf errstate id undefined ret__unsigned_long_')
   (\<lambda>s. valid_objs' s \<and> valid_mdb' s) (UNIV \<inter> \<lbrace>slot = ptr_val (\<acute>slot)\<rbrace>) []
   (ensureNoChildren slot) (Call ensureNoChildren_'proc)"
   apply (cinit lift: slot_')
   apply (rule ccorres_liftE_Seq)
   apply (rule ccorres_getCTE)
   apply (rule ccorres_move_c_guard_cte)

   apply (rule_tac P= "\<lambda> s. valid_objs' s \<and> valid_mdb' s \<and> ctes_of s (ptr_val slota) = Some cte" 
               and P' =UNIV in ccorres_from_vcg_throws)
   apply (rule allI, rule conseqPre, vcg)
   apply clarsimp

   apply (frule (1) rf_sr_ctes_of_clift, clarsimp)
   apply (simp add: typ_heap_simps)


   apply (clarsimp simp: whenE_def throwError_def return_def nullPointer_def liftE_bindE)

   apply (clarsimp simp: returnOk_def return_def) -- "solve the case where mdbNext is zero"

   -- "main goal"
   apply (simp add: ccte_relation_def)
   apply (frule_tac cte="cte_to_H y" in valid_mdb_ctes_of_next, simp+)
   apply (clarsimp simp: cte_wp_at_ctes_of)
   apply (frule_tac cte=cte in rf_sr_ctes_of_clift, assumption, clarsimp)
   apply (rule conjI) 
    apply (frule_tac cte="(cte_to_H ya)" in ctes_of_valid', assumption, simp)
    apply (rule valid_capAligned, assumption)       
   apply (rule conjI)
    apply (frule_tac cte="(cte_to_H y)" in ctes_of_valid', assumption, simp)
    apply blast

   apply clarsimp
   apply (rule conjI)
   -- "isMDBParentOf is not zero"
    apply clarsimp
    apply (simp add: from_bool_def)
    apply (case_tac "isMDBParentOf (cte_to_H y) (cte_to_H ya)", simp_all)[1]

    apply (simp add: bind_def)
    apply (simp add: split_paired_Bex)
    apply (clarsimp simp: in_getCTE_cte_wp_at')
    apply (simp add: cte_wp_at_ctes_of)
    apply (simp add: syscall_error_rel_def EXCEPTION_NONE_def EXCEPTION_SYSCALL_ERROR_def)
    apply (simp add: syscall_error_to_H_cases(9))
   -- "isMDBParentOf is zero"
   apply clarsimp
   apply (simp add: from_bool_def)
   apply (case_tac "isMDBParentOf (cte_to_H y) (cte_to_H ya)", simp_all)[1]
   apply (simp add: bind_def)
   apply (simp add: split_paired_Bex)
   apply (clarsimp simp: in_getCTE_cte_wp_at')
   apply (simp add: cte_wp_at_ctes_of)
   apply (simp add: returnOk_def return_def) 

  -- " last goal"
  apply clarsimp
  apply (simp add: cte_wp_at_ctes_of)
done




lemma cap_small_frame_cap_set_capFMappedASID_spec:
  "\<forall>s. \<Gamma> \<turnstile> \<lbrace>s. cap_get_tag \<^bsup>s\<^esup>cap = scast cap_small_frame_cap\<rbrace>
    Call cap_small_frame_cap_set_capFMappedASID_'proc
   \<lbrace>cap_small_frame_cap_lift \<acute>ret__struct_cap_C
         = cap_small_frame_cap_lift \<^bsup>s\<^esup>cap 
               \<lparr> cap_small_frame_cap_CL.capFMappedASIDHigh_CL := (\<^bsup>s\<^esup>asid >> asidLowBits) && mask asidHighBits,
                 cap_small_frame_cap_CL.capFMappedASIDLow_CL  := \<^bsup>s\<^esup>asid && mask asidLowBits \<rparr>
        \<and> cap_get_tag \<acute>ret__struct_cap_C = scast cap_small_frame_cap\<rbrace>"
  apply vcg
  by (clarsimp simp: Kernel_C.asidLowBits_def word_sle_def
                     Kernel_C.asidHighBits_def asid_low_bits_def asid_high_bits_def mask_def)

lemma cap_frame_cap_set_capFMappedASID_spec:
  "\<forall>s. \<Gamma> \<turnstile> \<lbrace>s. cap_get_tag \<^bsup>s\<^esup>cap = scast cap_frame_cap\<rbrace>
    Call cap_frame_cap_set_capFMappedASID_'proc
   \<lbrace>cap_frame_cap_lift \<acute>ret__struct_cap_C
         = cap_frame_cap_lift \<^bsup>s\<^esup>cap 
               \<lparr> cap_frame_cap_CL.capFMappedASIDHigh_CL := (\<^bsup>s\<^esup>asid >> asidLowBits) && mask asidHighBits,
                 cap_frame_cap_CL.capFMappedASIDLow_CL  := \<^bsup>s\<^esup>asid && mask asidLowBits \<rparr>
        \<and> cap_get_tag \<acute>ret__struct_cap_C = scast cap_frame_cap\<rbrace>"
  apply vcg
  by (clarsimp simp: Kernel_C.asidLowBits_def word_sle_def
                     Kernel_C.asidHighBits_def asid_low_bits_def asid_high_bits_def mask_def)

lemma Arch_deriveCap_ccorres:
  "ccorres (syscall_error_rel \<currency> (ccap_relation \<circ> ArchObjectCap)) deriveCap_xf
  \<top> (UNIV \<inter> {s. ccap_relation (ArchObjectCap cap) (cap_' s)}) []
  (Arch.deriveCap slot cap) (Call Arch_deriveCap_'proc)"
  apply (cinit lift: cap_')
   apply csymbr
   apply (unfold ARM_H.deriveCap_def Let_def)
   apply (fold case_bool_If)
   apply wpc
    apply (clarsimp simp: cap_get_tag_isCap_ArchObject
                          ccorres_cond_iffs)
    apply (rule ccorres_from_vcg_throws[where P=\<top> and P'=UNIV])
    apply (rule allI, rule conseqPre, vcg)
    apply clarsimp
    apply (rule context_conjI)
     apply (simp add: cap_get_tag_isCap_ArchObject)
    apply (clarsimp simp: returnOk_def return_def)
    subgoal by (simp add: ccap_relation_def cap_lift_def Let_def
                          cap_tag_defs cap_to_H_def
                          cap_page_table_cap_lift_def)
   apply wpc
    apply (clarsimp simp: cap_get_tag_isCap_ArchObject
                          ccorres_cond_iffs)
    apply (rule ccorres_from_vcg_throws[where P=\<top> and P'=UNIV])
    apply (rule allI, rule conseqPre, vcg)
    apply clarsimp
    apply (rule context_conjI)
     apply (simp add: cap_get_tag_isCap_ArchObject)
    apply (clarsimp simp: throwError_def return_def
                          errstate_def syscall_error_rel_def
                          syscall_error_to_H_cases
                          exception_defs)
    subgoal by (simp add: ccap_relation_def cap_lift_def Let_def
                          cap_tag_defs cap_to_H_def to_bool_def
                          cap_page_table_cap_lift_def
                   split: if_split_asm)
   apply wpc
    apply (clarsimp simp: cap_get_tag_isCap_ArchObject
                          ccorres_cond_iffs)
    apply (rule ccorres_from_vcg_throws[where P=\<top> and P'=UNIV])
    apply (rule allI, rule conseqPre, vcg)
    apply clarsimp
    apply (rule context_conjI)
     apply (simp add: cap_get_tag_isCap_ArchObject)
    apply (clarsimp simp: returnOk_def return_def)
    subgoal by  (simp add: ccap_relation_def cap_lift_def Let_def
                          cap_tag_defs cap_to_H_def
                          cap_page_directory_cap_lift_def)
   apply wpc
    apply (clarsimp simp: cap_get_tag_isCap_ArchObject
                          ccorres_cond_iffs)
    apply (rule ccorres_from_vcg_throws[where P=\<top> and P'=UNIV])
    apply (rule allI, rule conseqPre, vcg)
    apply clarsimp
    apply (rule context_conjI)
     apply (simp add: cap_get_tag_isCap_ArchObject)
    apply (clarsimp simp: throwError_def return_def
                          errstate_def syscall_error_rel_def
                          syscall_error_to_H_cases
                          exception_defs)
    subgoal by (simp add: ccap_relation_def cap_lift_def Let_def
                          cap_tag_defs cap_to_H_def to_bool_def
                          cap_page_directory_cap_lift_def
                   split: if_split_asm)
   apply wpc
    apply (clarsimp simp: cap_get_tag_isCap_ArchObject
                          ccorres_cond_iffs)
    apply (case_tac "capVPSize cap = ARMSmallPage")
     apply (clarsimp simp: ccorres_cond_iffs)
     apply (rule ccorres_from_vcg_throws[where P=\<top> and P'=UNIV])
     apply (rule allI, rule conseqPre, vcg)
     apply clarsimp
     apply (rule context_conjI)
      apply (simp add: cap_get_tag_isCap_ArchObject)
     apply (clarsimp simp: returnOk_def return_def isCap_simps)
     subgoal by  (simp add: ccap_relation_def cap_lift_def Let_def
                            cap_tag_defs cap_to_H_def to_bool_def
                            cap_small_frame_cap_lift_def asidInvalid_def)
    apply (clarsimp simp: ccorres_cond_iffs)
    apply (rule ccorres_from_vcg_throws[where P=\<top> and P'=UNIV])
    apply (rule allI, rule conseqPre, vcg)
    apply clarsimp
    apply (rule context_conjI)
     apply (simp add: cap_get_tag_isCap_ArchObject)
    apply (clarsimp simp: returnOk_def return_def isCap_simps)
    subgoal by (simp add: ccap_relation_def cap_lift_def Let_def
                          cap_tag_defs cap_to_H_def to_bool_def
                          cap_frame_cap_lift_def asidInvalid_def c_valid_cap_def cl_valid_cap_def)
   apply (simp add: cap_get_tag_isCap_ArchObject
                    ccorres_cond_iffs)
   apply (rule ccorres_from_vcg_throws[where P=\<top> and P'=UNIV])
   apply (rule allI, rule conseqPre, vcg)
   apply (clarsimp simp: returnOk_def return_def subset_iff
                  split: bool.split)
   apply (cases cap, simp_all add: isCap_simps)[1]
  apply clarsimp
  done

lemma isArchCap_T_isArchObjectCap:
  "isArchCap \<top> = isArchObjectCap"
  by (rule ext, auto simp: isCap_simps) 

lemma deriveCap_ccorres':
  "ccorres (syscall_error_rel \<currency> ccap_relation) deriveCap_xf
  (valid_objs' and valid_mdb') (UNIV \<inter> {s. ccap_relation cap (cap_' s)} \<inter> {s. slot_' s = Ptr slot}) []
  (deriveCap slot cap) (Call deriveCap_'proc)"
  apply (cinit lift: cap_' slot_')
   apply csymbr
   apply (fold case_bool_If)
   apply wpc
    apply (clarsimp simp: cap_get_tag_isCap isCap_simps from_bool_def)
    apply csymbr
    apply (clarsimp simp: cap_get_tag_isCap)
    apply (rule ccorres_from_vcg_throws [where P=\<top> and P' = UNIV])
    apply (simp add: returnOk_def return_def ccap_relation_NullCap_iff)
    apply (rule allI, rule conseqPre)
     apply vcg
    apply clarsimp
   apply wpc
    apply (clarsimp simp: isCap_simps cap_get_tag_isCap from_bool_def)
    apply csymbr
    apply (clarsimp simp: isCap_simps cap_get_tag_isCap)
    apply (rule ccorres_from_vcg_throws[where P=\<top> and P'=UNIV])
    apply (rule allI, rule conseqPre, vcg)
    apply (clarsimp simp: returnOk_def return_def
                          ccap_relation_NullCap_iff)
   apply wpc
    apply (clarsimp simp: isCap_simps cap_get_tag_isCap from_bool_def)
    apply csymbr
    apply (clarsimp simp: isCap_simps cap_get_tag_isCap)
    apply (rule ccorres_rhs_assoc)+
    apply ctac_print_xf
    apply (rule ccorres_split_nothrow_call_novcgE
                   [where xf'="deriveCap_ret_C.status_C o ret___struct_deriveCap_ret_C_'"])
           apply (rule ensureNoChildren_ccorres)
          apply simp+
       apply ceqv
      apply simp
      apply (rule_tac P'="\<lbrace>deriveCap_ret_C.status_C \<acute>ret___struct_deriveCap_ret_C
                              = scast EXCEPTION_NONE\<rbrace>"
                 in ccorres_from_vcg_throws[where P=\<top>])
      apply (rule allI, rule conseqPre, vcg)
      apply (clarsimp simp: return_def returnOk_def)
     apply simp
     apply (rule_tac P'="{s. deriveCap_ret_C.status_C (ret___struct_deriveCap_ret_C_' s)
                             = rv' \<and> errstate s = err'}"
                in ccorres_from_vcg_throws[where P=\<top>])
     apply (rule allI, rule conseqPre, vcg)
     apply (clarsimp simp: throwError_def return_def
                           errstate_def)
    apply wp
   apply wpc
    apply (clarsimp simp: isCap_simps cap_get_tag_isCap from_bool_def)
    apply csymbr
    apply (clarsimp simp: isCap_simps cap_get_tag_isCap)
    apply (rule ccorres_from_vcg_throws[where P=\<top> and P'=UNIV])
    apply (rule allI, rule conseqPre, vcg)
    apply (clarsimp simp: returnOk_def return_def
                          ccap_relation_NullCap_iff)
   apply wpc
    apply (rule ccorres_split_throws[rotated])
     apply (clarsimp simp: cap_get_tag_isCap
                           liftME_def Let_def isArchCap_T_isArchObjectCap)
     apply vcg
    apply (clarsimp simp: cap_get_tag_isCap
                          liftME_def Let_def isArchCap_T_isArchObjectCap
                          ccorres_cond_univ_iff from_bool_def)
    apply (rule ccorres_split_nothrow_call_novcgE
                    [where xf'=ret__struct_deriveCap_ret_C_'])
           apply (rule Arch_deriveCap_ccorres)
          apply simp+
       apply (rule ceqv_refl)
      apply (rule_tac P'="\<lbrace>\<acute>ret__struct_deriveCap_ret_C
                              = rv'\<rbrace>"
                 in ccorres_from_vcg_throws[where P=\<top>])
      apply (rule allI, rule conseqPre, vcg)
      apply (clarsimp simp: return_def returnOk_def)
     apply (rule_tac P'="{s. (ret__struct_deriveCap_ret_C_' s)
                               = rv' \<and> errstate s = err'}"
                in ccorres_from_vcg_throws[where P=\<top>])
     apply (rule allI, rule conseqPre, vcg)
     apply (clarsimp simp: return_def throwError_def)
    apply wp
   apply (simp add: cap_get_tag_isCap isArchCap_T_isArchObjectCap from_bool_def)
   apply csymbr
   apply (simp add: cap_get_tag_isCap)
   apply (rule ccorres_from_vcg_throws[where P=\<top> and P'=UNIV])
   apply (rule allI, rule conseqPre, vcg)
   apply (clarsimp simp: return_def returnOk_def)
  apply (clarsimp simp: errstate_def isCap_simps
                        Collect_const_mem from_bool_0
                        cap_get_tag_isArchCap_unfolded_H_cap)
  done


lemma deriveCap_ccorres:
  "ccorres (syscall_error_rel \<currency> ccap_relation) deriveCap_xf
  (invs') (UNIV \<inter> {s. ccap_relation cap (cap_' s)} \<inter> {s. slot_' s = Ptr slot}) []
  (deriveCap slot cap) (Call deriveCap_'proc)"
  apply (rule ccorres_guard_imp2, rule deriveCap_ccorres')
  apply fastforce
  done




lemma ensureEmptySlot_ccorres:
  "ccorres (syscall_error_rel \<currency> dc) (liftxf errstate id undefined ret__unsigned_long_')
   \<top>  (UNIV \<inter> \<lbrace>slot = ptr_val (\<acute>slot)\<rbrace>) []
   (ensureEmptySlot slot) (Call ensureEmptySlot_'proc)"
  apply (cinit lift: slot_')
   apply (rule ccorres_liftE_Seq)
   apply (rule ccorres_getCTE)
   apply (rule ccorres_move_c_guard_cte)
   apply (rule_tac P= "\<lambda> s. ctes_of s (ptr_val slota) = Some cte" 
               and P' =UNIV in ccorres_from_vcg_throws)
   apply (rule allI, rule conseqPre, vcg)
   apply clarsimp

   apply (frule (1) rf_sr_ctes_of_clift, clarsimp)
   apply (simp add: typ_heap_simps)

   apply (rule conjI)
    apply (clarsimp simp: unlessE_def throwError_def return_def)
    apply (subgoal_tac "cap_to_H (cap_CL y) \<noteq> capability.NullCap")
     apply simp
     apply (simp add: syscall_error_rel_def EXCEPTION_NONE_def EXCEPTION_SYSCALL_ERROR_def)
     apply (rule syscall_error_to_H_cases(8))
     apply simp
    apply (subst cap_get_tag_NullCap [symmetric]) 
     prefer 2 apply assumption
    apply (simp add: ccap_relation_def c_valid_cte_def)

   apply (clarsimp simp: unlessE_def throwError_def return_def)
   apply (subgoal_tac "cap_to_H (cap_CL y) = capability.NullCap")
    apply simp
    apply (simp add: returnOk_def return_def)
   apply (subst cap_get_tag_NullCap [symmetric]) 
    prefer 2 apply assumption
   apply (simp add: ccap_relation_def c_valid_cte_def)

  apply clarsimp
  apply (simp add: cte_wp_at_ctes_of)
done



lemma (in kernel_m) updateMDB_set_mdbPrev:
 "ccorres dc xfdc 
     ( \<lambda>s. is_aligned ptr 3 \<and> (slota\<noteq>0 \<longrightarrow> is_aligned slota 3))
     {s. slotc = slota } hs
      (updateMDB ptr (mdbPrev_update (\<lambda>_. slota)))

      (IF ptr \<noteq> 0 
       THEN
          Guard C_Guard \<lbrace>hrs_htd \<acute>t_hrs \<Turnstile>\<^sub>t (Ptr ptr:: cte_C ptr)\<rbrace>
               (call (\<lambda>ta. ta(| mdb_node_ptr_' := Ptr &(Ptr ptr:: cte_C ptr
                                                          \<rightarrow>[''cteMDBNode_C'']),
                                 v_' := slotc |))
                mdb_node_ptr_set_mdbPrev_'proc (\<lambda>s t. s\<lparr> globals := globals t \<rparr>) (\<lambda>ta s'. Basic (\<lambda>a. a)))
      FI)"
  apply (rule ccorres_guard_imp2) -- "replace preconditions by schematics"
  -- "Main Goal"
  apply (rule ccorres_Cond_rhs)
    apply (rule ccorres_updateMDB_cte_at)
    apply (ctac add: ccorres_updateMDB_set_mdbPrev)
   apply (ctac ccorres: ccorres_updateMDB_skip)
  apply (simp  add: Collect_const_mem)
  done

lemma (in kernel_m) updateMDB_set_mdbNext:
 "ccorres dc xfdc 
     ( \<lambda>s. is_aligned ptr 3 \<and> (slota\<noteq>0 \<longrightarrow> is_aligned slota 3))
     {s. slotc = slota} hs 
      (updateMDB ptr (mdbNext_update (\<lambda>_. slota)))
      (IF ptr \<noteq> 0 
       THEN
          Guard C_Guard \<lbrace>hrs_htd \<acute>t_hrs \<Turnstile>\<^sub>t (Ptr ptr:: cte_C ptr)\<rbrace>
               (call (\<lambda>ta. ta(| mdb_node_ptr_' := Ptr &(Ptr ptr:: cte_C ptr
                                                          \<rightarrow>[''cteMDBNode_C'']),
                                 v_' := slotc |))
                mdb_node_ptr_set_mdbNext_'proc (\<lambda>s t. s\<lparr> globals := globals t \<rparr>) (\<lambda>ta s'. Basic (\<lambda>a. a)))
      FI)"
  apply (rule ccorres_guard_imp2) -- "replace preconditions by schematics"
  -- "Main Goal"
  apply (rule ccorres_Cond_rhs)
    apply (rule ccorres_updateMDB_cte_at)
    apply (ctac add: ccorres_updateMDB_set_mdbNext)
   apply (ctac ccorres: ccorres_updateMDB_skip)
  apply simp
  done
     
end
end
