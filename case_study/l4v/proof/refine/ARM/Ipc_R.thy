(*
 * Copyright 2014, General Dynamics C4 Systems
 *
 * This software may be distributed and modified according to the terms of
 * the GNU General Public License version 2. Note that NO WARRANTY is provided.
 * See "LICENSE_GPLv2.txt" for details.
 *
 * @TAG(GD_GPL)
 *)

theory Ipc_R
imports Finalise_R
begin

context begin interpretation Arch . (*FIXME: arch_split*)

lemmas lookup_slot_wrapper_defs'[simp] =
   lookupSourceSlot_def lookupTargetSlot_def lookupPivotSlot_def

lemma get_mi_corres: "corres (op = \<circ> message_info_map)
                      (tcb_at t) (tcb_at' t)
                      (get_message_info t) (getMessageInfo t)"
  apply (rule corres_guard_imp)
    apply (unfold get_message_info_def getMessageInfo_def fun_app_def)
    apply (simp add: ARM_H.msgInfoRegister_def
             ARM.msgInfoRegister_def ARM_A.msg_info_register_def)
    apply (rule corres_split_eqr [OF _ user_getreg_corres])
       apply (rule corres_trivial, simp add: message_info_from_data_eqv)
      apply (wp | simp)+
  done


lemma get_mi_inv'[wp]: "\<lbrace>I\<rbrace> getMessageInfo a \<lbrace>\<lambda>x. I\<rbrace>"
  by (simp add: getMessageInfo_def, wp)

definition
  "get_send_cap_relation rv rv' \<equiv> 
   (case rv of Some (c, cptr) \<Rightarrow> (\<exists>c' cptr'. rv' = Some (c', cptr') \<and>
                                            cte_map cptr = cptr' \<and>
                                            cap_relation c c')
             | None \<Rightarrow> rv' = None)"

lemma get_send_cap_relation_None [simp]:
  "get_send_cap_relation None None"
  by (simp add: get_send_cap_relation_def)

lemma cap_relation_mask:
  "\<lbrakk> cap_relation c c'; msk' = rights_mask_map msk \<rbrakk> \<Longrightarrow> 
  cap_relation (mask_cap msk c) (maskCapRights msk' c')"
  by simp

lemma lsfco_cte_at':
  "\<lbrace>valid_objs' and valid_cap' cap\<rbrace> 
  lookupSlotForCNodeOp f cap idx depth 
  \<lbrace>\<lambda>rv. cte_at' rv\<rbrace>, -"
  apply (simp add: lookupSlotForCNodeOp_def)
  apply (rule conjI)
   prefer 2
   apply clarsimp
   apply (wp)
  apply (clarsimp simp: split_def unlessE_def
             split del: if_split)
  apply (wp hoare_drop_imps throwE_R)
  done

declare unifyFailure_wp [wp]

(* FIXME: move *)
lemma unifyFailure_wp_E [wp]:
  "\<lbrace>P\<rbrace> f -, \<lbrace>\<lambda>_. E\<rbrace> \<Longrightarrow> \<lbrace>P\<rbrace> unifyFailure f -, \<lbrace>\<lambda>_. E\<rbrace>"
  unfolding validE_E_def
  by (erule unifyFailure_wp)+

(* FIXME: move *)
lemma unifyFailure_wp2 [wp]:
  assumes x: "\<lbrace>P\<rbrace> f \<lbrace>\<lambda>_. Q\<rbrace>"
  shows      "\<lbrace>P\<rbrace> unifyFailure f \<lbrace>\<lambda>_. Q\<rbrace>"
  by (wp x, simp)

definition
  ct_relation :: "captransfer \<Rightarrow> cap_transfer \<Rightarrow> bool"
where
 "ct_relation ct ct' \<equiv>
    ct_receive_root ct = to_bl (ctReceiveRoot ct')
  \<and> ct_receive_index ct = to_bl (ctReceiveIndex ct')
  \<and> ctReceiveDepth ct' = unat (ct_receive_depth ct)"

lemma rights_mask_map_data_to_rights:
  "rights_mask_map (data_to_rights x) = rightsFromWord x"
  by (simp add: rights_mask_map_def rightsFromWord_def
                data_to_rights_def Let_def nth_ucast)

(* MOVE *)
lemma valid_ipc_buffer_ptr_aligned_2:
  "\<lbrakk>valid_ipc_buffer_ptr' a s;  is_aligned y 2 \<rbrakk> \<Longrightarrow> is_aligned (a + y) 2"
  unfolding valid_ipc_buffer_ptr'_def 
  apply clarsimp
  apply (erule (1) aligned_add_aligned)
  apply (simp add: msg_align_bits)
  done

(* MOVE *)
lemma valid_ipc_buffer_ptr'D2:
  "\<lbrakk>valid_ipc_buffer_ptr' a s; y < max_ipc_words * 4; is_aligned y 2\<rbrakk> \<Longrightarrow> typ_at' UserDataT (a + y && ~~ mask pageBits) s"
  unfolding valid_ipc_buffer_ptr'_def 
  apply clarsimp
  apply (subgoal_tac "(a + y) && ~~ mask pageBits = a  && ~~ mask pageBits")
   apply simp
  apply (rule mask_out_first_mask_some [where n = msg_align_bits])
   apply (erule is_aligned_add_helper [THEN conjunct2])
   apply (erule order_less_le_trans)
   apply (simp add: msg_align_bits max_ipc_words )
  apply simp
  done

lemma load_ct_corres:
  "corres ct_relation \<top> (valid_ipc_buffer_ptr' buffer) (load_cap_transfer buffer) (loadCapTransfer buffer)"
  apply (simp add: load_cap_transfer_def loadCapTransfer_def 
                   captransfer_from_words_def captransfer_size_def 
                   capTransferDataSize_def capTransferFromWords_def
                   msgExtraCapBits_def word_size add.commute add.left_commute
                   msg_max_length_def msg_max_extra_caps_def word_size_def
                   msgMaxLength_def msgMaxExtraCaps_def msgLengthBits_def wordSize_def wordBits_def
              del: upt.simps)
  apply (rule corres_guard_imp)
    apply (rule corres_split [OF _ load_word_corres])
      apply (rule corres_split [OF _ load_word_corres])
        apply (rule corres_split [OF _ load_word_corres])
          apply (rule_tac P=\<top> and P'=\<top> in corres_inst)
          apply (clarsimp simp: ct_relation_def)
         apply (wp no_irq_loadWord)+
   apply simp
  apply (simp add: conj_comms)
  apply safe
       apply (erule valid_ipc_buffer_ptr_aligned_2, simp add: is_aligned_def)+
    apply (erule valid_ipc_buffer_ptr'D2, simp add: max_ipc_words, simp add: is_aligned_def)+
  done

lemma get_recv_slot_corres:
  "corres (\<lambda>xs ys. ys = map cte_map xs)
    (tcb_at receiver and valid_objs and pspace_aligned)
    (tcb_at' receiver and valid_objs' and pspace_aligned' and pspace_distinct' and
     case_option \<top> valid_ipc_buffer_ptr' recv_buf)
    (get_receive_slots receiver recv_buf)
    (getReceiveSlots receiver recv_buf)"
  apply (cases recv_buf)
   apply (simp add: getReceiveSlots_def)
  apply (simp add: getReceiveSlots_def split_def)
  apply (rule corres_guard_imp)
    apply (rule corres_split [OF _ load_ct_corres])
      apply (rule corres_empty_on_failure)
      apply (rule corres_splitEE)
         prefer 2
         apply (rule corres_unify_failure)
          apply (rule lookup_cap_corres)
          apply (simp add: ct_relation_def)
         apply simp
        apply (rule corres_splitEE)
           prefer 2
           apply (rule corres_unify_failure)
            apply (simp add: ct_relation_def)
            apply (erule lsfc_corres [OF _ refl])
           apply simp
          apply (simp add: split_def liftE_bindE unlessE_whenE)
          apply (rule corres_split [OF _ get_cap_corres])
            apply (rule corres_split_norE)
               apply (rule corres_trivial, simp add: returnOk_def)
              apply (rule corres_whenE)
                apply (case_tac cap, auto)[1]
               apply (rule corres_trivial, simp)
              apply simp
             apply (wp lookup_cap_valid lookup_cap_valid' lsfco_cte_at | simp)+
  done

lemma get_recv_slot_inv'[wp]:
  "\<lbrace> P \<rbrace> getReceiveSlots receiver buf \<lbrace>\<lambda>rv'. P \<rbrace>"
  apply (case_tac buf)
   apply (simp add: getReceiveSlots_def)
  apply (simp add: getReceiveSlots_def
                   split_def unlessE_def)
  apply (wp | simp)+
  done

lemma get_rs_cte_at'[wp]:
  "\<lbrace>\<top>\<rbrace> 
   getReceiveSlots receiver recv_buf 
   \<lbrace>\<lambda>rv s. \<forall>x \<in> set rv. cte_wp_at' (\<lambda>c. cteCap c = capability.NullCap) x s\<rbrace>"
  apply (cases recv_buf)
   apply (simp add: getReceiveSlots_def)
   apply (wp,simp)
  apply (clarsimp simp add: getReceiveSlots_def
                            split_def whenE_def unlessE_whenE)
  apply wp
     apply simp
     apply (rule getCTE_wp)
    apply (simp add: cte_wp_at_ctes_of cong: conj_cong)
    apply wp+
  apply simp
  done

lemma get_rs_real_cte_at'[wp]:
  "\<lbrace>valid_objs'\<rbrace>
   getReceiveSlots receiver recv_buf 
   \<lbrace>\<lambda>rv s. \<forall>x \<in> set rv. real_cte_at' x s\<rbrace>"
  apply (cases recv_buf)
   apply (simp add: getReceiveSlots_def)
   apply (wp,simp)
  apply (clarsimp simp add: getReceiveSlots_def
                            split_def whenE_def unlessE_whenE)
  apply wp
     apply simp
     apply (wp hoare_drop_imps)[1]
    apply simp
    apply (wp lookup_cap_valid')+
  apply simp
  done

declare word_div_1 [simp]
declare word_minus_one_le [simp]
declare word32_minus_one_le [simp]

lemma load_word_offs_corres':
  "\<lbrakk> y < unat max_ipc_words; y' = of_nat y * 4 \<rbrakk> \<Longrightarrow>
  corres op = \<top> (valid_ipc_buffer_ptr' a) (load_word_offs a y) (loadWordUser (a + y'))"
  apply simp
  apply (erule load_word_offs_corres)
  done

declare loadWordUser_inv [wp]

lemma get_extra_cptrs_corres:
  "corres (\<lambda>xs ys. xs = map to_bl ys) (\<lambda>_. valid_message_info mi) 
      (case_option \<top> valid_ipc_buffer_ptr' buf)
      (get_extra_cptrs buf mi) (getExtraCPtrs buf (message_info_map mi))"
  apply (rule corres_gen_asm [where P = \<top>, simplified])
  apply (cases mi, cases buf; simp add: getExtraCPtrs_def del: upt.simps)
  apply (rule corres_guard_imp)
    apply (simp add: mapM_map_simp comp_def del: upt.simps)
  apply (rule corres_mapM_list_all2[where r'="op =" and S="\<lambda>x y. y < 7 \<and> x = Suc msg_max_length + unat y"])
         apply simp
        apply simp
       apply simp
       apply (rule load_word_offs_corres')
        apply (simp add: word_size_def word_size field_simps
                         msg_max_length_def msgMaxLength_def
                         msgLengthBits_def max_ipc_words word_less_nat_alt)
       apply (simp add: word_size_def word_size field_simps
                        msg_max_length_def msgMaxLength_def wordSize_def wordBits_def
                        msgLengthBits_def max_ipc_words word_less_nat_alt)
      apply wp+
    apply (simp add: map_Suc_upt[symmetric] upt_lhs_sub_map[where x=msg_max_length]
                     upto_enum_step_def upto_enum_def unat_minus_one unat_gt_0
                     list_all2_map2 list_all2_map1
                del: upt.simps)
    apply (rule impI)
    apply (rule list_all2I)
     apply (subst upt_lhs_sub_map)
     apply (clarsimp simp: set_zip_same zip_map1 buffer_cptr_index_def)
     apply (clarsimp simp add: valid_message_info_def msg_max_extra_caps_def)
      apply (subgoal_tac "b < 6")
     apply (simp add: of_nat_Suc [symmetric] word_less_nat_alt unat_of_nat32 word_bits_conv
     del: of_nat_Suc)
     apply (simp add: word_le_nat_alt)
    apply simp+
  done

lemma getExtraCptrs_inv[wp]:
  "\<lbrace>P\<rbrace> getExtraCPtrs buf mi \<lbrace>\<lambda>rv. P\<rbrace>"
  apply (cases mi, cases buf, simp_all add: getExtraCPtrs_def)
  apply (wp dmo_inv' mapM_wp' loadWord_inv)
  done

lemma getSlotCap_cte_wp_at_rv:
  "\<lbrace>cte_wp_at' (\<lambda>cte. P (cteCap cte) cte) p\<rbrace>
     getSlotCap p
   \<lbrace>\<lambda>rv. cte_wp_at' (P rv) p\<rbrace>"
  apply (simp add: getSlotCap_def)
  apply (wp getCTE_ctes_wp)
  apply (clarsimp simp: cte_wp_at_ctes_of)
  done

lemma badge_derived_mask [simp]:
  "badge_derived' (maskCapRights R c) c' = badge_derived' c c'"
  by (simp add: badge_derived'_def)

declare derived'_not_Null [simp]

lemma maskCapRights_vsCapRef[simp]:
  "vsCapRef (maskCapRights msk cap) = vsCapRef cap"
  unfolding vsCapRef_def
  apply (cases cap, simp_all add: maskCapRights_def isCap_simps Let_def)
  apply (rename_tac arch_capability)
  apply (case_tac arch_capability;
         simp add: maskCapRights_def ARM_H.maskCapRights_def isCap_simps Let_def)
  done

lemma corres_set_extra_badge:
  "b' = b \<Longrightarrow> 
  corres dc (in_user_frame buffer)
         (valid_ipc_buffer_ptr' buffer and
          (\<lambda>_. msg_max_length + 2 + n < unat max_ipc_words))
         (set_extra_badge buffer b n) (setExtraBadge buffer b' n)"
  apply (rule corres_gen_asm2)
  apply (drule store_word_offs_corres [where a=buffer and w=b])
  apply (simp add: set_extra_badge_def setExtraBadge_def buffer_cptr_index_def
                   bufferCPtrOffset_def Let_def)
  apply (simp add: word_size word_size_def wordSize_def wordBits_def
                   bufferCPtrOffset_def buffer_cptr_index_def msgMaxLength_def 
                   msg_max_length_def msgLengthBits_def store_word_offs_def
                   add.commute add.left_commute)
  done

crunch typ_at': setExtraBadge "\<lambda>s. P (typ_at' T p s)"
lemmas setExtraBadge_typ_ats' [wp] = typ_at_lifts [OF setExtraBadge_typ_at']
crunch valid_pspace' [wp]: setExtraBadge valid_pspace'
crunch cte_wp_at' [wp]: setExtraBadge "cte_wp_at' P p"
crunch ipc_buffer' [wp]: setExtraBadge "valid_ipc_buffer_ptr' buffer"

crunch inv'[wp]: getExtraCPtr P (wp: dmo_inv' loadWord_inv)

lemma get_extra_cptr_corres:
  "corres (\<lambda>a c. a = to_bl c) \<top> 
          (valid_ipc_buffer_ptr' buffer and K (2 + msg_max_length + n < unat max_ipc_words))
          (get_extra_cptr buffer n)
          (getExtraCPtr buffer n)"
  apply (unfold K_def)
  apply (rule corres_gen_asm2)
  apply (simp add: get_extra_cptr_def getExtraCPtr_def buffer_cptr_index_def 
                   word_size_def msg_max_length_def word_size bufferCPtrOffset_def
                   msgMaxLength_def msgLengthBits_def wordSize_def wordBits_def)
  apply (simp add: field_simps)
  apply (rule corres_guard_imp, rule corres_rel_imp,
         rule load_word_offs_corres', simp_all)
  done

lemmas unifyFailure_discard2
    = corres_injection[OF id_injection unifyFailure_injection, simplified]

lemma deriveCap_not_null:
  "\<lbrace>\<top>\<rbrace> deriveCap slot cap \<lbrace>\<lambda>rv. K (rv \<noteq> NullCap \<longrightarrow> cap \<noteq> NullCap)\<rbrace>,-"
  apply (simp add: deriveCap_def split del: if_split)
  apply (case_tac cap)
          apply (simp_all add: Let_def isCap_simps)
  apply wp
  apply simp
  done

lemma deriveCap_derived_foo:
  "\<lbrace>\<lambda>s. \<forall>cap'. (cte_wp_at' (\<lambda>cte. badge_derived' cap (cteCap cte)
                     \<and> capASID cap = capASID (cteCap cte) \<and> cap_asid_base' cap = cap_asid_base' (cteCap cte)
                     \<and> cap_vptr' cap = cap_vptr' (cteCap cte)) slot s
              \<and> valid_objs' s \<and> cap' \<noteq> NullCap \<longrightarrow> cte_wp_at' (is_derived' (ctes_of s) slot cap' \<circ> cteCap) slot s)
        \<and> (cte_wp_at' (untyped_derived_eq cap \<circ> cteCap) slot s
            \<longrightarrow> cte_wp_at' (untyped_derived_eq cap' \<circ> cteCap) slot s)
        \<and> (s \<turnstile>' cap \<longrightarrow> s \<turnstile>' cap') \<and> (cap' \<noteq> NullCap \<longrightarrow> cap \<noteq> NullCap) \<longrightarrow> Q cap' s\<rbrace>
    deriveCap slot cap \<lbrace>Q\<rbrace>,-"
  using deriveCap_derived[where slot=slot and c'=cap] deriveCap_valid[where slot=slot and c=cap]
        deriveCap_untyped_derived[where slot=slot and c'=cap] deriveCap_not_null[where slot=slot and cap=cap]
  apply (clarsimp simp: validE_R_def validE_def valid_def split: sum.split)
  apply (frule in_inv_by_hoareD[OF deriveCap_inv])
  apply (clarsimp simp: o_def)
  apply (drule spec, erule mp)
  apply safe
     apply fastforce
    apply (drule spec, drule(1) mp)
    apply fastforce
   apply (drule spec, drule(1) mp)
   apply fastforce
  apply (drule spec, drule(1) bspec, simp)
  done

lemma valid_mdb_untyped_incD':
  "valid_mdb' s \<Longrightarrow> untyped_inc' (ctes_of s)"
  by (simp add: valid_mdb'_def valid_mdb_ctes_def)

lemma cteInsert_cte_wp_at:
  "\<lbrace>\<lambda>s. cte_wp_at' (\<lambda>c. is_derived' (ctes_of s) src cap (cteCap c)) src s 
       \<and> valid_mdb' s \<and> valid_objs' s
       \<and> (if p = dest then P cap 
            else cte_wp_at' (\<lambda>c. P (maskedAsFull (cteCap c) cap)) p s)\<rbrace>
    cteInsert cap src dest 
   \<lbrace>\<lambda>uu. cte_wp_at' (\<lambda>c. P (cteCap c)) p\<rbrace>"
  apply (simp add: cteInsert_def)
  apply (wp updateMDB_weak_cte_wp_at updateCap_cte_wp_at_cases getCTE_wp static_imp_wp
         | clarsimp simp: comp_def
         | unfold setUntypedCapAsFull_def)+
  apply (drule cte_at_cte_wp_atD)
  apply (elim exE)
  apply (rule_tac x=cte in exI)
  apply clarsimp
  apply (drule cte_at_cte_wp_atD)
  apply (elim exE)
  apply (rule_tac x=ctea in exI)
  apply clarsimp
  apply (cases "p=dest")
   apply (clarsimp simp: cte_wp_at'_def)
  apply (cases "p=src")
   apply clarsimp
   apply (intro conjI impI)
    apply ((clarsimp simp: cte_wp_at'_def maskedAsFull_def split: if_split_asm)+)[2]
  apply clarsimp
  apply (rule conjI)
   apply (clarsimp simp: maskedAsFull_def cte_wp_at_ctes_of split:if_split_asm)
   apply (erule disjE) prefer 2 apply simp
   apply (clarsimp simp: is_derived'_def isCap_simps)
   apply (drule valid_mdb_untyped_incD')
   apply (case_tac cte, case_tac cteb, clarsimp)
   apply (drule untyped_incD', (simp add: isCap_simps)+)
   apply (frule(1) ctes_of_valid'[where p = p])
   apply (clarsimp simp:valid_cap'_def capAligned_def split:if_splits)
    apply (drule_tac y ="of_nat fb"  in word_plus_mono_right[OF _  is_aligned_no_overflow',rotated])
      apply simp+
     apply (rule word_of_nat_less)
     apply simp
    apply (simp add:p_assoc_help)
   apply (simp add: max_free_index_def)
  apply (clarsimp simp: maskedAsFull_def is_derived'_def badge_derived'_def 
                        isCap_simps capMasterCap_def cte_wp_at_ctes_of
                  split: if_split_asm capability.splits)
  done

lemma cteInsert_weak_cte_wp_at3:
  assumes imp:"\<And>c. P c \<Longrightarrow> \<not> isUntypedCap c"
  shows " \<lbrace>\<lambda>s. if p = dest then P cap 
            else cte_wp_at' (\<lambda>c. P (cteCap c)) p s\<rbrace>
    cteInsert cap src dest 
   \<lbrace>\<lambda>uu. cte_wp_at' (\<lambda>c. P (cteCap c)) p\<rbrace>"
  by (wp updateMDB_weak_cte_wp_at updateCap_cte_wp_at_cases getCTE_wp' static_imp_wp
         | clarsimp simp: comp_def cteInsert_def
         | unfold setUntypedCapAsFull_def
         | auto simp: cte_wp_at'_def dest!: imp)+

lemma maskedAsFull_null_cap[simp]:
  "(maskedAsFull x y = capability.NullCap) = (x = capability.NullCap)"
  "(capability.NullCap  = maskedAsFull x y) = (x = capability.NullCap)"
  by (case_tac x, auto simp:maskedAsFull_def isCap_simps )

lemma maskCapRights_eq_null:
  "(RetypeDecls_H.maskCapRights r xa = capability.NullCap) =
   (xa = capability.NullCap)"
  apply (cases xa; simp add: maskCapRights_def isCap_simps)
  apply (rename_tac arch_capability)
  apply (case_tac arch_capability)
      apply (simp_all add: ARM_H.maskCapRights_def isCap_simps)
  done

lemma capMasterCap_maskedAsFull[simp]:
  "capMasterCap (maskedAsFull xa xa) = capMasterCap xa"
  by (cases xa; simp add: maskedAsFull_def isCap_simps capMasterCap_def)

lemma cte_refs'_maskedAsFull[simp]:
  "cte_refs' (maskedAsFull a b) = cte_refs' a"
  apply (rule ext)+
  apply (case_tac a)
   apply (clarsimp simp:maskedAsFull_def isCap_simps)+
 done


lemma tc_loop_corres:
  "\<lbrakk> list_all2 (\<lambda>(cap, slot) (cap', slot'). cap_relation cap cap'
             \<and> slot' = cte_map slot) caps caps';
      mi' = message_info_map mi \<rbrakk> \<Longrightarrow>
   corres (op = \<circ> message_info_map)
      (\<lambda>s. valid_objs s \<and> pspace_aligned s \<and> pspace_distinct s \<and> valid_mdb s
         \<and> valid_list s
         \<and> (case ep of Some x \<Rightarrow> ep_at x s | _ \<Rightarrow> True)
         \<and> (\<forall>x \<in> set slots. cte_wp_at (\<lambda>cap. cap = cap.NullCap) x s \<and>
                             real_cte_at x s)
         \<and> (\<forall>(cap, slot) \<in> set caps. valid_cap cap s \<and>
                    cte_wp_at (\<lambda>cp'. (cap \<noteq> cap.NullCap \<longrightarrow> cp'\<noteq>cap \<longrightarrow> cp' = masked_as_full cap cap )) slot s )
         \<and> distinct slots
         \<and> in_user_frame buffer s)
      (\<lambda>s. valid_pspace' s 
         \<and> (case ep of Some x \<Rightarrow> ep_at' x s | _ \<Rightarrow> True)
         \<and> (\<forall>x \<in> set (map cte_map slots).
             cte_wp_at' (\<lambda>cte. cteCap cte = NullCap) x s
                   \<and> real_cte_at' x s)
         \<and> distinct (map cte_map slots)
         \<and> valid_ipc_buffer_ptr' buffer s
         \<and> (\<forall>(cap, slot) \<in> set caps'. valid_cap' cap s \<and> 
                    cte_wp_at' (\<lambda>cte. cap \<noteq> NullCap \<longrightarrow> cteCap cte \<noteq> cap \<longrightarrow> cteCap cte = maskedAsFull cap cap) slot s)
         \<and> 2 + msg_max_length + n + length caps' < unat max_ipc_words)
      (transfer_caps_loop ep buffer n caps slots mi)
      (transferCapsToSlots ep buffer n caps'
         (map cte_map slots) mi')"
  (is "\<lbrakk> list_all2 ?P caps caps'; ?v \<rbrakk> \<Longrightarrow> ?corres")
proof (induct caps caps' arbitrary: slots n mi mi' rule: list_all2_induct)
  case Nil
  show ?case using Nil.prems by (case_tac mi, simp)
next
  case (Cons x xs y ys slots n mi mi')
  note if_weak_cong[cong] if_cong [cong del]
  assume P: "?P x y"
  show ?case using Cons.prems P
    apply (clarsimp split del: if_split)
    apply (simp add: Let_def split_def word_size liftE_bindE
                     word_bits_conv[symmetric] split del: if_split)
    apply (rule corres_const_on_failure)
    apply (simp add: dc_def[symmetric] split del: if_split)
    apply (rule corres_guard_imp)
      apply (rule corres_if2)
        apply (case_tac "fst x", auto simp add: isCap_simps)[1]
       apply (rule corres_split [OF _ corres_set_extra_badge])
          apply (drule conjunct1)
          apply simp
          apply (rule corres_rel_imp, rule Cons.hyps, simp_all)[1]
          apply (case_tac mi, simp)
         apply (clarsimp simp: is_cap_simps)
        apply (simp add: split_def)
        apply (wp hoare_vcg_const_Ball_lift)
       apply (subgoal_tac "obj_ref_of (fst x) = capEPPtr (fst y)")
        prefer 2
        apply (clarsimp simp: is_cap_simps)
       apply (simp add: split_def)
       apply (wp hoare_vcg_const_Ball_lift)
      apply (rule_tac P="slots = []" and Q="slots \<noteq> []" in corres_disj_division)
        apply simp
       apply (rule corres_trivial, simp add: returnOk_def)
       apply (case_tac mi, simp)
      apply (simp add: list_case_If2 split del: if_split)
      apply (rule corres_splitEE)
         prefer 2
         apply (rule unifyFailure_discard2)
          apply (case_tac mi, clarsimp)
         apply (rule derive_cap_corres)
          apply (simp add: remove_rights_def cap_relation_update_masks)
         apply clarsimp
        apply (rule corres_split_norE)
           apply (simp add: liftE_bindE)
           apply (rule corres_split_nor)
              prefer 2
              apply (rule cins_corres, simp_all add: hd_map)[1]
             apply (simp add: tl_map)
             apply (rule corres_rel_imp, rule Cons.hyps, simp_all)[1]
            apply (wp valid_case_option_post_wp hoare_vcg_const_Ball_lift
                        hoare_vcg_const_Ball_lift cap_insert_weak_cte_wp_at)
             apply (wp hoare_vcg_const_Ball_lift | simp add:split_def del: imp_disj1)+
             apply (wp cap_insert_cte_wp_at)
           apply (wp valid_case_option_post_wp hoare_vcg_const_Ball_lift
                     cteInsert_valid_pspace
                     | simp add: split_def)+
           apply (wp cteInsert_weak_cte_wp_at hoare_valid_ipc_buffer_ptr_typ_at')+
           apply (wp hoare_vcg_const_Ball_lift cteInsert_cte_wp_at  valid_case_option_post_wp
             | simp add:split_def)+
          apply (rule corres_whenE)
            apply (case_tac cap', auto)[1]
           apply (rule corres_trivial, simp)
           apply (case_tac mi, simp)
          apply simp
         apply (unfold whenE_def)
         apply wp+
        apply (clarsimp simp: conj_comms ball_conj_distrib split del: if_split)
        apply (rule_tac Q' ="\<lambda>cap' s. (cap'\<noteq> cap.NullCap \<longrightarrow> 
          cte_wp_at (is_derived (cdt s) (a, b) cap') (a, b) s
          \<and> QM s cap')" for QM
          in hoare_post_imp_R)
        prefer 2
         apply clarsimp
         apply assumption
        apply (subst imp_conjR)
        apply (rule hoare_vcg_conj_liftE_R)
        apply (rule derive_cap_is_derived)
       apply (wp derive_cap_is_derived_foo)+
      apply (simp split del: if_split)
      apply (rule_tac Q' ="\<lambda>cap' s. (cap'\<noteq> capability.NullCap \<longrightarrow> 
         cte_wp_at' (\<lambda>c. is_derived' (ctes_of s) (cte_map (a, b)) cap' (cteCap c)) (cte_map (a, b)) s
         \<and> QM s cap')" for QM
        in hoare_post_imp_R)
      prefer 2
       apply clarsimp
       apply assumption
      apply (subst imp_conjR)
      apply (rule hoare_vcg_conj_liftE_R)
       apply (rule hoare_post_imp_R[OF deriveCap_derived])
       apply (clarsimp simp:cte_wp_at_ctes_of)
      apply (wp deriveCap_derived_foo)
     apply (clarsimp simp: cte_wp_at_caps_of_state remove_rights_def
                           real_cte_tcb_valid if_apply_def2
                split del: if_split)
     apply (rule conjI, (clarsimp split del: if_split)+)
     apply (clarsimp simp:conj_comms split del:if_split)
     apply (intro conjI allI)
       apply (clarsimp split:if_splits)
       apply (case_tac "cap = fst x",simp+)
      apply (clarsimp simp:masked_as_full_def is_cap_simps cap_master_cap_simps)
    apply (clarsimp split del: if_split)
    apply (intro conjI)
           apply (clarsimp simp:neq_Nil_conv)
        apply (drule hd_in_set)
        apply (drule(1) bspec)
        apply (clarsimp split:if_split_asm)
      apply (fastforce simp:neq_Nil_conv)
      apply (intro ballI conjI)
       apply (clarsimp simp:neq_Nil_conv)
      apply (intro impI)
      apply (drule(1) bspec[OF _ subsetD[rotated]])
       apply (clarsimp simp:neq_Nil_conv)
     apply (clarsimp split:if_splits)
    apply clarsimp
    apply (intro conjI)
     apply (drule(1) bspec,clarsimp)+
    subgoal for \<dots> aa _ _ capa
     by (case_tac "capa = aa"; clarsimp split:if_splits simp:masked_as_full_def is_cap_simps)
   apply (case_tac "isEndpointCap (fst y) \<and> capEPPtr (fst y) = the ep \<and> (\<exists>y. ep = Some y)")
    apply (clarsimp simp:conj_comms split del:if_split)
   apply (subst if_not_P)
    apply clarsimp
   apply (clarsimp simp:valid_pspace'_def cte_wp_at_ctes_of split del:if_split)
   apply (intro conjI)
    apply (case_tac  "cteCap cte = fst y",clarsimp simp: badge_derived'_def)
    apply (clarsimp simp: maskCapRights_eq_null maskedAsFull_def badge_derived'_def isCap_simps
                    split: if_split_asm)
  apply (clarsimp split del: if_split)
  apply (case_tac "fst y = capability.NullCap")
    apply (clarsimp simp: neq_Nil_conv split del: if_split)+
  apply (intro allI impI conjI)
     apply (clarsimp split:if_splits)
    apply (clarsimp simp:image_def)+
   apply (thin_tac "\<forall>x\<in>set ys. Q x" for Q)
   apply (drule(1) bspec)+
   apply clarsimp+
  apply (drule(1) bspec)
  apply (rule conjI)
   apply clarsimp+
  apply (case_tac "cteCap cteb = ab")
   by (clarsimp simp: isCap_simps maskedAsFull_def split:if_splits)+
qed

declare constOnFailure_wp [wp]

lemma transferCapsToSlots_pres1[crunch_rules]:
  assumes x: "\<And>cap src dest. \<lbrace>P\<rbrace> cteInsert cap src dest \<lbrace>\<lambda>rv. P\<rbrace>"
  assumes eb: "\<And>b n. \<lbrace>P\<rbrace> setExtraBadge buffer b n \<lbrace>\<lambda>_. P\<rbrace>"
  shows      "\<lbrace>P\<rbrace> transferCapsToSlots ep buffer n caps slots mi \<lbrace>\<lambda>rv. P\<rbrace>"
  apply (induct caps arbitrary: slots n mi)
   apply simp
  apply (simp add: Let_def split_def whenE_def
             cong: if_cong list.case_cong
             split del: if_split)
  apply (rule hoare_pre)
   apply (wp x eb | assumption | simp split del: if_split | wpc
             | wp_once hoare_drop_imps)+
  done

lemma is_derived'_cte_refs':
  "is_derived' m src a b \<Longrightarrow> cte_refs' a = cte_refs' b"
  apply (rule ext)+
  apply (case_tac a)
  apply (clarsimp simp: is_derived'_def badge_derived'_def vsCapRef_def isCap_simps
                  split: capability.split_asm)+
  done

lemma cteInsert_cte_cap_to':
  "\<lbrace>ex_cte_cap_to' p and cte_wp_at' (\<lambda>cte. cteCap cte = NullCap) dest\<rbrace>
   cteInsert cap src dest
   \<lbrace>\<lambda>rv. ex_cte_cap_to' p\<rbrace>"
  apply (simp add: ex_cte_cap_to'_def)
  apply (rule hoare_pre)
   apply (rule hoare_use_eq_irq_node' [OF cteInsert_ksInterruptState])
   apply (clarsimp simp:cteInsert_def)
    apply (wp hoare_vcg_ex_lift  updateMDB_weak_cte_wp_at updateCap_cte_wp_at_cases
      setUntypedCapAsFull_cte_wp_at getCTE_wp static_imp_wp)
   apply (clarsimp simp:cte_wp_at_ctes_of)
   apply (rule_tac x = "cref" in exI)
     apply (rule conjI)
     apply clarsimp+
  done

declare maskCapRights_eq_null[simp]

lemma lsfco_cte_wp_at_univ':
  "\<lbrace>valid_objs' and valid_cap' cap and K (\<forall>cte rv. P cte rv)\<rbrace>
      lookupSlotForCNodeOp f cap idx depth
   \<lbrace>\<lambda>rv. cte_wp_at' (P rv) rv\<rbrace>, -"
  apply (rule hoare_gen_asmE)
  apply (rule hoare_post_imp_R)
   apply (rule lsfco_cte_at')
  apply (clarsimp simp: cte_wp_at_ctes_of)
  done

crunch ex_cte_cap_wp_to' [wp]: setExtraBadge "ex_cte_cap_wp_to' P p"
  (rule: ex_cte_cap_to'_pres)

crunch valid_objs' [wp]: setExtraBadge valid_objs'
crunch aligned' [wp]: setExtraBadge pspace_aligned'
crunch distinct' [wp]: setExtraBadge pspace_distinct'

lemma cteInsert_assume_Null:
  "\<lbrace>P\<rbrace> cteInsert cap src dest \<lbrace>Q\<rbrace> \<Longrightarrow>
   \<lbrace>\<lambda>s. cte_wp_at' (\<lambda>cte. cteCap cte = NullCap) dest s \<longrightarrow> P s\<rbrace>
   cteInsert cap src dest
   \<lbrace>Q\<rbrace>"
  apply (rule hoare_name_pre_state)
  apply (erule impCE)
   apply (simp add: cteInsert_def)
   apply (rule hoare_seq_ext[OF _ getCTE_sp])+
   apply (rule hoare_name_pre_state)
   apply (clarsimp simp: cte_wp_at_ctes_of)
  apply (erule hoare_pre(1))
  apply simp
  done

crunch mdb'[wp]: setExtraBadge valid_mdb'

lemma cteInsert_weak_cte_wp_at2:
  assumes weak:"\<And>c cap. P (maskedAsFull c cap) = P c"
  shows
    "\<lbrace>\<lambda>s. if p = dest then P cap else cte_wp_at' (\<lambda>c. P (cteCap c)) p s\<rbrace>
     cteInsert cap src dest 
     \<lbrace>\<lambda>uu. cte_wp_at' (\<lambda>c. P (cteCap c)) p\<rbrace>"
  apply (rule hoare_pre)
   apply (rule hoare_use_eq_irq_node' [OF cteInsert_ksInterruptState])
   apply (clarsimp simp:cteInsert_def)
    apply (wp hoare_vcg_ex_lift  updateMDB_weak_cte_wp_at updateCap_cte_wp_at_cases
      setUntypedCapAsFull_cte_wp_at getCTE_wp static_imp_wp)
   apply (clarsimp simp:cte_wp_at_ctes_of weak)
   apply auto
  done

lemma transferCapsToSlots_presM:
  assumes x: "\<And>cap src dest. \<lbrace>\<lambda>s. P s \<and> (emx \<longrightarrow> cte_wp_at' (\<lambda>cte. cteCap cte = NullCap) dest s \<and> ex_cte_cap_to' dest s)
                                       \<and> (vo \<longrightarrow> valid_objs' s \<and> valid_cap' cap s \<and> real_cte_at' dest s)
                                       \<and> (drv \<longrightarrow> cte_wp_at' (is_derived' (ctes_of s) src cap \<circ> cteCap) src s
                                               \<and> cte_wp_at' (untyped_derived_eq cap o cteCap) src s
                                               \<and> valid_mdb' s)
                                       \<and> (pad \<longrightarrow> pspace_aligned' s \<and> pspace_distinct' s)\<rbrace>
                                           cteInsert cap src dest \<lbrace>\<lambda>rv. P\<rbrace>"
  assumes eb: "\<And>b n. \<lbrace>P\<rbrace> setExtraBadge buffer b n \<lbrace>\<lambda>_. P\<rbrace>"
  shows      "\<lbrace>\<lambda>s. P s
                 \<and> (emx \<longrightarrow> (\<forall>x \<in> set slots. ex_cte_cap_to' x s \<and> cte_wp_at' (\<lambda>cte. cteCap cte = NullCap) x s) \<and> distinct slots)
                 \<and> (vo \<longrightarrow> valid_objs' s \<and> (\<forall>x \<in> set slots. real_cte_at' x s \<and> cte_wp_at' (\<lambda>cte. cteCap cte = NullCap) x s)
                           \<and> (\<forall>x \<in> set caps. s \<turnstile>' fst x ) \<and> distinct slots)
                 \<and> (pad \<longrightarrow> pspace_aligned' s \<and> pspace_distinct' s)
                 \<and> (drv \<longrightarrow> vo \<and> pspace_aligned' s \<and> pspace_distinct' s \<and> valid_mdb' s
                         \<and> length slots \<le> 1
                         \<and> (\<forall>x \<in> set caps. s \<turnstile>' fst x \<and> (slots \<noteq> []
                              \<longrightarrow> cte_wp_at' (\<lambda>cte. fst x \<noteq> NullCap \<longrightarrow> cteCap cte = fst x) (snd x) s)))\<rbrace>
                 transferCapsToSlots ep buffer n caps slots mi
              \<lbrace>\<lambda>rv. P\<rbrace>"
  apply (induct caps arbitrary: slots n mi)
   apply (simp, wp, simp)
  apply (simp add: Let_def split_def whenE_def
             cong: if_cong list.case_cong split del: if_split)
  apply (rule hoare_pre)
   apply (wp eb hoare_vcg_const_Ball_lift hoare_vcg_const_imp_lift
           | assumption | wpc)+
     apply (rule cteInsert_assume_Null)
     apply (wp x hoare_vcg_const_Ball_lift cteInsert_cte_cap_to' static_imp_wp)
       apply (rule cteInsert_weak_cte_wp_at2,clarsimp)
      apply (wp hoare_vcg_const_Ball_lift static_imp_wp)+
       apply (rule cteInsert_weak_cte_wp_at2,clarsimp)
      apply (wp hoare_vcg_const_Ball_lift cteInsert_cte_wp_at static_imp_wp
          deriveCap_derived_foo)+
  apply (thin_tac "\<And>slots. PROP P slots" for P)
  apply (clarsimp simp: cte_wp_at_ctes_of remove_rights_def
                        real_cte_tcb_valid if_apply_def2
             split del: if_split)
  apply (rule conjI)
   apply (clarsimp simp:cte_wp_at_ctes_of untyped_derived_eq_def)
  apply (intro conjI allI)
     apply (clarsimp simp:Fun.comp_def cte_wp_at_ctes_of)+
  apply (clarsimp simp:valid_capAligned)
  done

lemmas transferCapsToSlots_pres2
    = transferCapsToSlots_presM[where vo=False and emx=True
                                  and drv=False and pad=False, simplified]

lemma transferCapsToSlots_aligned'[wp]:
  "\<lbrace>pspace_aligned'\<rbrace>
     transferCapsToSlots ep buffer n caps slots mi
   \<lbrace>\<lambda>rv. pspace_aligned'\<rbrace>"
  by (wp transferCapsToSlots_pres1)

lemma transferCapsToSlots_distinct'[wp]:
  "\<lbrace>pspace_distinct'\<rbrace>
     transferCapsToSlots ep buffer n caps slots mi
   \<lbrace>\<lambda>rv. pspace_distinct'\<rbrace>"
  by (wp transferCapsToSlots_pres1)

lemma transferCapsToSlots_typ_at'[wp]:
   "\<lbrace>\<lambda>s. P (typ_at' T p s)\<rbrace>
      transferCapsToSlots ep buffer n caps slots mi
    \<lbrace>\<lambda>rv s. P (typ_at' T p s)\<rbrace>"
  by (wp transferCapsToSlots_pres1 setExtraBadge_typ_at')

lemma transferCapsToSlots_valid_objs[wp]:
  "\<lbrace>valid_objs' and valid_mdb' and (\<lambda>s. \<forall>x \<in> set slots. real_cte_at' x s \<and> cte_wp_at' (\<lambda>cte. cteCap cte = capability.NullCap) x s)
       and (\<lambda>s. \<forall>x \<in> set caps. s \<turnstile>' fst x) and K(distinct slots)\<rbrace>
       transferCapsToSlots ep buffer n caps slots mi
   \<lbrace>\<lambda>rv. valid_objs'\<rbrace>"
  apply (rule hoare_pre)
   apply (rule transferCapsToSlots_presM[where vo=True and emx=False and drv=False and pad=False])
    apply (wp | simp)+
  done

abbreviation(input)
  "transferCaps_srcs caps s \<equiv> \<forall>x\<in>set caps. cte_wp_at' (\<lambda>cte. fst x \<noteq> NullCap \<longrightarrow> cteCap cte = fst x) (snd x) s"

lemma transferCapsToSlots_mdb[wp]:
  "\<lbrace>\<lambda>s. valid_pspace' s \<and> distinct slots
          \<and> length slots \<le> 1
          \<and> (\<forall>x \<in> set slots. ex_cte_cap_to' x s \<and> cte_wp_at' (\<lambda>cte. cteCap cte = capability.NullCap) x s)
          \<and> (\<forall>x \<in> set slots. real_cte_at' x s)
          \<and> transferCaps_srcs caps s\<rbrace>
    transferCapsToSlots ep buffer n caps slots mi
   \<lbrace>\<lambda>rv. valid_mdb'\<rbrace>"
  apply (wp transferCapsToSlots_presM[where drv=True and vo=True and emx=True and pad=True])
    apply clarsimp
    apply (frule valid_capAligned)
    apply (clarsimp simp: cte_wp_at_ctes_of is_derived'_def badge_derived'_def)
   apply wp
  apply (clarsimp simp: valid_pspace'_def)
  apply (clarsimp simp:cte_wp_at_ctes_of)
  apply (drule(1) bspec,clarify)
  apply (case_tac cte)
  apply (clarsimp dest!:ctes_of_valid_cap' split:if_splits)
  apply (fastforce simp:valid_cap'_def)
  done

crunch no_0' [wp]: setExtraBadge no_0_obj'

lemma transferCapsToSlots_no_0_obj' [wp]:
  "\<lbrace>no_0_obj'\<rbrace> transferCapsToSlots ep buffer n caps slots mi \<lbrace>\<lambda>rv. no_0_obj'\<rbrace>"
  by (wp transferCapsToSlots_pres1)

lemma transferCapsToSlots_vp[wp]:
  "\<lbrace>\<lambda>s. valid_pspace' s \<and> distinct slots
          \<and> length slots \<le> 1
          \<and> (\<forall>x \<in> set slots. ex_cte_cap_to' x s \<and> cte_wp_at' (\<lambda>cte. cteCap cte = capability.NullCap) x s)
          \<and> (\<forall>x \<in> set slots. real_cte_at' x s)
          \<and> transferCaps_srcs caps s\<rbrace>
    transferCapsToSlots ep buffer n caps slots mi
   \<lbrace>\<lambda>rv. valid_pspace'\<rbrace>"
  apply (rule hoare_pre)
   apply (simp add: valid_pspace'_def | wp)+
  apply (fastforce simp: cte_wp_at_ctes_of dest: ctes_of_valid')
  done

crunch sch_act [wp]: setExtraBadge, doIPCTransfer "\<lambda>s. P (ksSchedulerAction s)"
  (wp: crunch_wps mapME_wp' simp: zipWithM_x_mapM)
crunch pred_tcb_at' [wp]: setExtraBadge "\<lambda>s. pred_tcb_at' proj P p s"
crunch ksCurThread[wp]: setExtraBadge "\<lambda>s. P (ksCurThread s)"
crunch ksCurDomain[wp]: setExtraBadge "\<lambda>s. P (ksCurDomain s)"
crunch obj_at' [wp]: setExtraBadge "\<lambda>s. P' (obj_at' P p s)"
  (simp: storeWordUser_def)
crunch queues [wp]: setExtraBadge "\<lambda>s. P (ksReadyQueues s)"
crunch queuesL1 [wp]: setExtraBadge "\<lambda>s. P (ksReadyQueuesL1Bitmap s)"
crunch queuesL2 [wp]: setExtraBadge "\<lambda>s. P (ksReadyQueuesL2Bitmap s)"

lemma tcts_sch_act[wp]:
  "\<lbrace>\<lambda>s. sch_act_wf (ksSchedulerAction s) s\<rbrace>
     transferCapsToSlots ep buffer n caps slots mi
   \<lbrace>\<lambda>rv s. sch_act_wf (ksSchedulerAction s) s\<rbrace>"
  by (wp sch_act_wf_lift tcb_in_cur_domain'_lift transferCapsToSlots_pres1)

lemma tcts_vq[wp]:
  "\<lbrace>Invariants_H.valid_queues\<rbrace> transferCapsToSlots ep buffer n caps slots mi \<lbrace>\<lambda>rv. Invariants_H.valid_queues\<rbrace>"
  by (wp valid_queues_lift transferCapsToSlots_pres1)

lemma tcts_vq'[wp]:
  "\<lbrace>valid_queues'\<rbrace> transferCapsToSlots ep buffer n caps slots mi \<lbrace>\<lambda>rv. valid_queues'\<rbrace>"
  by (wp valid_queues_lift' transferCapsToSlots_pres1)

crunch state_refs_of' [wp]: setExtraBadge "\<lambda>s. P (state_refs_of' s)"

lemma tcts_state_refs_of'[wp]:
  "\<lbrace>\<lambda>s. P (state_refs_of' s)\<rbrace>
     transferCapsToSlots ep buffer n caps slots mi
   \<lbrace>\<lambda>rv s. P (state_refs_of' s)\<rbrace>"
  by (wp transferCapsToSlots_pres1)

crunch if_live' [wp]: setExtraBadge if_live_then_nonz_cap'

lemma tcts_iflive[wp]:
  "\<lbrace>\<lambda>s. if_live_then_nonz_cap' s \<and> distinct slots \<and>
         (\<forall>x\<in>set slots.
             ex_cte_cap_to' x s \<and> cte_wp_at' (\<lambda>cte. cteCap cte = capability.NullCap) x s)\<rbrace>
  transferCapsToSlots ep buffer n caps slots mi
   \<lbrace>\<lambda>rv. if_live_then_nonz_cap'\<rbrace>"
  by (wp transferCapsToSlots_pres2 | simp)+

crunch if_unsafe' [wp]: setExtraBadge if_unsafe_then_cap'

lemma tcts_ifunsafe[wp]:
  "\<lbrace>\<lambda>s. if_unsafe_then_cap' s \<and> distinct slots \<and>
         (\<forall>x\<in>set slots.  cte_wp_at' (\<lambda>cte. cteCap cte = capability.NullCap) x s \<and>
             ex_cte_cap_to' x s)\<rbrace> transferCapsToSlots ep buffer n caps slots mi
   \<lbrace>\<lambda>rv. if_unsafe_then_cap'\<rbrace>"
  by (wp transferCapsToSlots_pres2 | simp)+

crunch it[wp]: ensureNoChildren "\<lambda>s. P (ksIdleThread s)"

crunch idle'[wp]: deriveCap "valid_idle'"

lemma deriveCap_not_idle [wp]:
  "\<lbrace>\<lambda>s. valid_idle' s \<and> ksIdleThread s \<notin> capRange cap\<rbrace>
   deriveCap slot cap
   \<lbrace>\<lambda>rv s. ksIdleThread s \<notin> capRange rv\<rbrace>, -"
  unfolding deriveCap_def badge_derived'_def
  including no_pre
  apply (cases cap, simp_all add: isCap_simps Let_def)
            defer 8 (* arch *)
            apply (wp ensureNoChildren_wp | clarsimp simp: capRange_def)+
  apply (rename_tac arch_capability)
  apply (case_tac arch_capability,
         simp_all add: ARM_H.deriveCap_def Let_def isCap_simps
                split: if_split,
         safe)
        apply (wp throwError_validE_R | clarsimp simp: capRange_def)+
  done

lemma maskCapRights_capRange[simp]:
  "capRange (maskCapRights r c) = capRange c"
  apply (case_tac c)
  apply (simp_all add: maskCapRights_def isCap_defs capRange_def Let_def
                       ARM_H.maskCapRights_def
                split: arch_capability.split)
  done

lemma getSlotCap_not_idle [wp]:
  "\<lbrace>valid_global_refs'\<rbrace> getSlotCap addr \<lbrace>\<lambda>rv s. ksIdleThread s \<notin> capRange rv\<rbrace>"
  by (simp add: getSlotCap_def | wp getCTE_no_idle_cap)+

crunch valid_idle' [wp]: setExtraBadge valid_idle'

lemma tcts_idle'[wp]:
  "\<lbrace>\<lambda>s. valid_idle' s\<rbrace> transferCapsToSlots ep buffer n caps slots mi
   \<lbrace>\<lambda>rv. valid_idle'\<rbrace>"
  apply (rule hoare_pre) 
   apply (wp transferCapsToSlots_pres1)
  apply simp
  done

lemma tcts_ct[wp]:
  "\<lbrace>cur_tcb'\<rbrace> transferCapsToSlots ep buffer n caps slots mi \<lbrace>\<lambda>rv. cur_tcb'\<rbrace>"
  by (wp transferCapsToSlots_pres1 cur_tcb_lift)

crunch valid_arch_state' [wp]: setExtraBadge valid_arch_state'

lemma transferCapsToSlots_valid_arch [wp]:
  "\<lbrace>valid_arch_state'\<rbrace> transferCapsToSlots ep buffer n caps slots mi \<lbrace>\<lambda>rv. valid_arch_state'\<rbrace>"
  by (rule transferCapsToSlots_pres1; wp)

crunch valid_global_refs' [wp]: setExtraBadge valid_global_refs'

lemma transferCapsToSlots_valid_globals [wp]:
  "\<lbrace>valid_global_refs' and valid_objs' and valid_mdb' and pspace_distinct' and pspace_aligned' and K (distinct slots)
         and K (length slots \<le> 1)
         and (\<lambda>s. \<forall>x \<in> set slots. real_cte_at' x s \<and> cte_wp_at' (\<lambda>cte. cteCap cte = capability.NullCap) x s)
  and transferCaps_srcs caps\<rbrace> 
  transferCapsToSlots ep buffer n caps slots mi 
  \<lbrace>\<lambda>rv. valid_global_refs'\<rbrace>"
  apply (wp transferCapsToSlots_presM[where vo=True and emx=False and drv=True and pad=True] | clarsimp)+
  apply (clarsimp simp:cte_wp_at_ctes_of)
  apply (drule(1) bspec,clarsimp)
  apply (case_tac cte,clarsimp)
  apply (frule(1) CSpace_I.ctes_of_valid_cap')
  apply (fastforce simp:valid_cap'_def)
  done

crunch irq_node' [wp]: setExtraBadge "\<lambda>s. P (irq_node' s)"

lemma transferCapsToSlots_irq_node'[wp]:
  "\<lbrace>\<lambda>s. P (irq_node' s)\<rbrace> transferCapsToSlots ep buffer n caps slots mi \<lbrace>\<lambda>rv s. P (irq_node' s)\<rbrace>"
   by (wp transferCapsToSlots_pres1)

lemma valid_irq_handlers_ctes_ofD:
  "\<lbrakk> ctes_of s p = Some cte; cteCap cte = IRQHandlerCap irq; valid_irq_handlers' s \<rbrakk>
       \<Longrightarrow> irq_issued' irq s"
  by (auto simp: valid_irq_handlers'_def cteCaps_of_def ran_def)

crunch valid_irq_handlers' [wp]: setExtraBadge valid_irq_handlers'

lemma transferCapsToSlots_irq_handlers[wp]:
  "\<lbrace>valid_irq_handlers' and valid_objs' and valid_mdb' and pspace_distinct' and pspace_aligned'
         and K(distinct slots \<and> length slots \<le> 1)
         and (\<lambda>s. \<forall>x \<in> set slots. real_cte_at' x s \<and> cte_wp_at' (\<lambda>cte. cteCap cte = capability.NullCap) x s)
         and transferCaps_srcs caps\<rbrace>
     transferCapsToSlots ep buffer n caps slots mi 
  \<lbrace>\<lambda>rv. valid_irq_handlers'\<rbrace>"
  apply (wp transferCapsToSlots_presM[where vo=True and emx=False and drv=True and pad=False])
     apply (clarsimp simp: is_derived'_def cte_wp_at_ctes_of badge_derived'_def)
     apply (erule(2) valid_irq_handlers_ctes_ofD)
    apply wp
  apply (clarsimp simp:cte_wp_at_ctes_of | intro ballI conjI)+
  apply (drule(1) bspec,clarsimp)
  apply (case_tac cte,clarsimp)
  apply (frule(1) CSpace_I.ctes_of_valid_cap')
  apply (fastforce simp:valid_cap'_def)
  done

crunch irq_state' [wp]: setExtraBadge "\<lambda>s. P (ksInterruptState s)"

lemma setExtraBadge_irq_states'[wp]: 
  "\<lbrace>valid_irq_states'\<rbrace> setExtraBadge buffer b n \<lbrace>\<lambda>_. valid_irq_states'\<rbrace>"
  apply (wp valid_irq_states_lift')
   apply (simp add: setExtraBadge_def storeWordUser_def)
   apply (wp no_irq dmo_lift' no_irq_storeWord)
  apply assumption
  done

lemma transferCapsToSlots_irq_states' [wp]: 
  "\<lbrace>valid_irq_states'\<rbrace> transferCapsToSlots ep buffer n caps slots mi \<lbrace>\<lambda>_. valid_irq_states'\<rbrace>"
  by (wp transferCapsToSlots_pres1)

crunch valid_pde_mappings' [wp]: setExtraBadge valid_pde_mappings'

lemma transferCapsToSlots_pde_mappings'[wp]:
  "\<lbrace>valid_pde_mappings'\<rbrace> transferCapsToSlots ep buffer n caps slots mi \<lbrace>\<lambda>rv. valid_pde_mappings'\<rbrace>"
  by (wp transferCapsToSlots_pres1)

lemma transferCapsToSlots_irqs_masked'[wp]:
  "\<lbrace>irqs_masked'\<rbrace> transferCapsToSlots ep buffer n caps slots mi \<lbrace>\<lambda>rv. irqs_masked'\<rbrace>"
  by (wp transferCapsToSlots_pres1 irqs_masked_lift)

lemma storeWordUser_vms'[wp]:
  "\<lbrace>valid_machine_state'\<rbrace> storeWordUser a w \<lbrace>\<lambda>_. valid_machine_state'\<rbrace>"
proof -
  have aligned_offset_ignore:
    "\<And>(l::word32) (p::word32) sz. l<4 \<Longrightarrow> p && mask 2 = 0 \<Longrightarrow>
       p+l && ~~ mask pageBits = p && ~~ mask pageBits"
  proof -
    fix l p sz
    assume al: "(p::word32) && mask 2 = 0"
    assume "(l::word32) < 4" hence less: "l<2^2" by simp
    have le: "2 \<le> pageBits" by (simp add: pageBits_def)
    show "?thesis l p sz"
      by (rule is_aligned_add_helper[simplified is_aligned_mask,
          THEN conjunct2, THEN mask_out_first_mask_some,
          where n=2, OF al less le])
  qed

  show ?thesis
    apply (simp add: valid_machine_state'_def storeWordUser_def
                     doMachineOp_def split_def)
    apply wp
    apply clarsimp
    apply (drule use_valid)
    apply (rule_tac x=p in storeWord_um_inv, simp+)
    apply (drule_tac x=p in spec)
    apply (erule disjE, simp_all)
    apply (erule conjE)
    apply (erule disjE, simp)
    apply (simp add: pointerInUserData_def word_size)
    apply (subgoal_tac "a && ~~ mask pageBits = p && ~~ mask pageBits", simp)
    apply (simp only: is_aligned_mask[of _ 2])
    apply (elim disjE, simp_all)
      apply (rule aligned_offset_ignore[symmetric], simp+)+
    done
qed

lemma setExtraBadge_vms'[wp]:
  "\<lbrace>valid_machine_state'\<rbrace> setExtraBadge buffer b n \<lbrace>\<lambda>_. valid_machine_state'\<rbrace>"
by (simp add: setExtraBadge_def) wp

lemma transferCapsToSlots_vms[wp]:
  "\<lbrace>\<lambda>s. valid_machine_state' s\<rbrace>
   transferCapsToSlots ep buffer n caps slots mi
   \<lbrace>\<lambda>_ s. valid_machine_state' s\<rbrace>"
  by (wp transferCapsToSlots_pres1)

crunch pspace_domain_valid[wp]: setExtraBadge, transferCapsToSlots
        "pspace_domain_valid"

crunch ct_not_inQ[wp]: setExtraBadge "ct_not_inQ"

lemma tcts_ct_not_inQ[wp]:
  "\<lbrace>ct_not_inQ\<rbrace>
   transferCapsToSlots ep buffer n caps slots mi
   \<lbrace>\<lambda>_. ct_not_inQ\<rbrace>"
  by (wp transferCapsToSlots_pres1)

crunch gsUntypedZeroRanges[wp]: setExtraBadge "\<lambda>s. P (gsUntypedZeroRanges s)"
crunch ctes_of[wp]: setExtraBadge "\<lambda>s. P (ctes_of s)"

lemma tcts_zero_ranges[wp]:
  "\<lbrace>\<lambda>s. untyped_ranges_zero' s \<and> valid_pspace' s \<and> distinct slots
          \<and> (\<forall>x \<in> set slots. ex_cte_cap_to' x s \<and> cte_wp_at' (\<lambda>cte. cteCap cte = capability.NullCap) x s)
          \<and> (\<forall>x \<in> set slots. real_cte_at' x s)
          \<and> length slots \<le> 1
          \<and> transferCaps_srcs caps s\<rbrace>
    transferCapsToSlots ep buffer n caps slots mi
  \<lbrace>\<lambda>rv. untyped_ranges_zero'\<rbrace>"
  apply (wp transferCapsToSlots_presM[where emx=True and vo=True
      and drv=True and pad=True])
    apply (clarsimp simp: cte_wp_at_ctes_of)
   apply (simp add: cteCaps_of_def)
   apply (rule hoare_pre, wp untyped_ranges_zero_lift)
   apply (simp add: o_def)
  apply (clarsimp simp: valid_pspace'_def ball_conj_distrib[symmetric])
  apply (drule(1) bspec)
  apply (clarsimp simp: cte_wp_at_ctes_of)
  apply (case_tac cte, clarsimp)
  apply (frule(1) ctes_of_valid_cap')
  apply auto[1]
  done

crunch ct_idle_or_in_cur_domain'[wp]: setExtraBadge ct_idle_or_in_cur_domain'
crunch ct_idle_or_in_cur_domain'[wp]: transferCapsToSlots ct_idle_or_in_cur_domain'
crunch ksCurDomain[wp]: transferCapsToSlots "\<lambda>s. P (ksCurDomain s)"
crunch ksDomSchedule[wp]: setExtraBadge "\<lambda>s. P (ksDomSchedule s)"
crunch ksDomScheduleIdx[wp]: setExtraBadge "\<lambda>s. P (ksDomScheduleIdx s)"
crunch ksDomSchedule[wp]: transferCapsToSlots "\<lambda>s. P (ksDomSchedule s)"
crunch ksDomScheduleIdx[wp]: transferCapsToSlots "\<lambda>s. P (ksDomScheduleIdx s)"


lemma transferCapsToSlots_invs[wp]:
  "\<lbrace>\<lambda>s. invs' s \<and> distinct slots 
          \<and> (\<forall>x \<in> set slots. cte_wp_at' (\<lambda>cte. cteCap cte = NullCap) x s)
          \<and> (\<forall>x \<in> set slots. ex_cte_cap_to' x s)
          \<and> (\<forall>x \<in> set slots. real_cte_at' x s)
          \<and> length slots \<le> 1
          \<and> transferCaps_srcs caps s\<rbrace>
    transferCapsToSlots ep buffer n caps slots mi
   \<lbrace>\<lambda>rv. invs'\<rbrace>"
  apply (simp add: invs'_def valid_state'_def)
  apply (wp valid_irq_node_lift)
  apply fastforce
  done

lemma set_extra_badges_flags_eq:
  "length badges \<le> msgMaxExtraCaps \<Longrightarrow>
   of_bl (rev (map (\<lambda>x. x = None) badges)) =
          foldl op + (0::word32)
           (zipWith (\<lambda>n. case_option (2 ^ n) (\<lambda>v5. 0)) [0..< Suc msgMaxExtraCaps]
             badges)"
  apply (induct badges rule: rev_induct)
   apply (simp add: zipWith_def)
  apply (simp add: of_bl_Cons zipWith_append2
              del: upt.simps)
  apply (simp split: option.split)
  done

lemma grs_distinct'[wp]:
  "\<lbrace>\<top>\<rbrace> getReceiveSlots t buf \<lbrace>\<lambda>rv s. distinct rv\<rbrace>"
  apply (cases buf, simp_all add: getReceiveSlots_def
                                  split_def unlessE_def)
   apply (wp, simp)
  apply (wp | simp only: distinct.simps list.simps empty_iff)+
  apply simp
  done

lemma getExtraCPtrs_length [wp]:
  "\<lbrace>\<lambda>s. msgExtraCaps msg < 6\<rbrace> 
  getExtraCPtrs send_buf msg \<lbrace>\<lambda>rv s. Suc (Suc (msg_max_length + length rv)) < unat max_ipc_words\<rbrace>"
  apply (simp add: getExtraCPtrs_def)
  apply (rule hoare_pre)
   apply (wpc|wp)+
  apply (clarsimp simp: max_ipc_words msg_max_length_def)
  apply (case_tac "1 \<le> xa")
   apply (simp add: length_upto_enum_step)
   apply unat_arith
  apply (subgoal_tac "0 = xa")
   prefer 2
   apply unat_arith
  apply (simp add: upto_enum_step_def)
  done 

lemma tc_corres:
  "\<lbrakk> info' = message_info_map info;
    list_all2 (\<lambda>x y. cap_relation (fst x) (fst y) \<and> snd y = cte_map (snd x))
         caps caps' \<rbrakk>
  \<Longrightarrow>
   corres (op = \<circ> message_info_map)
   (tcb_at receiver and valid_objs and 
    pspace_aligned and pspace_distinct and valid_mdb
    and valid_list
    and (\<lambda>s. case ep of Some x \<Rightarrow> ep_at x s | _ \<Rightarrow> True)
    and case_option \<top> in_user_frame recv_buf
    and (\<lambda>s. valid_message_info info)
    and transfer_caps_srcs caps)
   (tcb_at' receiver and valid_objs' and
    pspace_aligned' and pspace_distinct' and no_0_obj' and valid_mdb'
    and (\<lambda>s. case ep of Some x \<Rightarrow> ep_at' x s | _ \<Rightarrow> True)
    and case_option \<top> valid_ipc_buffer_ptr' recv_buf
    and transferCaps_srcs caps'
    and (\<lambda>s. length caps' \<le> msgMaxExtraCaps))
   (transfer_caps info caps ep receiver recv_buf)
   (transferCaps info' caps' ep receiver recv_buf)"
  apply (simp add: transfer_caps_def transferCaps_def
                   getThreadCSpaceRoot)
  apply (rule corres_assume_pre)
  apply (rule corres_guard_imp)
    apply (rule corres_split [OF _ get_recv_slot_corres]) 
      apply (rule_tac x=recv_buf in option_corres)
       apply (rule_tac P=\<top> and P'=\<top> in corres_inst)
       apply (case_tac info, simp)
      apply simp
      apply (rule corres_rel_imp, rule tc_loop_corres,
             simp_all add: split_def)[1]
      apply (case_tac info, simp)
     apply (wp hoare_vcg_all_lift get_rs_cte_at static_imp_wp
                | simp only: ball_conj_distrib)+
   apply (simp add: cte_map_def tcb_cnode_index_def split_def)
   apply (clarsimp simp: valid_pspace'_def valid_ipc_buffer_ptr'_def2
                        split_def
                  cong: option.case_cong)
   apply (drule(1) bspec)
   apply (clarsimp simp:cte_wp_at_caps_of_state)
   apply (frule(1) Invariants_AI.caps_of_state_valid)
   apply (fastforce simp:valid_cap_def)
  apply (cases info)
  apply (clarsimp simp: msg_max_extra_caps_def valid_message_info_def 
                        max_ipc_words msg_max_length_def
                        msgMaxExtraCaps_def msgExtraCapBits_def
                        shiftL_nat valid_pspace'_def)
  apply (drule(1) bspec)
  apply (clarsimp simp:cte_wp_at_ctes_of)
  apply (case_tac cte,clarsimp)
  apply (frule(1) ctes_of_valid_cap')
  apply (fastforce simp:valid_cap'_def)
  done

crunch typ_at'[wp]: transferCaps "\<lambda>s. P (typ_at' T p s)"

lemmas transferCaps_typ_ats[wp] = typ_at_lifts [OF transferCaps_typ_at']

lemma capRights_Null_eq [simp]:
  "(maskCapRights R cap = NullCap) = (cap = NullCap)"
  apply (cases cap)
  apply (simp_all add: Let_def maskCapRights_def isCap_simps)
  apply (simp add: ARM_H.maskCapRights_def
            split: arch_capability.split)
  done

lemma updateCapData_not_nullD:
  "updateCapData p d cap \<noteq> NullCap \<Longrightarrow> cap \<noteq> NullCap"
  apply (cases cap)
  by (simp_all add: updateCapData_def isCap_simps)

lemma cte_wp_at_orth':
  "\<lbrakk> cte_wp_at' (\<lambda>c. P c) p s; cte_wp_at' (\<lambda>c. \<not> P c) p s \<rbrakk> \<Longrightarrow> False"
  unfolding cte_wp_at'_def
  by clarsimp

declare maskCapRights_Reply [simp]

lemma isIRQControlCap_mask [simp]:
  "isIRQControlCap (maskCapRights R c) = isIRQControlCap c"
  apply (case_tac c)
            apply (clarsimp simp: isCap_simps maskCapRights_def Let_def)+
      apply (rename_tac arch_capability)
      apply (case_tac arch_capability)
          apply (clarsimp simp: isCap_simps ARM_H.maskCapRights_def
                                maskCapRights_def Let_def)+
  done

lemma isPageCap_maskCapRights[simp]:
" isArchCap isPageCap (RetypeDecls_H.maskCapRights R c) = isArchCap isPageCap c"
  apply (case_tac c; simp add: isCap_simps isArchCap_def maskCapRights_def)
  apply (rename_tac arch_capability)
  apply (case_tac arch_capability; simp add: isCap_simps ARM_H.maskCapRights_def)
  done
   
lemma capReplyMaster_mask[simp]:
  "isReplyCap c \<Longrightarrow> capReplyMaster (maskCapRights R c) = capReplyMaster c"
  by (clarsimp simp: isCap_simps maskCapRights_def)

lemma is_derived_mask' [simp]:
  "is_derived' m p (maskCapRights R c) = is_derived' m p c"
  apply (rule ext)
  apply (simp add: is_derived'_def badge_derived'_def)
  done

lemma sameRegionAs_update:
  "\<lbrakk> updateCapData P d cap \<noteq> NullCap; sameRegionAs cap' cap\<rbrakk>
  \<Longrightarrow> sameRegionAs cap' (updateCapData P d cap)"
  by (drule updateCapData_Master, simp add: sameRegionAs_def2)

lemma updateCapData_ordering:
  "\<lbrakk> (x, capBadge cap) \<in> capBadge_ordering P; updateCapData p d cap \<noteq> NullCap \<rbrakk>
    \<Longrightarrow> (x, capBadge (updateCapData p d cap)) \<in> capBadge_ordering P"
  apply (cases cap, simp_all add: updateCapData_def isCap_simps Let_def
                                  capBadge_def ARM_H.updateCapData_def
                           split: if_split_asm)
   apply fastforce+
  done

lemma updateCapData_capReplyMaster:
  "isReplyCap cap \<Longrightarrow> capReplyMaster (updateCapData p d cap) = capReplyMaster cap"
  by (clarsimp simp: isCap_simps updateCapData_def split del: if_split)

lemma updateCapData_is_Reply[simp]:
  "(updateCapData p d cap = ReplyCap x y) = (cap = ReplyCap x y)"
  by (rule ccontr,
      clarsimp simp: isCap_simps updateCapData_def Let_def
                     ARM_H.updateCapData_def
          split del: if_split
              split: if_split_asm)

lemma updateCapDataIRQ:
  "updateCapData p d cap \<noteq> NullCap \<Longrightarrow> 
  isIRQControlCap (updateCapData p d cap) = isIRQControlCap cap"
  apply (cases cap, simp_all add: updateCapData_def isCap_simps Let_def
                                  ARM_H.updateCapData_def
                           split: if_split_asm)
  done

lemma updateCapData_vsCapRef[simp]:
  "vsCapRef (updateCapData pr D c) = vsCapRef c"
  by (rule ccontr,
      clarsimp simp: isCap_simps updateCapData_def Let_def
                     ARM_H.updateCapData_def
                     vsCapRef_def
          split del: if_split
              split: if_split_asm)

lemma isPageCap_updateCapData[simp]:
"isArchCap isPageCap (updateCapData pr D c) = isArchCap isPageCap c"
  apply (case_tac c; simp add:updateCapData_def isCap_simps isArchCap_def)
   apply (rename_tac arch_capability)
   apply (case_tac arch_capability; simp add: ARM_H.updateCapData_def isCap_simps isArchCap_def)
  apply (clarsimp split:capability.splits simp:Let_def)
  done

lemma updateCapData_derived:
  "\<lbrakk> updateCapData pr D c \<noteq> NullCap; is_derived' m p c c' \<rbrakk> \<Longrightarrow>
  is_derived' m p (updateCapData pr D c) c'"
  apply (frule updateCapData_Master,
         clarsimp simp add: is_derived'_def badge_derived'_def updateCapDataIRQ)
  apply (rule conjI, erule(1) updateCapData_ordering)
  apply (clarsimp simp add: isCap_simps updateCapData_capReplyMaster)
  apply auto
  done

lemma lookup_cap_to'[wp]:
  "\<lbrace>\<top>\<rbrace> lookupCap t cref \<lbrace>\<lambda>rv s. \<forall>r\<in>cte_refs' rv (irq_node' s). ex_cte_cap_to' r s\<rbrace>,-"
  by (simp add: lookupCap_def lookupCapAndSlot_def | wp)+

lemma grs_cap_to'[wp]:
  "\<lbrace>\<top>\<rbrace> getReceiveSlots t buf \<lbrace>\<lambda>rv s. \<forall>x \<in> set rv. ex_cte_cap_to' x s\<rbrace>"
  apply (cases buf; simp add: getReceiveSlots_def split_def unlessE_def)
   apply (wp, simp)
  apply (wp nothingOnFailure_wp | simp | rule hoare_drop_imps)+
  done

lemma grs_length'[wp]:
  "\<lbrace>\<lambda>s. 1 \<le> n\<rbrace> getReceiveSlots receiver recv_buf \<lbrace>\<lambda>rv s. length rv \<le> n\<rbrace>"
  apply (simp add: getReceiveSlots_def split_def unlessE_def)
  apply (rule hoare_pre)
   apply (wp | wpc | simp)+
  done

lemma sameObjectAs_maskCapRights[simp]:
  "sameObjectAs (maskCapRights msk cap) cap' = sameObjectAs cap cap'"
  by (simp add: sameObjectAs_def2)

lemma transferCaps_invs' [wp]:
  "\<lbrace>invs' and transferCaps_srcs caps\<rbrace> 
    transferCaps mi caps ep receiver recv_buf
   \<lbrace>\<lambda>rv. invs'\<rbrace>"
  apply (simp add: transferCaps_def Let_def split_def)
  apply (wp get_rs_cte_at' hoare_vcg_const_Ball_lift
             | wpcw | clarsimp)+
  done

lemma get_mrs_inv'[wp]:
  "\<lbrace>P\<rbrace> getMRs t buf info \<lbrace>\<lambda>rv. P\<rbrace>"
  by (simp add: getMRs_def load_word_offs_def getRegister_def
          | wp dmo_inv' loadWord_inv mapM_wp'
            asUser_inv det_mapM[where S=UNIV] | wpc)+


lemma copyMRs_typ_at':
  "\<lbrace>\<lambda>s. P (typ_at' T p s)\<rbrace> copyMRs s sb r rb n \<lbrace>\<lambda>rv s. P (typ_at' T p s)\<rbrace>"
  by (simp add: copyMRs_def | wp mapM_wp [where S=UNIV, simplified] | wpc)+

lemmas copyMRs_typ_at_lifts[wp] = typ_at_lifts [OF copyMRs_typ_at']

lemma copy_mrs_invs'[wp]:
  "\<lbrace> invs' and tcb_at' s and tcb_at' r \<rbrace> copyMRs s sb r rb n \<lbrace>\<lambda>rv. invs' \<rbrace>"
  including no_pre
  apply (simp add: copyMRs_def)  
  apply (wp dmo_invs' no_irq_mapM no_irq_storeWord|
         simp add: split_def)
   apply (case_tac sb, simp_all)[1]
    apply wp+
   apply (case_tac rb, simp_all)[1]
   apply (wp mapM_wp dmo_invs' no_irq_mapM no_irq_storeWord no_irq_loadWord)
   apply blast
  apply (rule hoare_strengthen_post)
   apply (rule mapM_wp)
    apply (wp | simp | blast)+
  done

crunch aligned'[wp]: transferCaps pspace_aligned'
  (wp: crunch_wps simp: zipWithM_x_mapM)
crunch distinct'[wp]: transferCaps pspace_distinct'
  (wp: crunch_wps simp: zipWithM_x_mapM)

crunch aligned'[wp]: setMRs pspace_aligned'
  (wp: crunch_wps simp: crunch_simps ignore: getObject)
crunch distinct'[wp]: setMRs pspace_distinct'
  (wp: crunch_wps simp: crunch_simps ignore: getObject)
crunch aligned'[wp]: copyMRs pspace_aligned'
  (wp: crunch_wps simp: crunch_simps ignore: getObject wp: crunch_wps)
crunch distinct'[wp]: copyMRs pspace_distinct'
  (wp: crunch_wps simp: crunch_simps ignore: getObject wp: crunch_wps)
crunch aligned'[wp]: setMessageInfo pspace_aligned'
  (wp: crunch_wps simp: crunch_simps ignore: getObject)
crunch distinct'[wp]: setMessageInfo pspace_distinct'
  (wp: crunch_wps simp: crunch_simps ignore: getObject)

crunch valid_objs'[wp]: storeWordUser valid_objs'
crunch valid_pspace'[wp]: storeWordUser valid_pspace'

lemma set_mrs_valid_objs' [wp]:
  "\<lbrace>valid_objs'\<rbrace> setMRs t a msgs \<lbrace>\<lambda>rv. valid_objs'\<rbrace>"
  apply (simp add: setMRs_def zipWithM_x_mapM split_def)
  apply (wp asUser_valid_objs crunch_wps)  
  done

crunch valid_objs'[wp]: copyMRs valid_objs'
  (wp: crunch_wps simp: crunch_simps)

crunch valid_queues'[wp]: asUser "Invariants_H.valid_queues'"
  (simp: crunch_simps wp: hoare_drop_imps)


lemma setMRs_invs_bits[wp]:
  "\<lbrace>valid_pspace'\<rbrace> setMRs t buf mrs \<lbrace>\<lambda>rv. valid_pspace'\<rbrace>"
  "\<lbrace>\<lambda>s. sch_act_wf (ksSchedulerAction s) s\<rbrace>
     setMRs t buf mrs \<lbrace>\<lambda>rv s. sch_act_wf (ksSchedulerAction s) s\<rbrace>"
  "\<lbrace>\<lambda>s. weak_sch_act_wf (ksSchedulerAction s) s\<rbrace>
     setMRs t buf mrs \<lbrace>\<lambda>rv s. weak_sch_act_wf (ksSchedulerAction s) s\<rbrace>"
  "\<lbrace>Invariants_H.valid_queues\<rbrace> setMRs t buf mrs \<lbrace>\<lambda>rv. Invariants_H.valid_queues\<rbrace>"
  "\<lbrace>valid_queues'\<rbrace> setMRs t buf mrs \<lbrace>\<lambda>rv. valid_queues'\<rbrace>"
  "\<lbrace>\<lambda>s. P (state_refs_of' s)\<rbrace>
     setMRs t buf mrs
   \<lbrace>\<lambda>rv s. P (state_refs_of' s)\<rbrace>"
  "\<lbrace>if_live_then_nonz_cap'\<rbrace> setMRs t buf mrs \<lbrace>\<lambda>rv. if_live_then_nonz_cap'\<rbrace>"
  "\<lbrace>ex_nonz_cap_to' p\<rbrace> setMRs t buf mrs \<lbrace>\<lambda>rv. ex_nonz_cap_to' p\<rbrace>"
  "\<lbrace>cur_tcb'\<rbrace> setMRs t buf mrs \<lbrace>\<lambda>rv. cur_tcb'\<rbrace>"
  "\<lbrace>if_unsafe_then_cap'\<rbrace> setMRs t buf mrs \<lbrace>\<lambda>rv. if_unsafe_then_cap'\<rbrace>"
  by (simp add: setMRs_def zipWithM_x_mapM split_def storeWordUser_def | wp crunch_wps)+

crunch no_0_obj'[wp]: setMRs no_0_obj'
  (wp: crunch_wps ignore: getObject simp: crunch_simps)

lemma copyMRs_invs_bits[wp]:
  "\<lbrace>valid_pspace'\<rbrace> copyMRs s sb r rb n \<lbrace>\<lambda>rv. valid_pspace'\<rbrace>"
  "\<lbrace>\<lambda>s. sch_act_wf (ksSchedulerAction s) s\<rbrace> copyMRs s sb r rb n
      \<lbrace>\<lambda>rv s. sch_act_wf (ksSchedulerAction s) s\<rbrace>"
  "\<lbrace>Invariants_H.valid_queues\<rbrace> copyMRs s sb r rb n \<lbrace>\<lambda>rv. Invariants_H.valid_queues\<rbrace>"
  "\<lbrace>valid_queues'\<rbrace> copyMRs s sb r rb n \<lbrace>\<lambda>rv. valid_queues'\<rbrace>"
  "\<lbrace>\<lambda>s. P (state_refs_of' s)\<rbrace>
      copyMRs s sb r rb n
   \<lbrace>\<lambda>rv s. P (state_refs_of' s)\<rbrace>"
  "\<lbrace>if_live_then_nonz_cap'\<rbrace> copyMRs s sb r rb n \<lbrace>\<lambda>rv. if_live_then_nonz_cap'\<rbrace>"
  "\<lbrace>ex_nonz_cap_to' p\<rbrace> copyMRs s sb r rb n \<lbrace>\<lambda>rv. ex_nonz_cap_to' p\<rbrace>"
  "\<lbrace>cur_tcb'\<rbrace> copyMRs s sb r rb n \<lbrace>\<lambda>rv. cur_tcb'\<rbrace>"
  "\<lbrace>if_unsafe_then_cap'\<rbrace> copyMRs s sb r rb n \<lbrace>\<lambda>rv. if_unsafe_then_cap'\<rbrace>"
  by (simp add: copyMRs_def  storeWordUser_def | wp mapM_wp' | wpc)+

crunch no_0_obj'[wp]: copyMRs no_0_obj'
  (wp: crunch_wps ignore: getObject simp: crunch_simps)

lemma valid_pspace_mdb_strengthen:
  "valid_pspace' s \<longrightarrow> valid_mdb' s"
  by clarsimp

lemma mi_map_length[simp]: "msgLength (message_info_map mi) = mi_length mi"
  by (cases mi, simp)

crunch cte_wp_at'[wp]: copyMRs "cte_wp_at' P p"
  (wp: crunch_wps)

lemma lookupExtraCaps_srcs[wp]:
  "\<lbrace>\<top>\<rbrace> lookupExtraCaps thread buf info \<lbrace>transferCaps_srcs\<rbrace>,-"
  apply (simp add: lookupExtraCaps_def lookupCapAndSlot_def
                   split_def lookupSlotForThread_def
                   getSlotCap_def)
  apply (wp mapME_set[where R=\<top>] getCTE_wp')
       apply (rule_tac P=\<top> in hoare_trivE_R)
       apply (simp add: cte_wp_at_ctes_of)
      apply (wp | simp)+
  done

crunch inv[wp]: lookupExtraCaps "P"
  (wp: crunch_wps mapME_wp' simp: crunch_simps ignore: mapME)

lemma invs_mdb_strengthen':
  "invs' s \<longrightarrow> valid_mdb' s" by auto

lemma lookupExtraCaps_length:
  "\<lbrace>\<lambda>s. unat (msgExtraCaps mi) \<le> n\<rbrace> lookupExtraCaps thread send_buf mi \<lbrace>\<lambda>rv s. length rv \<le> n\<rbrace>,-"
  apply (simp add: lookupExtraCaps_def getExtraCPtrs_def)
  apply (rule hoare_pre)
   apply (wp mapME_length | wpc)+
  apply (clarsimp simp: upto_enum_step_def Suc_unat_diff_1 word_le_sub1)
  done

lemma getMessageInfo_msgExtraCaps[wp]:
  "\<lbrace>\<top>\<rbrace> getMessageInfo t \<lbrace>\<lambda>rv s. unat (msgExtraCaps rv) \<le> msgMaxExtraCaps\<rbrace>"
  apply (simp add: getMessageInfo_def)
  apply wp
   apply (simp add: messageInfoFromWord_def Let_def msgMaxExtraCaps_def
                    shiftL_nat)
   apply (subst nat_le_Suc_less_imp)
    apply (rule unat_less_power)
     apply (simp add: word_bits_def msgExtraCapBits_def)
    apply (rule and_mask_less'[unfolded mask_2pm1])
    apply (simp add: msgExtraCapBits_def)
   apply wp+
  done

lemma lcs_corres:  
  "cptr = to_bl cptr' \<Longrightarrow> 
  corres (lfr \<oplus> (\<lambda>a b. cap_relation (fst a) (fst b) \<and> snd b = cte_map (snd a)))
    (valid_objs and pspace_aligned and tcb_at thread)
    (valid_objs' and pspace_distinct' and pspace_aligned' and tcb_at' thread)
    (lookup_cap_and_slot thread cptr) (lookupCapAndSlot thread cptr')"
  unfolding lookup_cap_and_slot_def lookupCapAndSlot_def
  apply (simp add: liftE_bindE split_def)
  apply (rule corres_guard_imp)
    apply (rule_tac r'="\<lambda>rv rv'. rv' = cte_map (fst rv)"
                 in corres_splitEE)
       apply (rule corres_split[OF _ getSlotCap_corres])
          apply (rule corres_returnOkTT, simp)
         apply simp
        apply wp+
      apply (rule corres_rel_imp, rule lookup_slot_corres)
      apply (simp add: split_def)
     apply (wp | simp add: liftE_bindE[symmetric])+
  done

lemma lec_corres:
  "\<lbrakk> info' = message_info_map info; buffer = buffer'\<rbrakk> \<Longrightarrow>
  corres (fr \<oplus> list_all2 (\<lambda>x y. cap_relation (fst x) (fst y) \<and> snd y = cte_map (snd x)))
   (valid_objs and pspace_aligned and tcb_at thread and (\<lambda>_. valid_message_info info))
   (valid_objs' and pspace_distinct' and pspace_aligned' and tcb_at' thread
        and case_option \<top> valid_ipc_buffer_ptr' buffer')
   (lookup_extra_caps thread buffer info) (lookupExtraCaps thread buffer' info')"
  unfolding lookupExtraCaps_def lookup_extra_caps_def
  apply (rule corres_gen_asm)
  apply (cases "mi_extra_caps info = 0")
   apply (cases info)
   apply (simp add: Let_def returnOk_def getExtraCPtrs_def
                    liftE_bindE upto_enum_step_def mapM_def
                    sequence_def doMachineOp_return mapME_Nil
             split: option.split)
  apply (cases info)
  apply (rename_tac w1 w2 w3 w4)
  apply (simp add: Let_def liftE_bindE)
  apply (cases buffer')
   apply (simp add: getExtraCPtrs_def mapME_Nil)
   apply (rule corres_returnOk)
   apply simp
  apply (simp add: msgLengthBits_def msgMaxLength_def word_size field_simps
                   getExtraCPtrs_def upto_enum_step_def upto_enum_word
                   word_size_def msg_max_length_def liftM_def
                   Suc_unat_diff_1 word_le_sub1 mapM_map_simp
                   upt_lhs_sub_map[where x=buffer_cptr_index]
                   wordSize_def wordBits_def
              del: upt.simps)
  apply (rule corres_guard_imp)
    apply (rule corres_split')

       apply (rule_tac S = "\<lambda>x y. x = y \<and> x < unat w2"
               in corres_mapM_list_all2
         [where Q = "\<lambda>_. valid_objs and pspace_aligned and tcb_at thread" and r = "op ="
            and Q' = "\<lambda>_. valid_objs' and pspace_aligned' and pspace_distinct' and tcb_at' thread
              and case_option \<top> valid_ipc_buffer_ptr' buffer'" and r'="op =" ])
            apply simp
           apply simp
          apply simp
          apply (rule corres_guard_imp)
            apply (rule load_word_offs_corres')
             apply (clarsimp simp: buffer_cptr_index_def msg_max_length_def
                                   max_ipc_words valid_message_info_def
                                   msg_max_extra_caps_def word_le_nat_alt)
            apply (simp add: buffer_cptr_index_def msg_max_length_def)
           apply simp
          apply simp
         apply (simp add: load_word_offs_word_def)
         apply (wp | simp)+
       apply (subst list_all2_same)
       apply (clarsimp simp: max_ipc_words field_simps)
      apply (simp add: mapME_def, fold mapME_def)[1]
      apply (rule corres_mapME [where S = Id and r'="(\<lambda>x y. cap_relation (fst x) (fst y) \<and> snd y = cte_map (snd x))"])
            apply simp
           apply simp
          apply simp
          apply (rule corres_cap_fault [OF lcs_corres])
          apply simp
         apply simp
         apply (wp | simp)+
      apply (simp add: set_zip_same Int_lower1)
     apply (wp mapM_wp [OF _ subset_refl] | simp)+
  done

crunch ctes_of[wp]: copyMRs "\<lambda>s. P (ctes_of s)"
  (ignore: threadSet setObject getObject
       wp: threadSet_ctes_of crunch_wps)

lemma copyMRs_valid_mdb[wp]:
  "\<lbrace>valid_mdb'\<rbrace> copyMRs t buf t' buf' n \<lbrace>\<lambda>rv. valid_mdb'\<rbrace>"
  by (simp add: valid_mdb'_def copyMRs_ctes_of)

lemma do_normal_transfer_corres:
  "corres dc 
  (tcb_at sender and tcb_at receiver and (pspace_aligned:: det_state \<Rightarrow> bool)
   and valid_objs and cur_tcb and valid_mdb and valid_list and pspace_distinct
   and (\<lambda>s. case ep of Some x \<Rightarrow> ep_at x s | _ \<Rightarrow> True)
   and case_option \<top> in_user_frame send_buf
   and case_option \<top> in_user_frame recv_buf)
  (tcb_at' sender and tcb_at' receiver and valid_objs'
   and pspace_aligned' and pspace_distinct' and cur_tcb'
   and valid_mdb' and no_0_obj'
   and (\<lambda>s. case ep of Some x \<Rightarrow> ep_at' x s | _ \<Rightarrow> True)
   and case_option \<top> valid_ipc_buffer_ptr' send_buf
   and case_option \<top> valid_ipc_buffer_ptr' recv_buf)
  (do_normal_transfer sender send_buf ep badge can_grant receiver recv_buf)
  (doNormalTransfer sender send_buf ep badge can_grant receiver recv_buf)"
  apply (simp add: do_normal_transfer_def doNormalTransfer_def)
  apply (rule corres_guard_imp)

    apply (rule corres_split_mapr [OF _ get_mi_corres])
      apply (rule_tac F="valid_message_info mi" in corres_gen_asm)
      apply (rule_tac r'="list_all2 (\<lambda>x y. cap_relation (fst x) (fst y) \<and> snd y = cte_map (snd x))"
                  in corres_split)
         prefer 2
         apply (rule corres_if[OF refl])
          apply (rule corres_split_catch)
             apply (rule corres_trivial, simp)
            apply (rule lec_corres, simp+)
           apply wp+
         apply (rule corres_trivial, simp)
        apply simp
        apply (rule corres_split_eqr [OF _ copy_mrs_corres])
          apply (rule corres_split [OF _ tc_corres])
              apply (rename_tac mi' mi'')
              apply (rule_tac F="mi_label mi' = mi_label mi"
                        in corres_gen_asm)
              apply (rule corres_split_nor [OF _ set_mi_corres])
                 apply (simp add: badge_register_def badgeRegister_def)
                 apply (fold dc_def)
                 apply (rule user_setreg_corres)
                apply (case_tac mi', clarsimp)
               apply wp
             apply simp+
           apply ((wp valid_case_option_post_wp hoare_vcg_const_Ball_lift
                     hoare_case_option_wp
                     hoare_valid_ipc_buffer_ptr_typ_at' copyMRs_typ_at'
                     hoare_vcg_const_Ball_lift lookupExtraCaps_length
                   | simp add: if_apply_def2)+)
      apply (wp static_imp_wp | strengthen valid_msg_length_strengthen)+
   apply clarsimp
  apply auto
  done

lemma corres_liftE_lift:
  "corres r1 P P' m m' \<Longrightarrow>
  corres (f1 \<oplus> r1) P P' (liftE m) (withoutFailure m')"
  by simp

lemmas corres_ipc_thread_helper = 
  corres_split_eqrE [OF _  corres_liftE_lift [OF gct_corres]]

lemmas corres_ipc_info_helper = 
  corres_split_maprE [where f = message_info_map, OF _
                                corres_liftE_lift [OF get_mi_corres]]

crunch typ_at'[wp]: doNormalTransfer "\<lambda>s. P (typ_at' T p s)"

lemmas doNormal_lifts[wp] = typ_at_lifts [OF doNormalTransfer_typ_at']

lemma doNormal_invs'[wp]:
  "\<lbrace>tcb_at' sender and tcb_at' receiver and invs'\<rbrace>
    doNormalTransfer sender send_buf ep badge
             can_grant receiver recv_buf \<lbrace>\<lambda>r. invs'\<rbrace>"
  apply (simp add: doNormalTransfer_def)
  apply (wp hoare_vcg_const_Ball_lift | simp)+
  done

crunch aligned'[wp]: doNormalTransfer pspace_aligned'
  (wp: crunch_wps)
crunch distinct'[wp]: doNormalTransfer pspace_distinct'
  (wp: crunch_wps)

lemma transferCaps_urz[wp]:
  "\<lbrace>untyped_ranges_zero' and valid_pspace'
      and (\<lambda>s. (\<forall>x\<in>set caps. cte_wp_at' (\<lambda>cte. fst x \<noteq> capability.NullCap \<longrightarrow> cteCap cte = fst x) (snd x) s))\<rbrace>
    transferCaps tag caps ep receiver recv_buf
  \<lbrace>\<lambda>r. untyped_ranges_zero'\<rbrace>"
  apply (simp add: transferCaps_def)
  apply (rule hoare_pre)
   apply (wp hoare_vcg_all_lift hoare_vcg_const_imp_lift
      | wpc
      | simp add: ball_conj_distrib)+
  apply clarsimp
  done

crunch gsUntypedZeroRanges[wp]: doNormalTransfer "\<lambda>s. P (gsUntypedZeroRanges s)"
  (wp: crunch_wps transferCapsToSlots_pres1 ignore: constOnFailure)

lemmas asUser_urz = untyped_ranges_zero_lift[OF asUser_gsUntypedZeroRanges]

crunch urz[wp]: doNormalTransfer "untyped_ranges_zero'"
  (ignore: asUser wp: crunch_wps asUser_urz hoare_vcg_const_Ball_lift)

lemma msgFromLookupFailure_map[simp]:
  "msgFromLookupFailure (lookup_failure_map lf)
     = msg_from_lookup_failure lf"
  by (cases lf, simp_all add: lookup_failure_map_def msgFromLookupFailure_def)

lemma getRestartPCs_corres:
  "corres op = (tcb_at t) (tcb_at' t)
                 (as_user t getRestartPC) (asUser t getRestartPC)"
  apply (rule corres_as_user')
  apply (rule corres_Id, simp, simp)
  apply (rule no_fail_getRestartPC)
  done

lemma user_mapM_getRegister_corres:
  "corres op = (tcb_at t) (tcb_at' t)
     (as_user t (mapM getRegister regs))
     (asUser t (mapM getRegister regs))"
  apply (rule corres_as_user')
  apply (rule corres_Id [OF refl refl])
  apply (rule no_fail_mapM)
  apply (simp add: getRegister_def)
  done

lemma make_arch_fault_msg_corres:
  "corres op = (tcb_at t) (tcb_at' t)
  (make_arch_fault_msg f t)
  (makeArchFaultMessage (arch_fault_map f) t)"
  apply (cases f, clarsimp simp: makeArchFaultMessage_def split: arch_fault.split)
  apply (rule corres_guard_imp)
    apply (rule corres_split_eqr[OF _ getRestartPCs_corres])
      apply (rule corres_trivial, simp add: arch_fault_map_def)
     apply (wp+, auto)
  done

lemma mk_ft_msg_corres:
  "corres op = (tcb_at t) (tcb_at' t)
     (make_fault_msg ft t)
     (makeFaultMessage (fault_map ft) t)"
  apply (cases ft, simp_all add: makeFaultMessage_def split del: if_split)
     apply (rule corres_guard_imp)
       apply (rule corres_split_eqr [OF _ getRestartPCs_corres])
         apply (rule corres_trivial, simp add: fromEnum_def enum_bool)
        apply (wp | simp)+
    apply (simp add: ARM_H.syscallMessage_def)
    apply (rule corres_guard_imp)
      apply (rule corres_split_eqr [OF _ user_mapM_getRegister_corres])
        apply (rule corres_trivial, simp)
       apply (wp | simp)+
   apply (simp add: ARM_H.exceptionMessage_def)
   apply (rule corres_guard_imp)
     apply (rule corres_split_eqr [OF _ user_mapM_getRegister_corres])
       apply (rule corres_trivial, simp)
      apply (wp | simp)+
  apply (rule make_arch_fault_msg_corres)
  done

lemma makeFaultMessage_inv[wp]:
  "\<lbrace>P\<rbrace> makeFaultMessage ft t \<lbrace>\<lambda>rv. P\<rbrace>"
  apply (cases ft, simp_all add: makeFaultMessage_def)
     apply (wp asUser_inv mapM_wp' det_mapM[where S=UNIV]
               det_getRestartPC getRestartPC_inv
             | clarsimp simp: getRegister_def makeArchFaultMessage_def
                        split: arch_fault.split)+
  done

lemmas threadget_fault_corres =
          threadget_corres [where r = fault_rel_optionation
                              and f = tcb_fault and f' = tcbFault,
                            simplified tcb_relation_def, simplified]

lemma do_fault_transfer_corres:
  "corres dc
    (obj_at (\<lambda>ko. \<exists>tcb ft. ko = TCB tcb \<and> tcb_fault tcb = Some ft) sender
     and tcb_at receiver and case_option \<top> in_user_frame recv_buf)
    (tcb_at' sender and tcb_at' receiver and
     case_option \<top> valid_ipc_buffer_ptr' recv_buf)
    (do_fault_transfer badge sender receiver recv_buf)
    (doFaultTransfer badge sender receiver recv_buf)"
  apply (clarsimp simp: do_fault_transfer_def doFaultTransfer_def split_def
                        ARM_H.badgeRegister_def badge_register_def)
  apply (rule_tac Q="\<lambda>fault. K (\<exists>f. fault = Some f) and
                             tcb_at sender and tcb_at receiver and
                             case_option \<top> in_user_frame recv_buf"
              and Q'="\<lambda>fault'. tcb_at' sender and tcb_at' receiver and
                               case_option \<top> valid_ipc_buffer_ptr' recv_buf"
               in corres_split')
     apply (rule corres_guard_imp)
       apply (rule threadget_fault_corres)
      apply (clarsimp simp: obj_at_def is_tcb)+
    apply (rule corres_assume_pre)
    apply (fold assert_opt_def | unfold haskell_fail_def)+
    apply (rule corres_assert_opt_assume)
     apply (clarsimp split: option.splits
                      simp: fault_rel_optionation_def assert_opt_def
                            map_option_case)
     defer
     defer
     apply (clarsimp simp: fault_rel_optionation_def)
    apply (wp thread_get_wp)
    apply (clarsimp simp: obj_at_def is_tcb)
   apply wp
   apply (rule corres_guard_imp)
      apply (rule corres_split_eqr [OF _ mk_ft_msg_corres])
        apply (rule corres_split_eqr [OF _ set_mrs_corres [OF refl]])
          apply (rule corres_split_nor [OF _ set_mi_corres])
             apply (rule user_setreg_corres)
            apply simp
           apply (wp | simp)+
   apply (rule corres_guard_imp)
      apply (rule corres_split_eqr [OF _ mk_ft_msg_corres])
        apply (rule corres_split_eqr [OF _ set_mrs_corres [OF refl]])
          apply (rule corres_split_nor [OF _ set_mi_corres])
             apply (rule user_setreg_corres)
            apply simp
           apply (wp | simp)+
  done

lemma doFaultTransfer_invs[wp]:
  "\<lbrace>invs' and tcb_at' receiver\<rbrace>
      doFaultTransfer badge sender receiver recv_buf
   \<lbrace>\<lambda>rv. invs'\<rbrace>"
  by (simp add: doFaultTransfer_def split_def | wp
    | clarsimp split: option.split)+

lemma corres_return_ignore:
  "\<lbrakk> m = return x; corres r P Q (f x) g \<rbrakk> \<Longrightarrow> corres r P Q (m >>= f) g"
  by simp

lemma invs_mdb_absorb' [simp]:
  "(invs' s \<and> valid_mdb' s) = invs' s"
  by (simp add: invs'_def valid_state'_def valid_pspace'_def conj_comms)

lemma invs_mdb_absorb'_ac [simp]:
  "(invs' s \<and> valid_mdb' s \<and> P s) = (invs' s \<and> P s)"
  by (simp add: invs'_def valid_state'_def valid_pspace'_def conj_comms)

lemma lookupIPCBuffer_valid_ipc_buffer [wp]:
  "\<lbrace>valid_objs'\<rbrace> VSpace_H.lookupIPCBuffer b s \<lbrace>case_option \<top> valid_ipc_buffer_ptr'\<rbrace>"
  unfolding lookupIPCBuffer_def ARM_H.lookupIPCBuffer_def
  apply (simp add: Let_def getSlotCap_def getThreadBufferSlot_def
                   locateSlot_conv threadGet_def comp_def)
  apply (wp getCTE_wp getObject_tcb_wp | wpc)+
  apply (clarsimp simp del: imp_disjL)
  apply (drule obj_at_ko_at')
  apply (clarsimp simp del: imp_disjL)
  apply (rule_tac x = ko in exI)
  apply (frule ko_at_cte_ipcbuffer)
  apply (clarsimp simp: cte_wp_at_ctes_of simp del: imp_disjL)
  apply (clarsimp simp: valid_ipc_buffer_ptr'_def)
  apply (frule (1) ko_at_valid_objs')
   apply (clarsimp simp: projectKO_opts_defs split: kernel_object.split_asm)
  apply (clarsimp simp add: valid_obj'_def valid_tcb'_def 
                            isCap_simps cte_level_bits_def field_simps)
  apply (drule bspec [OF _ ranI [where a = "0x40"]])
   apply simp
  apply (clarsimp simp add: valid_cap'_def)
  apply (rule conjI)
   apply (rule aligned_add_aligned)
     apply (clarsimp simp add: capAligned_def)
     apply assumption
    apply (erule is_aligned_andI1)
   apply (case_tac xd, simp_all add: msg_align_bits)[1]
  apply (clarsimp simp: capAligned_def)
  apply (drule_tac x = 
    "(tcbIPCBuffer ko && mask (pageBitsForSize xd))  >> pageBits" in spec)
  apply (subst(asm) mult.commute mult.left_commute, subst(asm) shiftl_t2n[symmetric])
  apply (simp add: shiftr_shiftl1)
  apply (subst (asm) mask_out_add_aligned)
   apply (erule is_aligned_weaken [OF _ pbfs_atleast_pageBits])
  apply (erule mp)
  apply (rule shiftr_less_t2n)
  apply (clarsimp simp: pbfs_atleast_pageBits)
  apply (rule and_mask_less')
  apply (simp add: word_bits_conv)
  done

lemma dit_corres:
  "corres dc
     (tcb_at s and tcb_at r and valid_objs and pspace_aligned
        and valid_list
        and pspace_distinct and valid_mdb and cur_tcb
        and (\<lambda>s. case ep of Some x \<Rightarrow> ep_at x s | _ \<Rightarrow> True))
     (tcb_at' s and tcb_at' r and valid_pspace' and cur_tcb'
        and (\<lambda>s. case ep of Some x \<Rightarrow> ep_at' x s | _ \<Rightarrow> True))
     (do_ipc_transfer s ep bg grt r)
     (doIPCTransfer s ep bg grt r)"
  apply (simp add: do_ipc_transfer_def doIPCTransfer_def)
  apply (rule_tac Q="%receiveBuffer sa. tcb_at s sa \<and> valid_objs sa \<and>
                       pspace_aligned sa \<and> tcb_at r sa \<and>
                       cur_tcb sa \<and> valid_mdb sa \<and> valid_list sa \<and> pspace_distinct sa \<and>
                       (case ep of None \<Rightarrow> True | Some x \<Rightarrow> ep_at x sa) \<and>
                       case_option (\<lambda>_. True) in_user_frame receiveBuffer sa \<and>
                       obj_at (\<lambda>ko. \<exists>tcb. ko = TCB tcb 
                                    (*\<exists>ft. tcb_fault tcb = Some ft*)) s sa"
               in corres_split')
     apply (rule corres_guard_imp)
       apply (rule lipcb_corres')
      apply auto[2]
    apply (rule corres_split' [OF _ _ thread_get_sp threadGet_inv])
     apply (rule corres_guard_imp)
       apply (rule threadget_fault_corres)
      apply simp
     defer
     apply (rule corres_guard_imp)
       apply (subst case_option_If)+
       apply (rule corres_if2)
         apply (simp add: fault_rel_optionation_def)
        apply (rule corres_split_eqr [OF _ lipcb_corres'])
          apply (simp add: dc_def[symmetric])
          apply (rule do_normal_transfer_corres)
         apply (wp | simp add: valid_pspace'_def)+
       apply (simp add: dc_def[symmetric])
       apply (rule do_fault_transfer_corres)
      apply (clarsimp simp: obj_at_def)
     apply (erule ignore_if)
    apply (wp|simp add: obj_at_def is_tcb valid_pspace'_def)+
  done


crunch ifunsafe[wp]: doIPCTransfer "if_unsafe_then_cap'"
  (wp: crunch_wps hoare_vcg_const_Ball_lift get_rs_cte_at' ignore: transferCapsToSlots
    simp: zipWithM_x_mapM ball_conj_distrib )
crunch iflive[wp]: doIPCTransfer "if_live_then_nonz_cap'"
  (wp: crunch_wps hoare_vcg_const_Ball_lift get_rs_cte_at' ignore: transferCapsToSlots 
    simp: zipWithM_x_mapM ball_conj_distrib )
lemma valid_pspace_valid_objs'[elim!]:
  "valid_pspace' s \<Longrightarrow> valid_objs' s"
  by (simp add: valid_pspace'_def)
crunch vp[wp]: doIPCTransfer "valid_pspace'"
  (wp: crunch_wps hoare_vcg_const_Ball_lift get_rs_cte_at' wp: transferCapsToSlots_vp simp:ball_conj_distrib )
crunch sch_act_wf[wp]: doIPCTransfer "\<lambda>s. sch_act_wf (ksSchedulerAction s) s"
  (wp: crunch_wps get_rs_cte_at' ignore: transferCapsToSlots  simp: zipWithM_x_mapM)
crunch vq[wp]: doIPCTransfer "Invariants_H.valid_queues"
  (wp: crunch_wps get_rs_cte_at' ignore: transferCapsToSlots  simp: zipWithM_x_mapM)
crunch vq'[wp]: doIPCTransfer "valid_queues'"
  (wp: crunch_wps get_rs_cte_at' ignore: transferCapsToSlots  simp: zipWithM_x_mapM)
crunch state_refs_of[wp]: doIPCTransfer "\<lambda>s. P (state_refs_of' s)"
  (wp: crunch_wps get_rs_cte_at' ignore: transferCapsToSlots  simp: zipWithM_x_mapM)
crunch ct[wp]: doIPCTransfer "cur_tcb'"
  (wp: crunch_wps get_rs_cte_at' ignore: transferCapsToSlots  simp: zipWithM_x_mapM)
crunch idle'[wp]: doIPCTransfer "valid_idle'"
  (wp: crunch_wps get_rs_cte_at' ignore: transferCapsToSlots  simp: zipWithM_x_mapM)

crunch typ_at'[wp]: doIPCTransfer "\<lambda>s. P (typ_at' T p s)"
  (wp: crunch_wps  simp: zipWithM_x_mapM)
lemmas dit'_typ_ats[wp] = typ_at_lifts [OF doIPCTransfer_typ_at']

crunch irq_node'[wp]: doIPCTransfer "\<lambda>s. P (irq_node' s)"
  (wp: crunch_wps simp: crunch_simps)

lemmas dit_irq_node'[wp]
    = valid_irq_node_lift [OF doIPCTransfer_irq_node' doIPCTransfer_typ_at']

crunch valid_arch_state'[wp]: doIPCTransfer "valid_arch_state'"
  (wp: crunch_wps simp: crunch_simps)

(* Levity: added (20090126 19:32:26) *)
declare asUser_global_refs' [wp]

lemma lec_valid_cap' [wp]:
  "\<lbrace>valid_objs'\<rbrace> lookupExtraCaps thread xa mi \<lbrace>\<lambda>rv s. (\<forall>x\<in>set rv. s \<turnstile>' fst x)\<rbrace>, -"
  apply (rule hoare_pre, rule hoare_post_imp_R)
    apply (rule hoare_vcg_conj_lift_R[where R=valid_objs' and S="\<lambda>_. valid_objs'"])
     apply (rule lookupExtraCaps_srcs)
    apply wp
   apply (clarsimp simp: cte_wp_at_ctes_of)
   apply (fastforce elim: ctes_of_valid')
  apply simp
  done

crunch objs'[wp]: doIPCTransfer "valid_objs'"
   (    wp: crunch_wps hoare_vcg_const_Ball_lift
            transferCapsToSlots_valid_objs
      simp: zipWithM_x_mapM ball_conj_distrib )

crunch global_refs'[wp]: doIPCTransfer "valid_global_refs'"
  (wp: crunch_wps hoare_vcg_const_Ball_lift threadSet_global_refsT
       transferCapsToSlots_valid_globals
      simp: zipWithM_x_mapM ball_conj_distrib)

declare asUser_irq_handlers' [wp]

crunch irq_handlers'[wp]: doIPCTransfer "valid_irq_handlers'"
  (wp: crunch_wps hoare_vcg_const_Ball_lift threadSet_irq_handlers'
       transferCapsToSlots_irq_handlers
       simp: zipWithM_x_mapM ball_conj_distrib )

crunch irq_states'[wp]: doIPCTransfer "valid_irq_states'"
  (wp: crunch_wps no_irq no_irq_mapM no_irq_storeWord no_irq_loadWord
       no_irq_case_option simp: crunch_simps zipWithM_x_mapM)

crunch pde_mappings'[wp]: doIPCTransfer "valid_pde_mappings'"
  (wp: crunch_wps simp: crunch_simps)

crunch irqs_masked'[wp]: doIPCTransfer "irqs_masked'"
  (wp: crunch_wps simp: crunch_simps rule: irqs_masked_lift)

lemma doIPCTransfer_invs[wp]:
  "\<lbrace>invs' and tcb_at' s and tcb_at' r\<rbrace>
   doIPCTransfer s ep bg grt r
   \<lbrace>\<lambda>rv. invs'\<rbrace>"
  apply (simp add: doIPCTransfer_def)
  apply (wpsimp wp: hoare_drop_imp)
  done

crunch nosch[wp]: doIPCTransfer "\<lambda>s. P (ksSchedulerAction s)" 
  (wp: hoare_drop_imps hoare_vcg_split_case_option mapM_wp'
   simp: split_def zipWithM_x_mapM)

lemma handle_fault_reply_registers_corres:
  "corres (op =) (tcb_at t) (tcb_at' t)
           (do t' \<leftarrow> thread_get id t;
               y \<leftarrow> as_user t
                (zipWithM_x
                  (\<lambda>r v. set_register r
                          (sanitise_register t' r v))
                  msg_template msg);
               return (label = 0)
            od)
           (do t' \<leftarrow> threadGet id t;
               y \<leftarrow> asUser t
                (zipWithM_x
                  (\<lambda>r v. setRegister r (sanitiseRegister t' r v))
                  msg_template msg);
               return (label = 0)
            od)"
  apply (rule corres_guard_imp)
    apply (rule corres_split [OF _ threadget_corres, where r'=tcb_relation])
       apply (rule corres_split)
       apply (rule corres_trivial, simp)
      apply (rule corres_as_user')
      apply(simp add: set_register_def setRegister_def sanitise_register_def
                      sanitiseRegister_def syscallMessage_def)
      apply(subst zipWithM_x_modify)+
      apply(rule corres_modify')
       apply (simp|wp)+
  done

lemma handle_fault_reply_corres:
  "ft' = fault_map ft \<Longrightarrow>
   corres (op =) (tcb_at t) (tcb_at' t)
     (handle_fault_reply ft t label msg)
     (handleFaultReply ft' t label msg)"
  apply (cases ft)
     apply(simp_all add: handleFaultReply_def
                         handle_arch_fault_reply_def handleArchFaultReply_def
                         syscallMessage_def exceptionMessage_def
                    split: arch_fault.split)
   by (rule handle_fault_reply_registers_corres)+

crunch typ_at'[wp]: handleFaultReply "\<lambda>s. P (typ_at' T p s)"

lemmas hfr_typ_ats[wp] = typ_at_lifts [OF handleFaultReply_typ_at']

crunch tcb_at'[wp]: attemptSwitchTo "tcb_at' t"
  (wp: crunch_wps)

crunch valid_pspace'[wp]: attemptSwitchTo valid_pspace'
  (wp: crunch_wps)

crunch ct'[wp]: handleFaultReply "\<lambda>s. P (ksCurThread s)"

lemma doIPCTransfer_sch_act_simple [wp]:
  "\<lbrace>sch_act_simple\<rbrace> doIPCTransfer sender endpoint badge grant receiver \<lbrace>\<lambda>_. sch_act_simple\<rbrace>"
  by (simp add: sch_act_simple_def, wp)

lemma possibleSwitchTo_invs'[wp]:
  "\<lbrace>invs' and st_tcb_at' runnable' t
          and (\<lambda>s. ksSchedulerAction s = ResumeCurrentThread \<longrightarrow> ksCurThread s \<noteq> t)\<rbrace>
   possibleSwitchTo t b \<lbrace>\<lambda>rv. invs'\<rbrace>"
  apply (simp add: possibleSwitchTo_def curDomain_def)
  apply (wp static_imp_wp ssa_invs' threadGet_wp | wpc | simp)+
  apply (auto simp: obj_at'_def tcb_in_cur_domain'_def)
  done

crunch invs'[wp]: attemptSwitchTo "invs'"

crunch cte_wp_at'[wp]: attemptSwitchTo "cte_wp_at' P p"
  (wp: crunch_wps)

crunch cur' [wp]: isFinalCapability "\<lambda>s. P (cur_tcb' s)"
  (simp: crunch_simps unless_when
     wp: crunch_wps getObject_inv loadObject_default_inv)

crunch ct' [wp]: deleteCallerCap "\<lambda>s. P (ksCurThread s)"
  (simp: crunch_simps unless_when
     wp: crunch_wps getObject_inv loadObject_default_inv
   ignore: getObject)

lemma getThreadCallerSlot_inv:
  "\<lbrace>P\<rbrace> getThreadCallerSlot t \<lbrace>\<lambda>_. P\<rbrace>"
  by (simp add: getThreadCallerSlot_def, wp)

lemma deleteCallerCap_ct_not_ksQ:
  "\<lbrace>invs' and ct_in_state' simple' and sch_act_sane
          and (\<lambda>s. ksCurThread s \<notin> set (ksReadyQueues s p))\<rbrace>
   deleteCallerCap t
   \<lbrace>\<lambda>rv s. ksCurThread s \<notin> set (ksReadyQueues s p)\<rbrace>"
  apply (simp add: deleteCallerCap_def getSlotCap_def getThreadCallerSlot_def locateSlot_conv)
  apply (wp getThreadCallerSlot_inv cteDeleteOne_ct_not_ksQ getCTE_wp)
  apply (clarsimp simp: cte_wp_at_ctes_of)
  done

crunch tcb_at'[wp]: unbindNotification "tcb_at' x"

lemma finaliseCapTrue_standin_tcb_at' [wp]:
  "\<lbrace>tcb_at' x\<rbrace> finaliseCapTrue_standin cap v2 \<lbrace>\<lambda>_. tcb_at' x\<rbrace>"
  apply (simp add: finaliseCapTrue_standin_def Let_def)
  apply (safe)
       apply (wp getObject_ntfn_inv
            | wpc
            | simp)+
  done

lemma finaliseCapTrue_standin_cur':
  "\<lbrace>\<lambda>s. cur_tcb' s\<rbrace> finaliseCapTrue_standin cap v2 \<lbrace>\<lambda>_ s'. cur_tcb' s'\<rbrace>"
  apply (simp add: cur_tcb'_def)
  apply (rule hoare_lift_Pf2 [OF _ finaliseCapTrue_standin_ct'])
  apply (wp)
  done

lemma cteDeleteOne_cur' [wp]:
  "\<lbrace>\<lambda>s. cur_tcb' s\<rbrace> cteDeleteOne slot \<lbrace>\<lambda>_ s'. cur_tcb' s'\<rbrace>"
  apply (simp add: cteDeleteOne_def unless_def when_def)
  apply (wp hoare_drop_imps finaliseCapTrue_standin_cur' isFinalCapability_cur'
         | simp add: split_def | wp_once cur_tcb_lift)+
  done

lemma handleFaultReply_cur' [wp]:
  "\<lbrace>\<lambda>s. cur_tcb' s\<rbrace> handleFaultReply x0 thread label msg \<lbrace>\<lambda>_ s'. cur_tcb' s'\<rbrace>"
  apply (clarsimp simp add: cur_tcb'_def)
  apply (rule hoare_lift_Pf2 [OF _ handleFaultReply_ct'])
  apply (wp)
  done

lemma capClass_Reply:
  "capClass cap = ReplyClass tcb \<Longrightarrow> isReplyCap cap \<and> capTCBPtr cap = tcb"
  apply (cases cap, simp_all add: isCap_simps)
  apply (rename_tac arch_capability)
  apply (case_tac arch_capability, simp_all)
  done

lemma reply_cap_end_mdb_chain:
  "\<lbrakk> cte_wp_at (op = (cap.ReplyCap t False)) slot s; invs s;
     invs' s';
     (s, s') \<in> state_relation; ctes_of s' (cte_map slot) = Some cte \<rbrakk>
      \<Longrightarrow> (mdbPrev (cteMDBNode cte) \<noteq> nullPointer
            \<and> mdbNext (cteMDBNode cte) = nullPointer)
           \<and> cte_wp_at' (\<lambda>cte. isReplyCap (cteCap cte) \<and> capReplyMaster (cteCap cte))
                    (mdbPrev (cteMDBNode cte)) s'"
  apply (frule(1) pspace_relation_ctes_ofI[OF state_relation_pspace_relation],
         clarsimp+)
  apply (subgoal_tac "\<exists>slot'. caps_of_state s slot' = Some (cap.ReplyCap t True)
                          \<and> descendants_of slot' (cdt s) = {slot}")
   apply (elim state_relationE exE)
   apply (clarsimp simp: cdt_relation_def
               simp del: split_paired_All)
   apply (drule spec, drule(1) mp[OF _ caps_of_state_cte_at])
   apply (frule(1) pspace_relation_cte_wp_at[OF _ caps_of_state_cteD],
          clarsimp+)
   apply (clarsimp simp: descendants_of'_def cte_wp_at_ctes_of)
   apply (frule_tac f="\<lambda>S. cte_map slot \<in> S" in arg_cong, simp(no_asm_use))
   apply (frule invs_mdb'[unfolded valid_mdb'_def])
   apply (rule context_conjI)
    apply (clarsimp simp: nullPointer_def valid_mdb_ctes_def)
    apply (erule(4) subtree_prev_0)
   apply (rule conjI)
    apply (rule ccontr)
    apply (frule valid_mdb_no_loops, simp add: no_loops_def)
    apply (drule_tac x="cte_map slot" in spec)
    apply (erule notE, rule r_into_trancl, rule ccontr)
    apply (clarsimp simp: mdb_next_unfold valid_mdb_ctes_def nullPointer_def)
    apply (rule valid_dlistEn, assumption+)
    apply (subgoal_tac "ctes_of s' \<turnstile> cte_map slot \<leadsto> mdbNext (cteMDBNode cte)")
     apply (frule(3) class_linksD)
     apply (clarsimp simp: isCap_simps dest!: capClass_Reply[OF sym])
     apply (drule_tac f="\<lambda>S. mdbNext (cteMDBNode cte) \<in> S" in arg_cong)
     apply (simp, erule notE, rule subtree.trans_parent, assumption+)
     apply (case_tac ctea, case_tac cte')
     apply (clarsimp simp add: parentOf_def isMDBParentOf_CTE)
     apply (simp add: sameRegionAs_def2 isCap_simps)
     apply (erule subtree.cases)
      apply (clarsimp simp: parentOf_def isMDBParentOf_CTE)
     apply (clarsimp simp: parentOf_def isMDBParentOf_CTE)
    apply (simp add: mdb_next_unfold)
   apply (erule subtree.cases)
    apply (clarsimp simp: valid_mdb_ctes_def)
    apply (erule_tac cte=ctea in valid_dlistEn, assumption)
     apply (simp add: mdb_next_unfold)
    apply (clarsimp simp: mdb_next_unfold isCap_simps)
   apply (drule_tac f="\<lambda>S. c' \<in> S" in arg_cong)
   apply (clarsimp simp: no_loops_direct_simp valid_mdb_no_loops)
  apply (frule invs_mdb)
  apply (drule invs_valid_reply_caps)
  apply (clarsimp simp: valid_mdb_def reply_mdb_def
                        valid_reply_caps_def reply_caps_mdb_def
                        cte_wp_at_caps_of_state
              simp del: split_paired_All)
  apply (drule spec, drule spec, drule(1) mp)
  apply (elim exEI)
  apply clarsimp
  apply (subgoal_tac "P" for P, rule sym, rule equalityI, assumption)
   apply clarsimp
   apply (erule(4) unique_reply_capsD)
  apply (simp add: descendants_of_def)
  apply (rule r_into_trancl)
  apply (simp add: cdt_parent_rel_def is_cdt_parent_def)
  done

lemma unbindNotification_valid_objs'_strengthen:
  "valid_tcb' tcb s \<longrightarrow> valid_tcb' (tcbBoundNotification_update Map.empty tcb) s"
  "valid_ntfn' ntfn s \<longrightarrow> valid_ntfn' (ntfnBoundTCB_update Map.empty ntfn) s"
  by (simp_all add: valid_tcb'_def valid_ntfn'_def valid_bound_tcb'_def valid_tcb_state'_def tcb_cte_cases_def split: ntfn.splits)

lemma unbindNotification_valid_objs':
  "\<lbrace>valid_objs'\<rbrace>
     unbindNotification tcb
   \<lbrace>\<lambda>_. valid_objs'\<rbrace>"
  apply (simp add: unbindNotification_def threadGet_def)
  apply (wp sts_valid_objs' threadSet_valid_objs' set_ntfn_valid_objs' gbn_wp'
            hoare_vcg_all_lift getObject_tcb_wp getNotification_wp sbn_valid_objs'
       | wpc
       | simp add: valid_tcb_state'_def
       | strengthen unbindNotification_valid_objs'_strengthen)+
  apply (fastforce simp: ran_def valid_objs'_def valid_obj'_def obj_at'_def
                         projectKOs valid_tcb'_def)
  done

crunch valid_objs'[wp]: cteDeleteOne "valid_objs'"
  (simp: crunch_simps unless_def
   wp: crunch_wps getObject_inv loadObject_default_inv 
   ignore: getObject)

crunch nosch[wp]: handleFaultReply "\<lambda>s. P (ksSchedulerAction s)"

lemma emptySlot_weak_sch_act[wp]:
  "\<lbrace>\<lambda>s. weak_sch_act_wf (ksSchedulerAction s) s\<rbrace>
   emptySlot slot irq
   \<lbrace>\<lambda>_ s. weak_sch_act_wf (ksSchedulerAction s) s\<rbrace>"
  by (wp weak_sch_act_wf_lift tcb_in_cur_domain'_lift)

lemma cancelAllIPC_weak_sch_act_wf[wp]:
  "\<lbrace>\<lambda>s. weak_sch_act_wf (ksSchedulerAction s) s\<rbrace>
   cancelAllIPC epptr
   \<lbrace>\<lambda>_ s. weak_sch_act_wf (ksSchedulerAction s) s\<rbrace>"
  apply (simp add: cancelAllIPC_def)
  apply (wp rescheduleRequired_weak_sch_act_wf hoare_drop_imp | wpc | simp)+
  done

lemma cancelAllSignals_weak_sch_act_wf[wp]:
  "\<lbrace>\<lambda>s. weak_sch_act_wf (ksSchedulerAction s) s\<rbrace>
   cancelAllSignals ntfnptr
   \<lbrace>\<lambda>_ s. weak_sch_act_wf (ksSchedulerAction s) s\<rbrace>"
  apply (simp add: cancelAllSignals_def)
  apply (wp rescheduleRequired_weak_sch_act_wf hoare_drop_imp | wpc | simp)+
  done

crunch weak_sch_act_wf[wp]: finaliseCapTrue_standin "\<lambda>s. weak_sch_act_wf (ksSchedulerAction s) s"
 (ignore: setThreadState getObject setObject
    simp: crunch_simps
      wp: crunch_wps getObject_inv loadObject_default_inv)

lemma cteDeleteOne_weak_sch_act[wp]:
  "\<lbrace>\<lambda>s. weak_sch_act_wf (ksSchedulerAction s) s\<rbrace>
   cteDeleteOne sl
   \<lbrace>\<lambda>_ s. weak_sch_act_wf (ksSchedulerAction s) s\<rbrace>"
  apply (simp add: cteDeleteOne_def unless_def)
  apply (wp hoare_drop_imps finaliseCapTrue_standin_cur' isFinalCapability_cur'
         | simp add: split_def)+
  done

crunch weak_sch_act_wf[wp]: emptySlot "\<lambda>s. weak_sch_act_wf (ksSchedulerAction s) s"

crunch pred_tcb_at'[wp]: handleFaultReply "pred_tcb_at' proj P t"
crunch valid_queues[wp]: handleFaultReply "Invariants_H.valid_queues"
crunch valid_queues'[wp]: handleFaultReply "valid_queues'"
crunch tcb_in_cur_domain'[wp]: handleFaultReply "tcb_in_cur_domain' t"

lemma as_user_valid_etcbs[wp]:
  "\<lbrace>valid_etcbs\<rbrace> as_user tptr f \<lbrace>\<lambda>rv. valid_etcbs\<rbrace>"
  apply (simp add: as_user_def set_object_def)
  apply (wp | wpc)+
  apply clarsimp
  apply (fastforce simp: valid_sched_def valid_etcbs_def valid_queues_def
                         valid_sched_action_def is_activatable_def
                         weak_valid_sched_action_def
                         st_tcb_at_kh_if_split st_tcb_def2)
  done

crunch sch_act_wf[wp]: unbindNotification "\<lambda>s. sch_act_wf (ksSchedulerAction s) s"
(wp: sbn_sch_act')

crunch valid_queues'[wp]: cteDeleteOne valid_queues'
  (simp: crunch_simps unless_def inQ_def
     wp: crunch_wps sts_st_tcb' getObject_inv loadObject_default_inv threadSet_valid_queues'
 ignore: getObject)

lemma cancelSignal_valid_queues'[wp]:
  "\<lbrace>valid_queues'\<rbrace> cancelSignal t ntfn \<lbrace>\<lambda>rv. valid_queues'\<rbrace>"
  apply (simp add: cancelSignal_def)
  apply (rule hoare_pre)
   apply (wp getNotification_wp| wpc | simp)+
  done

lemma cancelIPC_valid_queues'[wp]:
  "\<lbrace>valid_queues' and (\<lambda>s. sch_act_wf (ksSchedulerAction s) s) \<rbrace> cancelIPC t \<lbrace>\<lambda>rv. valid_queues'\<rbrace>"
  apply (simp add: cancelIPC_def Let_def getThreadReplySlot_def locateSlot_conv liftM_def)
  apply (rule hoare_seq_ext[OF _ gts_sp'])
  apply (case_tac state, simp_all) defer 2
  apply (rule hoare_pre)
   apply ((wp getEndpoint_wp getCTE_wp | wpc | simp)+)[8]
  apply (wp cteDeleteOne_valid_queues')
  apply (rule_tac Q="\<lambda>_. valid_queues' and (\<lambda>s. sch_act_wf (ksSchedulerAction s) s)" in hoare_post_imp)
  apply (clarsimp simp: capHasProperty_def cte_wp_at_ctes_of)
   apply (wp threadSet_valid_queues' threadSet_sch_act| simp)+
  apply (clarsimp simp: inQ_def)
  done

(* FIXME move *)
lemma cap_delete_one_cur_tcb[wp]:
  "\<lbrace>\<lambda>s. cur_tcb s\<rbrace> cap_delete_one slot \<lbrace>\<lambda>_ s. cur_tcb s\<rbrace>"
apply (simp add: cur_tcb_def)
apply (rule hoare_pre)
 apply wps
 apply wp
apply simp
done

crunch valid_objs'[wp]: handleFaultReply valid_objs'

lemma valid_tcb'_tcbFault_update[simp]: "\<And>tcb s. valid_tcb' tcb s \<Longrightarrow> valid_tcb' (tcbFault_update f tcb) s"
  by (clarsimp simp: valid_tcb'_def  tcb_cte_cases_def)

lemma do_reply_transfer_corres:
  "corres dc
     (einvs and tcb_at receiver and tcb_at sender
           and cte_wp_at (op = (cap.ReplyCap receiver False)) slot)
     (invs' and tcb_at' sender and tcb_at' receiver
            and valid_pspace' and cte_at' (cte_map slot))
     (do_reply_transfer sender receiver slot)
     (doReplyTransfer sender receiver (cte_map slot))"
  apply (simp add: do_reply_transfer_def doReplyTransfer_def)
  apply (rule corres_split' [OF _ _ gts_sp gts_sp'])
   apply (rule corres_guard_imp)
     apply (rule gts_corres, (clarsimp simp add: st_tcb_at_tcb_at)+)
  apply (rule_tac F = "awaiting_reply state" in corres_req)
   apply (clarsimp simp add: st_tcb_at_def obj_at_def is_tcb)
   apply (fastforce simp: invs_def valid_state_def
                   dest: has_reply_cap_cte_wpD
                  dest!: valid_reply_caps_awaiting_reply)
  apply (case_tac state, simp_all add: bind_assoc)
  apply (simp add: isReply_def liftM_def)
  apply (rule corres_symb_exec_r[OF _ getCTE_sp getCTE_inv, rotated])
   apply (rule no_fail_pre, wp)
   apply clarsimp
  apply (rename_tac mdbnode)
  apply (rule_tac P="Q" and Q="Q" and P'="Q'" and Q'="(\<lambda>s. Q' s \<and> R' s)" for Q Q' R'
            in stronger_corres_guard_imp[rotated])
    apply assumption
   apply (rule conjI, assumption)
   apply (clarsimp simp: cte_wp_at_ctes_of)
   apply (erule(4) reply_cap_end_mdb_chain)
  apply (rule corres_assert_assume[rotated], simp)
  apply (simp add: getSlotCap_def)
  apply (rule corres_symb_exec_r[OF _ getCTE_sp getCTE_inv, rotated])
   apply (rule no_fail_pre, wp)
   apply (clarsimp simp: cte_wp_at_ctes_of)
  apply (rule corres_assert_assume[rotated])
   apply (clarsimp simp: cte_wp_at_ctes_of)
  apply (rule corres_guard_imp)
    apply (rule corres_split [OF _ threadget_fault_corres])
      apply (case_tac rv, simp_all add: fault_rel_optionation_def bind_assoc)[1]
       apply (rule corres_split [OF _ dit_corres])
         apply (rule corres_split [OF _ cap_delete_one_corres])
           apply (rule corres_split [OF _ sts_corres])
              apply (rule attemptSwitchTo_corres)
             apply (wp set_thread_state_runnable_valid_sched set_thread_state_runnable_weak_valid_sched_action sts_st_tcb_at' sts_st_tcb' sts_valid_queues sts_valid_objs' delete_one_tcbDomain_obj_at'
                 | simp add: valid_tcb_state'_def)+
        apply (strengthen cte_wp_at_reply_cap_can_fast_finalise)
        apply (wp hoare_vcg_conj_lift)
         apply (rule hoare_strengthen_post [OF do_ipc_transfer_non_null_cte_wp_at])
          prefer 2
          apply (erule cte_wp_at_weakenE)
          apply (fastforce)
         apply (clarsimp simp:is_cap_simps)
        apply (wp weak_valid_sched_action_lift)+
       apply (rule_tac Q="\<lambda>_. valid_queues' and valid_objs' and cur_tcb' and tcb_at' receiver and (\<lambda>s. sch_act_wf (ksSchedulerAction s) s)" in hoare_post_imp, simp add: sch_act_wf_weak)
       apply (wp tcb_in_cur_domain'_lift)
      defer
      apply (simp)
      apply (wp)+
    apply (clarsimp)
    apply (rule conjI, erule invs_valid_objs)
    apply (rule conjI, clarsimp)+
    apply (rule conjI)
     apply (erule cte_wp_at_weakenE)
     apply (clarsimp)
     apply (rule conjI, rule refl)
     apply (fastforce)
    apply (clarsimp simp: invs_def valid_sched_def valid_sched_action_def)
   apply (simp)
   apply (auto simp: invs'_def valid_state'_def)[1]
  apply (rule corres_guard_imp)
    apply (rule corres_split [OF _ cap_delete_one_corres])
      apply (rule corres_split_mapr [OF _ get_mi_corres])
        apply (rule corres_split_eqr [OF _ lipcb_corres'])
          apply (rule corres_split_eqr [OF _ get_mrs_corres])
            apply (simp(no_asm) del: dc_simp)
            apply (rule corres_split_eqr [OF _ handle_fault_reply_corres])
               apply (rule corres_split [OF _ threadset_corresT])
                     apply (rule_tac Q="valid_sched and cur_tcb and tcb_at receiver"
                                 and Q'="tcb_at' receiver and cur_tcb'
                                           and (\<lambda>s. weak_sch_act_wf (ksSchedulerAction s) s)
                                           and Invariants_H.valid_queues and valid_queues' and valid_objs'"
                                   in corres_guard_imp)
                       apply (case_tac rvb, simp_all)[1]
                        apply (fold dc_def)
                        apply (rule corres_guard_imp)
                          apply (rule corres_split [OF _ sts_corres])
                             apply (simp add: when_def)
                             apply (rule attemptSwitchTo_corres)
                            apply (wp static_imp_wp static_imp_conj_wp set_thread_state_runnable_weak_valid_sched_action sts_st_tcb_at'
                                       sts_st_tcb' sts_valid_queues | simp | force simp: valid_sched_def valid_sched_action_def valid_tcb_state'_def)+
                       apply (rule corres_guard_imp)
                         apply (rule sts_corres)
                         apply (simp_all)[20]
                   apply (clarsimp simp add: tcb_relation_def fault_rel_optionation_def
                                             tcb_cap_cases_def tcb_cte_cases_def exst_same_def)+
                  apply (wp threadSet_cur weak_sch_act_wf_lift_linear threadSet_pred_tcb_no_state
                            thread_set_not_state_valid_sched threadSet_valid_queues threadSet_valid_queues'
                            threadSet_tcbDomain_triv threadSet_valid_objs'
                       | simp add: valid_tcb_state'_def)+
               apply (wp threadSet_cur weak_sch_act_wf_lift_linear threadSet_pred_tcb_no_state
                         thread_set_not_state_valid_sched threadSet_valid_queues threadSet_valid_queues'
                    | simp add: runnable_def inQ_def valid_tcb'_def)+
     apply (rule_tac Q="\<lambda>_. valid_sched and cur_tcb and tcb_at sender and tcb_at receiver and valid_objs and pspace_aligned"
                     in hoare_strengthen_post [rotated], clarsimp)
     apply (wp)
     apply (rule hoare_chain [OF cap_delete_one_invs])
      apply (assumption)
     apply (rule conjI, clarsimp)
     apply (clarsimp simp add: invs_def valid_state_def)
    apply (rule_tac Q="\<lambda>_. tcb_at' sender and tcb_at' receiver and invs'"
                    in hoare_strengthen_post [rotated])
     apply (auto simp: invs'_def valid_state'_def intro: sch_act_wf_weak)[1]
    apply wp
   apply clarsimp
   apply (rule conjI)
    apply (erule cte_wp_at_weakenE)
    apply (clarsimp simp add: can_fast_finalise_def)
   apply (erule(1) emptyable_cte_wp_atD)
   apply (rule allI, rule impI)
   apply (clarsimp simp add: is_master_reply_cap_def)
  apply (clarsimp)
  done


lemma valid_pspace'_splits[elim!]:
  "valid_pspace' s \<Longrightarrow> valid_objs' s"
  "valid_pspace' s \<Longrightarrow> pspace_aligned' s"
  "valid_pspace' s \<Longrightarrow> pspace_distinct' s"
  "valid_pspace' s \<Longrightarrow> valid_mdb' s"
  "valid_pspace' s \<Longrightarrow> no_0_obj' s"
  by (simp add: valid_pspace'_def)+

lemma sts_valid_pspace_hangers:
  "\<lbrace>valid_pspace' and tcb_at' t and
   valid_tcb_state' st\<rbrace> setThreadState st t \<lbrace>\<lambda>rv. valid_objs'\<rbrace>"
  "\<lbrace>valid_pspace' and tcb_at' t and
   valid_tcb_state' st\<rbrace> setThreadState st t \<lbrace>\<lambda>rv. pspace_distinct'\<rbrace>"
  "\<lbrace>valid_pspace' and tcb_at' t and
   valid_tcb_state' st\<rbrace> setThreadState st t \<lbrace>\<lambda>rv. pspace_aligned'\<rbrace>"
  "\<lbrace>valid_pspace' and tcb_at' t and
   valid_tcb_state' st\<rbrace> setThreadState st t \<lbrace>\<lambda>rv. valid_mdb'\<rbrace>"
  "\<lbrace>valid_pspace' and tcb_at' t and
   valid_tcb_state' st\<rbrace> setThreadState st t \<lbrace>\<lambda>rv. no_0_obj'\<rbrace>"
  by (safe intro!: hoare_strengthen_post [OF sts'_valid_pspace'_inv])

declare no_fail_getSlotCap [wp]

lemma setup_caller_corres:
  "corres dc
     (st_tcb_at (Not \<circ> halted) sender and tcb_at receiver and
      st_tcb_at (Not \<circ> awaiting_reply) sender and valid_reply_caps and
      valid_objs and pspace_distinct and pspace_aligned and valid_mdb 
      and valid_list and
      valid_reply_masters and cte_wp_at (\<lambda>c. c = cap.NullCap) (receiver, tcb_cnode_index 3))
     (tcb_at' sender and tcb_at' receiver and valid_pspace'
                and (\<lambda>s. weak_sch_act_wf (ksSchedulerAction s) s))
     (setup_caller_cap sender receiver)
     (setupCallerCap sender receiver)"
  apply (simp add: setup_caller_cap_def setupCallerCap_def
                   getThreadReplySlot_def locateSlot_conv
                   getThreadCallerSlot_def)
  apply (rule stronger_corres_guard_imp)
    apply (rule corres_split_nor)
       apply (rule corres_symb_exec_r)
          apply (rule_tac F="cteCap masterCTE = capability.ReplyCap sender True
                              \<and> mdbNext (cteMDBNode masterCTE) = nullPointer"
                       in corres_gen_asm2, simp add: isCap_simps)
          apply (rule corres_symb_exec_r)
             apply (rule_tac F="rv = capability.NullCap"
                          in corres_gen_asm2, simp)
             apply (rule cins_corres)
               apply simp
              apply (simp add: cte_map_def tcbReplySlot_def
                               tcb_cnode_index_def cte_level_bits_def)
             apply (simp add: cte_map_def tcbCallerSlot_def
                              tcb_cnode_index_def cte_level_bits_def)
            apply (rule_tac Q="\<lambda>rv. cte_at' (receiver + 2 ^ cte_level_bits * tcbCallerSlot)"
                     in valid_prove_more)

            apply (wp, (wp getSlotCap_wp)+)
           apply blast
          apply (rule no_fail_pre, wp)
          apply (clarsimp simp: cte_wp_at'_def cte_at'_def)
         apply (rule_tac Q="\<lambda>rv. cte_at' (sender + 2 ^ cte_level_bits * tcbReplySlot)"
                      in valid_prove_more)
         apply (wp, (wp getCTE_wp')+)
        apply blast
       apply (rule no_fail_pre, wp)
       apply (clarsimp simp: cte_wp_at_ctes_of)
      apply (rule sts_corres)
      apply (simp split: option.split)
     apply (wp sts_valid_pspace_hangers
                 | simp add: cte_wp_at_ctes_of)+
   apply (clarsimp simp: valid_tcb_state_def st_tcb_at_reply_cap_valid
                         st_tcb_at_tcb_at st_tcb_at_caller_cap_null
                  split: option.split)
  apply (clarsimp simp: valid_tcb_state'_def valid_cap'_def capAligned_reply_tcbI)
  apply (frule(1) st_tcb_at_reply_cap_valid, simp, clarsimp)
  apply (clarsimp simp: cte_wp_at_ctes_of cte_wp_at_caps_of_state)
  apply (drule pspace_relation_cte_wp_at[rotated, OF caps_of_state_cteD],
         erule valid_pspace'_splits, clarsimp+)+
  apply (clarsimp simp: cte_wp_at_ctes_of cte_map_def tcbReplySlot_def
                        tcbCallerSlot_def cte_level_bits_def tcb_cnode_index_def
                        is_cap_simps)
  apply (auto intro: reply_no_descendants_mdbNext_null[OF not_waiting_reply_slot_no_descendants])
  done

crunch tcb_at'[wp]: getThreadCallerSlot "tcb_at' t"

lemma getThreadReplySlot_tcb_at'[wp]:
  "\<lbrace>tcb_at' t\<rbrace> getThreadReplySlot tcb \<lbrace>\<lambda>_. tcb_at' t\<rbrace>"
  by (simp add: getThreadReplySlot_def, wp)

lemma setupCallerCap_tcb_at'[wp]:
  "\<lbrace>tcb_at' t\<rbrace> setupCallerCap sender receiver \<lbrace>\<lambda>_. tcb_at' t\<rbrace>"
  by (simp add: setupCallerCap_def, wp hoare_drop_imp)

crunch ct'[wp]: setupCallerCap "\<lambda>s. P (ksCurThread s)"
  (wp: crunch_wps)

lemma cteInsert_sch_act_wf[wp]:
  "\<lbrace>\<lambda>s. sch_act_wf (ksSchedulerAction s) s\<rbrace>
     cteInsert newCap srcSlot destSlot
   \<lbrace>\<lambda>_ s. sch_act_wf (ksSchedulerAction s) s\<rbrace>"
by (wp sch_act_wf_lift tcb_in_cur_domain'_lift)

lemma setupCallerCap_sch_act [wp]:
  "\<lbrace>\<lambda>s. sch_act_not t s \<and> sch_act_wf (ksSchedulerAction s) s\<rbrace> 
  setupCallerCap t r \<lbrace>\<lambda>_ s. sch_act_wf (ksSchedulerAction s) s\<rbrace>"
  apply (simp add: setupCallerCap_def getSlotCap_def getThreadCallerSlot_def
            getThreadReplySlot_def locateSlot_conv)
  apply (wp getCTE_wp' sts_sch_act' hoare_drop_imps hoare_vcg_all_lift)
  apply clarsimp
  done

lemma setupCallerCap_weak_sch_act_from_sch_act:
  "\<lbrace>\<lambda>s. sch_act_not t s \<and> sch_act_wf (ksSchedulerAction s) s\<rbrace> 
  setupCallerCap t r \<lbrace>\<lambda>_ s. weak_sch_act_wf (ksSchedulerAction s) s\<rbrace>"
  apply (rule hoare_strengthen_post, rule setupCallerCap_sch_act)
  apply (clarsimp simp: weak_sch_act_wf_def)
  done

lemma attemptSwitchTo_weak_sch_act_wf[wp]:
  "\<lbrace>\<lambda>s. weak_sch_act_wf (ksSchedulerAction s) s \<and> st_tcb_at' runnable' t s\<rbrace>
      attemptSwitchTo t \<lbrace>\<lambda>rv s. weak_sch_act_wf (ksSchedulerAction s) s\<rbrace>"
  apply (simp add: attemptSwitchTo_def possibleSwitchTo_def
                   setSchedulerAction_def threadGet_def curDomain_def)
  apply (wp rescheduleRequired_weak_sch_act_wf
            weak_sch_act_wf_lift_linear[where f="tcbSchedEnqueue t"]
            getObject_tcb_wp static_imp_wp
           | wpc)+
  apply (clarsimp simp: obj_at'_def projectKOs weak_sch_act_wf_def ps_clear_def tcb_in_cur_domain'_def)
  done

lemmas transferCapsToSlots_pred_tcb_at' =
    transferCapsToSlots_pres1 [OF cteInsert_pred_tcb_at']

crunch pred_tcb_at'[wp]: doIPCTransfer, attemptSwitchTo "pred_tcb_at' proj P t"
  (wp: mapM_wp' crunch_wps simp: zipWithM_x_mapM)


(* FIXME move *)
lemma tcb_in_cur_domain'_ksSchedulerAction_update[simp]:
  "tcb_in_cur_domain' t (ksSchedulerAction_update f s) = tcb_in_cur_domain' t s"
by (simp add: tcb_in_cur_domain'_def)

(* FIXME move *)
lemma ct_idle_or_in_cur_domain'_ksSchedulerAction_update[simp]:
  "b\<noteq> ResumeCurrentThread \<Longrightarrow> 
   ct_idle_or_in_cur_domain' (s\<lparr>ksSchedulerAction := b\<rparr>)"
  apply (clarsimp simp add: ct_idle_or_in_cur_domain'_def)
  done

lemma setSchedulerAction_ct_in_domain:
 "\<lbrace>\<lambda>s. ct_idle_or_in_cur_domain' s 
   \<and>  p \<noteq> ResumeCurrentThread \<rbrace> setSchedulerAction p
  \<lbrace>\<lambda>_. ct_idle_or_in_cur_domain'\<rbrace>"
  by (simp add:setSchedulerAction_def | wp)+

crunch ct_idle_or_in_cur_domain'[wp]: setupCallerCap, switchIfRequiredTo, doIPCTransfer, attemptSwitchTo ct_idle_or_in_cur_domain'
  (wp: crunch_wps setSchedulerAction_ct_in_domain simp: zipWithM_x_mapM)
crunch ksCurDomain[wp]: setupCallerCap, switchIfRequiredTo, doIPCTransfer, attemptSwitchTo "\<lambda>s. P (ksCurDomain s)"
  (wp: crunch_wps simp: zipWithM_x_mapM)
crunch ksDomSchedule[wp]: setupCallerCap, switchIfRequiredTo, doIPCTransfer, attemptSwitchTo "\<lambda>s. P (ksDomSchedule s)"
  (wp: crunch_wps simp: zipWithM_x_mapM)

crunch tcbDomain_obj_at'[wp]: doIPCTransfer "obj_at' (\<lambda>tcb. P (tcbDomain tcb)) t"
  (wp: crunch_wps constOnFailure_wp simp: crunch_simps)

lemma send_ipc_corres:
(* call is only true if called in handleSyscall SysCall, which
   is always blocking. *)
  assumes "call \<longrightarrow> bl"
  shows
  "corres dc (einvs and st_tcb_at active t and ep_at ep and ex_nonz_cap_to t)
             (invs' and  sch_act_not t and tcb_at' t and ep_at' ep)
             (send_ipc bl call bg cg t ep) (sendIPC bl call bg cg t ep)"
proof -
  have weak_sch_act_wf: "\<And>sa s. sch_act_wf sa s \<longrightarrow> weak_sch_act_wf sa s"
    by (clarsimp, erule sch_act_wf_weak)
  show ?thesis
  apply (insert assms)
  apply (unfold send_ipc_def sendIPC_def Let_def)
  apply (case_tac bl)
   apply clarsimp
   apply (rule corres_guard_imp)
     apply (rule corres_split [OF _ get_ep_corres, 
              where
              R="\<lambda>rv. einvs and st_tcb_at active t and ep_at ep and 
                      valid_ep rv and obj_at (\<lambda>ob. ob = Endpoint rv) ep
                      and ex_nonz_cap_to t"
              and
              R'="\<lambda>rv'. invs' and tcb_at' t and sch_act_not t
                              and ep_at' ep and valid_ep' rv'"])
       apply (case_tac rv)
         apply (simp add: ep_relation_def)
         apply (rule corres_guard_imp)
           apply (rule corres_split [OF _ sts_corres])
              apply (rule set_ep_corres)
              apply (simp add: ep_relation_def)
             apply (simp add: fault_rel_optionation_def)
            apply wp+
          apply (clarsimp simp: st_tcb_at_tcb_at valid_tcb_state_def)
         apply clarsimp
         -- "concludes IdleEP if bl branch"
        apply (simp add: ep_relation_def)
        apply (rule corres_guard_imp)
          apply (rule corres_split [OF _ sts_corres])
             apply (rule set_ep_corres)
             apply (simp add: ep_relation_def)
            apply (simp add: fault_rel_optionation_def)
           apply wp+
         apply (clarsimp simp: st_tcb_at_tcb_at valid_tcb_state_def)
        apply clarsimp
        -- "concludes SendEP if bl branch"
       apply (simp add: ep_relation_def)
       apply (rename_tac list)
       apply (rule_tac F="list \<noteq> []" in corres_req)
        apply (simp add: valid_ep_def)
       apply (case_tac list)
        apply simp
       apply (clarsimp split del: if_split)
       apply (rule corres_guard_imp) 
         apply (rule corres_split [OF _ set_ep_corres])
            apply (simp add: isReceive_def split del:if_split)
            apply (rule corres_split [OF _ gts_corres])
              apply (rule_tac 
                     F="recv_state = Structures_A.BlockedOnReceive ep" 
                     in corres_gen_asm)
              apply (clarsimp simp: case_bool_If  case_option_If if3_fold
                          simp del: dc_simp split del: if_split cong: if_cong)
              apply (rule corres_split [OF _ dit_corres])
                apply (rule corres_split [OF _ sts_corres])
                   apply (rule corres_split [OF _ attemptSwitchTo_corres])
                     apply (rule corres_split [OF _ threadget_fault_corres])
                       apply (fold when_def)[1]
                       apply (rename_tac fault fault')
                       apply (rule_tac P="call \<or> fault \<noteq> None"
                                  and P'="call \<or> fault' \<noteq> None"
                                   in corres_symmetric_bool_cases)
                         apply (auto simp: fault_rel_optionation_def)[1]
                        apply (simp add: when_def dc_def[symmetric] split del: if_split)
                        apply (rule corres_if2, simp)
                         apply (rule setup_caller_corres)
                        apply (rule sts_corres, simp)
                       apply (rule corres_trivial)
                       apply (simp add: when_def dc_def[symmetric] split del: if_split)
                      apply (simp split del: if_split add: if_apply_def2)
                      apply (wp hoare_drop_imps)[1]
                     apply (simp split del: if_split add: if_apply_def2)
                     apply (wp hoare_drop_imps)[1]
                    apply (wp | simp)+
                 apply (wp sts_cur_tcb set_thread_state_runnable_weak_valid_sched_action sts_st_tcb_at_cases)
                apply (wp setThreadState_valid_queues' sts_valid_queues sts_weak_sch_act_wf
                          sts_cur_tcb' setThreadState_tcb' sts_st_tcb_at'_cases)[1]
               apply (simp add: valid_tcb_state_def pred_conj_def)
               apply (strengthen reply_cap_doesnt_exist_strg disjI2_strg)
               apply ((wp hoare_drop_imps do_ipc_transfer_tcb_caps weak_valid_sched_action_lift
                    | clarsimp simp: is_cap_simps)+)[1]
              apply (simp add: pred_conj_def)
              apply (strengthen weak_sch_act_wf)
              apply (simp add: valid_tcb_state'_def)
              apply (wp weak_sch_act_wf_lift_linear tcb_in_cur_domain'_lift hoare_drop_imps)[1]
             apply (wp gts_st_tcb_at)+
           apply (simp add: ep_relation_def split: list.split)
          apply (simp add: pred_conj_def cong: conj_cong)
          apply (wp hoare_post_taut)
         apply (simp)
         apply (wp weak_sch_act_wf_lift_linear set_ep_valid_objs' setEndpoint_valid_mdb')+
        apply (clarsimp simp add: invs_def valid_state_def valid_pspace_def ep_redux_simps
                        ep_redux_simps' st_tcb_at_tcb_at valid_ep_def cong: list.case_cong)
        apply (drule(1) sym_refs_obj_atD[where P="\<lambda>ob. ob = e" for e])
        apply (clarsimp simp: st_tcb_at_refs_of_rev st_tcb_at_reply_cap_valid st_tcb_at_caller_cap_null)
        apply (fastforce simp: st_tcb_def2 valid_sched_def valid_sched_action_def)
       subgoal by (auto simp: valid_ep'_def invs'_def valid_state'_def split: list.split)
      apply wp+
    apply (clarsimp)+
  apply (rule corres_guard_imp)
    apply (rule corres_split [OF _ get_ep_corres,
             where
             R="\<lambda>rv. einvs and st_tcb_at active t and ep_at ep and
                     valid_ep rv and obj_at (\<lambda>k. k = Endpoint rv) ep"
             and
             R'="\<lambda>rv'. invs' and tcb_at' t and sch_act_not t
                             and ep_at' ep and valid_ep' rv'"])
      apply (rename_tac rv rv')
      apply (case_tac rv)
        apply (simp add: ep_relation_def)
        -- "concludes IdleEP branch if not bl and no ft"
       apply (simp add: ep_relation_def)
       -- "concludes SendEP branch if not bl and no ft"
      apply (simp add: ep_relation_def)
      apply (rename_tac list)
      apply (rule_tac F="list \<noteq> []" in corres_req)
       apply (simp add: valid_ep_def)
      apply (case_tac list)
       apply simp
      apply (rule_tac F="a \<noteq> t" in corres_req)
       apply (clarsimp simp: invs_def valid_state_def
                             valid_pspace_def)
       apply (drule(1) sym_refs_obj_atD[where P="\<lambda>ob. ob = e" for e])
       apply (clarsimp simp: st_tcb_at_def obj_at_def tcb_bound_refs_def2)
       apply fastforce
      apply (clarsimp split del: if_split)
      apply (rule corres_guard_imp)
        apply (rule corres_split [OF _ set_ep_corres])
           apply (rule corres_split [OF _ gts_corres])
             apply (rule_tac
                F="recv_state = Structures_A.BlockedOnReceive ep"
                    in corres_gen_asm)
             apply (clarsimp simp: isReceive_def case_bool_If
                        split del: if_split cong: if_cong)
             apply (rule corres_split [OF _ dit_corres])
               apply (rule corres_split [OF _ sts_corres])
                   apply (rule corres_split [OF _ attemptSwitchTo_corres])
                   apply (rule corres_split [OF _ threadget_fault_corres])
                     apply (rename_tac rv rv')
                     apply (case_tac rv)
                      apply (clarsimp simp: fault_rel_optionation_def when_def split del: if_split)
                     apply (clarsimp simp: fault_rel_optionation_def when_def
                                           case_bool_If
                                split del: if_split)
                     apply (fold dc_def)[1]
                     apply (rule corres_if2, simp)
                      apply (rule setup_caller_corres)
                     apply (rule sts_corres, simp)
                    apply wp+
                  apply (simp add: if_apply_def2)
                  apply (wp hoare_drop_imps)
                  apply (simp add: if_apply_def2)
                  apply (wp hoare_drop_imps)
                 apply simp
                apply ((wp sts_cur_tcb set_thread_state_runnable_weak_valid_sched_action sts_st_tcb_at_cases |
                           simp add: if_apply_def2 split del: if_split)+)[1]
               apply (wp setThreadState_valid_queues' sts_valid_queues sts_weak_sch_act_wf
                         sts_cur_tcb' setThreadState_tcb' sts_st_tcb_at'_cases)
              apply (simp add: valid_tcb_state_def pred_conj_def)
              apply (strengthen reply_cap_doesnt_exist_strg disjI2_strg)
              apply ((wp hoare_drop_imps do_ipc_transfer_tcb_caps  weak_valid_sched_action_lift
                     | clarsimp simp:is_cap_simps)+)[1]
             apply (simp add: valid_tcb_state'_def pred_conj_def)
             apply (strengthen weak_sch_act_wf)
             apply (wp weak_sch_act_wf_lift_linear hoare_drop_imps)
            apply (wp gts_st_tcb_at)+
          apply (simp add: ep_relation_def split: list.split)
         apply (simp add: pred_conj_def cong: conj_cong)
         apply (wp hoare_post_taut)
        apply simp
        apply (wp weak_sch_act_wf_lift_linear set_ep_valid_objs' setEndpoint_valid_mdb')
       apply (clarsimp simp add: invs_def valid_state_def
                                 valid_pspace_def ep_redux_simps ep_redux_simps'
                                 st_tcb_at_tcb_at
                           cong: list.case_cong)
       apply (clarsimp simp: valid_ep_def)
       apply (drule(1) sym_refs_obj_atD[where P="\<lambda>ob. ob = e" for e])
       apply (clarsimp simp: st_tcb_at_refs_of_rev st_tcb_at_reply_cap_valid
                             st_tcb_at_caller_cap_null)
       apply (fastforce simp: st_tcb_def2 valid_sched_def valid_sched_action_def)
      subgoal by (auto simp: valid_ep'_def
                      split: list.split; 
                  clarsimp simp: invs'_def valid_state'_def)
     apply wp+
   apply (clarsimp)+
  done
qed

lemma threadSet_ep_at:
  "\<lbrace>ep_at' p\<rbrace> threadSet f r \<lbrace>\<lambda>x. ep_at' p\<rbrace>"
  apply (simp add: threadSet_def)
  apply (wp setObject_tcb_ep_at)
  done

crunch typ_at'[wp]: setMessageInfo "\<lambda>s. P (typ_at' T p s)"

lemmas setMessageInfo_typ_ats[wp] = typ_at_lifts [OF setMessageInfo_typ_at']

(* Annotation added by Simon Winwood (Thu Jul  1 20:54:41 2010) using taint-mode *)
declare tl_drop_1[simp]

crunch cur[wp]: cancel_ipc "cur_tcb"
  (wp: select_wp crunch_wps simp: crunch_simps)

crunch valid_objs'[wp]: asUser "valid_objs'"

lemma valid_sched_weak_strg:
  "valid_sched s \<longrightarrow> weak_valid_sched_action s"
  by (simp add: valid_sched_def valid_sched_action_def)

lemma invs_psp'_strg:
  "invs' s \<longrightarrow> valid_pspace' s"
  by clarsimp

crunch weak_valid_sched_action[wp]: as_user weak_valid_sched_action
  (wp: weak_valid_sched_action_lift)

lemma send_signal_corres:
  "corres dc (einvs and ntfn_at ep) (invs' and ntfn_at' ep)
             (send_signal ep bg) (sendSignal ep bg)"
  apply (simp add: send_signal_def sendSignal_def Let_def)
  apply (rule corres_guard_imp)
    apply (rule corres_split [OF _ get_ntfn_corres,
                where
                R  = "\<lambda>rv. einvs and ntfn_at ep and valid_ntfn rv and 
                           ko_at (Structures_A.Notification rv) ep" and
                R' = "\<lambda>rv'. invs' and ntfn_at' ep and
                            valid_ntfn' rv' and ko_at' rv' ep"])
      defer
      apply (wp get_ntfn_ko get_ntfn_ko')+
    apply (simp add: invs_valid_objs)+
  apply (case_tac "ntfn_obj ntfn")
    -- "IdleNtfn"
    apply (clarsimp simp add: ntfn_relation_def)
    apply (case_tac "ntfnBoundTCB nTFN")
     apply clarsimp
     apply (rule corres_guard_imp[OF set_ntfn_corres])
       apply (clarsimp simp add: ntfn_relation_def)+
    apply (rule corres_guard_imp)
      apply (rule corres_split[OF _ gts_corres])
        apply (rule corres_if)
          apply (fastforce simp: receive_blocked_def receiveBlocked_def
                                 thread_state_relation_def
                          split: Structures_A.thread_state.splits
                                 Structures_H.thread_state.splits)
         apply (rule corres_split[OF _ cancel_ipc_corres])
           apply (rule corres_split[OF _ sts_corres])
              apply (simp add: badgeRegister_def badge_register_def)
              apply (rule corres_split[OF _ user_setreg_corres])
                apply (rule switchIfRequiredTo_corres)
               apply wp
             apply (clarsimp simp: thread_state_relation_def)
            apply (wp set_thread_state_runnable_weak_valid_sched_action sts_st_tcb_at'
                      sts_valid_queues sts_st_tcb' hoare_disjI2
                      cancel_ipc_cte_wp_at_not_reply_state
                 | strengthen invs_vobjs_strgs invs_psp_aligned_strg valid_sched_weak_strg
                 | simp add: valid_tcb_state_def)+
         apply (rule_tac Q="\<lambda>rv. invs' and tcb_at' a" in hoare_strengthen_post)
          apply wp
         apply (clarsimp simp: invs'_def valid_state'_def sch_act_wf_weak
                               valid_tcb_state'_def)
        apply (rule set_ntfn_corres)
        apply (clarsimp simp add: ntfn_relation_def)
       apply (wp gts_wp gts_wp' | clarsimp)+
     apply (auto simp: valid_ntfn_def receive_blocked_def valid_sched_def invs_cur
                 elim: pred_tcb_weakenE
                intro: st_tcb_at_reply_cap_valid
                split: Structures_A.thread_state.splits)[1]
    apply (clarsimp simp: valid_ntfn'_def invs'_def valid_state'_def valid_pspace'_def sch_act_wf_weak)
   -- "WaitingNtfn"
   apply (clarsimp simp add: ntfn_relation_def Let_def)
   apply (simp add: update_waiting_ntfn_def)
   apply (rename_tac list)
   apply (case_tac "tl list = []")
    -- "tl list = []"
    apply (rule corres_guard_imp)
      apply (rule_tac F="list \<noteq> []" in corres_gen_asm)
      apply (simp add: list_case_helper split del: if_split)
      apply (rule corres_split [OF _ set_ntfn_corres])
         apply (rule corres_split [OF _ sts_corres])
            apply (simp add: badgeRegister_def badge_register_def)
            apply (rule corres_split [OF _ user_setreg_corres])
              apply (rule switchIfRequiredTo_corres)
             apply ((wp | simp)+)[1]
            apply (rule_tac Q="\<lambda>_. Invariants_H.valid_queues and valid_queues' and
                                   (\<lambda>s. sch_act_wf (ksSchedulerAction s) s) and
                                   cur_tcb' and
                                   st_tcb_at' runnable' (hd list) and valid_objs'"
                     in hoare_post_imp, clarsimp simp: pred_tcb_at' elim!: sch_act_wf_weak)
            apply (wp | simp)+
          apply (wp sts_st_tcb_at' set_thread_state_runnable_weak_valid_sched_action
               | simp)+ 
         apply (wp sts_st_tcb_at'_cases sts_valid_queues setThreadState_valid_queues'
                   setThreadState_st_tcb
              | simp)+
        apply (simp add: ntfn_relation_def)
       apply (wp set_ntfn_valid_objs set_ntfn_aligned' set_ntfn_valid_objs'
                 hoare_vcg_disj_lift weak_sch_act_wf_lift_linear
            | simp add: valid_tcb_state_def valid_tcb_state'_def)+
     apply (clarsimp simp: invs_def valid_state_def valid_ntfn_def 
                           valid_pspace_def ntfn_queued_st_tcb_at valid_sched_def
                           valid_sched_action_def)
    apply (auto simp: valid_ntfn'_def )[1]
    apply (clarsimp simp: invs'_def valid_state'_def)

   -- "tl list \<noteq> []"
   apply (rule corres_guard_imp)
     apply (rule_tac F="list \<noteq> []" in corres_gen_asm)
     apply (simp add: list_case_helper)
     apply (rule corres_split [OF _ set_ntfn_corres])
        apply (rule corres_split [OF _ sts_corres])
           apply (simp add: badgeRegister_def badge_register_def)
           apply (rule corres_split [OF _ user_setreg_corres])
             apply (rule switchIfRequiredTo_corres)
            apply (wp cur_tcb_lift | simp)+
         apply (wp sts_st_tcb_at' set_thread_state_runnable_weak_valid_sched_action
              | simp)+ 
        apply (wp sts_st_tcb_at'_cases sts_valid_queues setThreadState_valid_queues'
                  setThreadState_st_tcb
             | simp)+
       apply (simp add: ntfn_relation_def split:list.splits)
      apply (wp set_ntfn_aligned' set_ntfn_valid_objs set_ntfn_valid_objs'
                hoare_vcg_disj_lift weak_sch_act_wf_lift_linear
           | simp add: valid_tcb_state_def valid_tcb_state'_def)+
    apply (clarsimp simp: invs_def valid_state_def valid_ntfn_def 
                          valid_pspace_def neq_Nil_conv
                          ntfn_queued_st_tcb_at valid_sched_def valid_sched_action_def
                  split: option.splits)
   apply (auto simp: valid_ntfn'_def neq_Nil_conv invs'_def valid_state'_def
                     weak_sch_act_wf_def
              split: option.splits)[1]
  -- "ActiveNtfn"
  apply (clarsimp simp add: ntfn_relation_def)
  apply (rule corres_guard_imp)
    apply (rule set_ntfn_corres)
    apply (simp add: ntfn_relation_def combine_ntfn_badges_def
                     combine_ntfn_msgs_def)
   apply (simp add: invs_def valid_state_def valid_ntfn_def)
  apply (simp add: invs'_def valid_state'_def valid_ntfn'_def)
  done

lemma valid_Running'[simp]:
  "valid_tcb_state' Running = \<top>"
  by (rule ext, simp add: valid_tcb_state'_def)

lemma ko_wp_at_state_refs_of':
  "ko_wp_at' P p s \<Longrightarrow> \<exists>ko. P ko \<and> state_refs_of' s p = refs_of' ko"
  apply (clarsimp simp: state_refs_of'_def ko_wp_at'_def)
  apply fastforce
  done

crunch typ'[wp]: setMRs "\<lambda>s. P (typ_at' T p s)"
   (wp: crunch_wps simp: zipWithM_x_mapM)

lemma possibleSwitchTo_sch_act[wp]:
  "\<lbrace>\<lambda>s. sch_act_wf (ksSchedulerAction s) s \<and> st_tcb_at' runnable' t s\<rbrace>
     possibleSwitchTo t b
   \<lbrace>\<lambda>rv s. sch_act_wf (ksSchedulerAction s) s\<rbrace>"
  apply (simp add: possibleSwitchTo_def curDomain_def)
  apply (wp static_imp_wp threadSet_sch_act setQueue_sch_act threadGet_wp
       | simp add: unless_def | wpc)+
  apply (auto simp: obj_at'_def projectKOs tcb_in_cur_domain'_def)
  done

lemmas attemptSwitchTo_sch_act[wp]
    = possibleSwitchTo_sch_act[where b=True, folded attemptSwitchTo_def]

lemma possibleSwitchTo_valid_queues[wp]:
  "\<lbrace>Invariants_H.valid_queues and valid_objs' and (\<lambda>s. sch_act_wf (ksSchedulerAction s) s) and st_tcb_at' runnable' t\<rbrace>
   possibleSwitchTo t b
   \<lbrace>\<lambda>rv. Invariants_H.valid_queues\<rbrace>"
  apply (simp add: possibleSwitchTo_def curDomain_def)
  apply (wp hoare_drop_imps | wpc | simp)+
  apply (auto simp: valid_tcb'_def weak_sch_act_wf_def
              dest: pred_tcb_at'
             elim!: valid_objs_valid_tcbE)
  done

(* FIXME: move *)
lemma valid_queues'_ksSchedulerAction_update[simp]:
  "valid_queues' (s \<lparr>ksSchedulerAction := sa\<rparr>) = valid_queues' s"
  by (simp add: valid_queues'_def)

lemma possibleSwitchTo_ksQ':
  "\<lbrace>(\<lambda>s. t' \<notin> set (ksReadyQueues s p) \<and> sch_act_not t' s) and K(t' \<noteq> t)\<rbrace>
     possibleSwitchTo t same
   \<lbrace>\<lambda>_ s. t' \<notin> set (ksReadyQueues s p)\<rbrace>"
  apply (simp add: possibleSwitchTo_def curDomain_def)
  apply (wp static_imp_wp rescheduleRequired_ksQ' tcbSchedEnqueue_ksQ threadGet_wp
         | wpc
         | simp split del: if_split)+
  apply (auto simp: obj_at'_def)
  done

lemma attemptSwitchTo_ksQ:
  "\<lbrace>(\<lambda>s. t' \<notin> set (ksReadyQueues s p) \<and> sch_act_not t' s) and K (t' \<noteq> t)\<rbrace>
   attemptSwitchTo t \<lbrace>\<lambda>_ s. t' \<notin> set (ksReadyQueues s p)\<rbrace>"
  by (simp add: attemptSwitchTo_def, wp possibleSwitchTo_ksQ', (fastforce)+)

lemma possibleSwitchTo_valid_queues'[wp]:
  "\<lbrace>valid_queues' and (\<lambda>s. sch_act_wf (ksSchedulerAction s) s)
                  and st_tcb_at' runnable' t\<rbrace>
   possibleSwitchTo t b
   \<lbrace>\<lambda>rv. valid_queues'\<rbrace>"
  apply (simp add: possibleSwitchTo_def curDomain_def)
  apply (wp static_imp_wp threadGet_wp | wpc | simp)+
  apply (auto simp: obj_at'_def)
  done

lemmas attemptSwitchTo_vq[wp]
    = possibleSwitchTo_valid_queues[where b=True, folded attemptSwitchTo_def]
      possibleSwitchTo_valid_queues'[where b=True, folded attemptSwitchTo_def]

crunch st_refs_of'[wp]: attemptSwitchTo "\<lambda>s. P (state_refs_of' s)"
  (wp: crunch_wps) 

lemma possibleSwitchTo_iflive[wp]:
  "\<lbrace>if_live_then_nonz_cap' and ex_nonz_cap_to' t
           and (\<lambda>s. sch_act_wf (ksSchedulerAction s) s)\<rbrace>
     possibleSwitchTo t b
   \<lbrace>\<lambda>rv. if_live_then_nonz_cap'\<rbrace>"
  apply (simp add: possibleSwitchTo_def curDomain_def)
  apply (wp | wpc | simp)+
      apply (simp only: imp_conv_disj, wp hoare_vcg_all_lift hoare_vcg_disj_lift)
    apply (wp threadGet_wp)+
  apply (auto simp: obj_at'_def projectKOs)
  done

lemmas attemptSwitchTo_iflive[wp]
    = possibleSwitchTo_iflive[where b=True, folded attemptSwitchTo_def]

crunch ifunsafe[wp]: attemptSwitchTo if_unsafe_then_cap'
  (wp: crunch_wps)
crunch idle'[wp]: attemptSwitchTo valid_idle'
  (wp: crunch_wps)
crunch global_refs'[wp]: attemptSwitchTo valid_global_refs'
  (wp: crunch_wps)
crunch arch_state'[wp]: attemptSwitchTo valid_arch_state'
  (wp: crunch_wps)
crunch irq_node'[wp]: attemptSwitchTo "\<lambda>s. P (irq_node' s)"
  (wp: crunch_wps)
crunch typ_at'[wp]: attemptSwitchTo "\<lambda>s. P (typ_at' T p s)"
  (wp: crunch_wps)
crunch irq_handlers'[wp]: attemptSwitchTo valid_irq_handlers'
  (simp: unless_def tcb_cte_cases_def wp: crunch_wps)
crunch irq_states'[wp]: attemptSwitchTo valid_irq_states'
  (wp: crunch_wps)
crunch pde_mappigns'[wp]: attemptSwitchTo valid_pde_mappings'
  (wp: crunch_wps)

(* Levity: added (20090713 10:04:33) *)
declare setNotification_ct' [wp]

crunch ct'[wp]: sendSignal "\<lambda>s. P (ksCurThread s)"
  (wp: crunch_wps simp: crunch_simps)
crunch it'[wp]: sendSignal "\<lambda>s. P (ksIdleThread s)"
  (wp: crunch_wps simp: crunch_simps)

crunch irqs_masked'[wp]: sendSignal "irqs_masked'"
  (wp: crunch_wps getObject_inv loadObject_default_inv simp: crunch_simps unless_def rule: irqs_masked_lift ignore: getObject)

lemma sts_running_valid_queues:
  "runnable' st \<Longrightarrow> \<lbrace> Invariants_H.valid_queues \<rbrace> setThreadState st t \<lbrace>\<lambda>_. Invariants_H.valid_queues \<rbrace>"
  by (wp sts_valid_queues, clarsimp)

lemma ct_in_state_activatable_imp_simple'[simp]:
  "ct_in_state' activatable' s \<Longrightarrow> ct_in_state' simple' s"
  apply (simp add: ct_in_state'_def)
  apply (erule pred_tcb'_weakenE)
  apply (case_tac st; simp)
  done

lemma setThreadState_nonqueued_state_update:
  "\<lbrace>\<lambda>s. invs' s \<and> st_tcb_at' simple' t s
               \<and> st \<in> {Inactive, Running, Restart, IdleThreadState}
               \<and> (st \<noteq> Inactive \<longrightarrow> ex_nonz_cap_to' t s)
               \<and> (t = ksIdleThread s \<longrightarrow> idle' st)

               \<and> (\<not> runnable' st \<longrightarrow> sch_act_simple s)
               \<and> (\<not> runnable' st \<longrightarrow> (\<forall>p. t \<notin> set (ksReadyQueues s p)))\<rbrace>
  setThreadState st t \<lbrace>\<lambda>rv. invs'\<rbrace>"
  apply (simp add: invs'_def valid_state'_def)
  apply (rule hoare_pre, wp valid_irq_node_lift
                            sts_valid_queues
                            setThreadState_ct_not_inQ)
  apply (clarsimp simp: pred_tcb_at')
  apply (rule conjI, fastforce simp: valid_tcb_state'_def)
  apply (drule simple_st_tcb_at_state_refs_ofD')
  apply (drule bound_tcb_at_state_refs_ofD')
  apply (rule conjI, fastforce)
  apply clarsimp
  apply (erule delta_sym_refs)
   apply (fastforce split: if_split_asm)
  apply (fastforce simp: symreftype_inverse' tcb_bound_refs'_def
                  split: if_split_asm)
  done

lemma cteDeleteOne_reply_cap_to'[wp]:
  "\<lbrace>ex_nonz_cap_to' p and
    cte_wp_at' (\<lambda>c. isReplyCap (cteCap c)) slot\<rbrace>
   cteDeleteOne slot
   \<lbrace>\<lambda>rv. ex_nonz_cap_to' p\<rbrace>"
  apply (simp add: cteDeleteOne_def ex_nonz_cap_to'_def unless_def)
  apply (rule hoare_seq_ext [OF _ getCTE_sp])
  apply (rule hoare_assume_pre)
  apply (subgoal_tac "isReplyCap (cteCap cte)")
   apply (wp hoare_vcg_ex_lift emptySlot_cte_wp_cap_other isFinalCapability_inv
        | clarsimp simp: finaliseCap_def isCap_simps | simp)+
   apply (fastforce simp: cte_wp_at_ctes_of)
  apply (clarsimp simp: cte_wp_at_ctes_of isCap_simps)
  done

lemma switchIfRequiredTo_sch_act[wp]:
  "\<lbrace>\<lambda>s. sch_act_wf (ksSchedulerAction s) s \<and> st_tcb_at' runnable' t s\<rbrace>
    switchIfRequiredTo t
   \<lbrace>\<lambda>rv s. sch_act_wf (ksSchedulerAction s) s\<rbrace>"
  apply (simp add: switchIfRequiredTo_def tcbSchedEnqueue_def)
  apply wp
  done

lemmas switchIfRequiredTo_vq[wp]
    = possibleSwitchTo_valid_queues[where b=True, folded switchIfRequiredTo_def]
      possibleSwitchTo_valid_queues'[where b=True, folded switchIfRequiredTo_def]

crunch st_refs_of'[wp]: switchIfRequiredTo "\<lambda>s. P (state_refs_of' s)" 

lemmas switchIfRequiredTo_iflive[wp]
    = possibleSwitchTo_iflive[where b=False, folded switchIfRequiredTo_def]

crunch ifunsafe[wp]: switchIfRequiredTo if_unsafe_then_cap'
crunch idle'[wp]: switchIfRequiredTo valid_idle'
crunch global_refs'[wp]: switchIfRequiredTo valid_global_refs'
crunch arch_state'[wp]: switchIfRequiredTo valid_arch_state'
crunch irq_node'[wp]: switchIfRequiredTo "\<lambda>s. P (irq_node' s)"
crunch typ_at'[wp]: switchIfRequiredTo "\<lambda>s. P (typ_at' T p s)"
crunch irq_handlers'[wp]: switchIfRequiredTo valid_irq_handlers'
  (simp: unless_def tcb_cte_cases_def)
crunch irq_states'[wp]: switchIfRequiredTo valid_irq_states'
crunch pde_mappings'[wp]: switchIfRequiredTo valid_pde_mappings'
crunch vp[wp]: switchIfRequiredTo valid_pspace'
crunch tcb_at'[wp]: switchIfRequiredTo "tcb_at' t"
crunch ct'[wp]: switchIfRequiredTo "\<lambda>s. P (ksCurThread s)"
  (wp: crunch_wps)
crunch it'[wp]: switchIfRequiredTo "\<lambda>s. P (ksIdleThread s)"
  (wp: crunch_wps)
crunch ct[wp]: switchIfRequiredTo cur_tcb'
  (wp: cur_tcb_lift)

crunch vms'[wp]: setupCallerCap, switchIfRequiredTo, asUser,
    doIPCTransfer "valid_machine_state'"
  (wp: crunch_wps simp: zipWithM_x_mapM_x)

crunch nonz_cap_to'[wp]: cancelSignal "ex_nonz_cap_to' p"
  (wp: crunch_wps simp: crunch_simps)

lemma cancelIPC_nonz_cap_to'[wp]:
  "\<lbrace>ex_nonz_cap_to' p\<rbrace> cancelIPC t \<lbrace>\<lambda>rv. ex_nonz_cap_to' p\<rbrace>"
  apply (simp add: cancelIPC_def getThreadReplySlot_def Let_def
                   capHasProperty_def)
  apply (wp threadSet_cap_to'
       | wpc
       | simp
       | clarsimp elim!: cte_wp_at_weakenE'
       | rule hoare_post_imp[where Q="\<lambda>rv. ex_nonz_cap_to' p"])+
  done


crunch nosch[wp]: activateIdleThread "\<lambda>s. P (ksSchedulerAction s)"
  (ignore: setNextPC)
crunch nosch[wp]: getThreadReplySlot "\<lambda>s. P (ksSchedulerAction s)"
crunch nosch[wp]: isFinalCapability "\<lambda>s. P (ksSchedulerAction s)"
  (simp: Let_def)

crunch pspace_domain_valid[wp]:
        setupCallerCap, switchIfRequiredTo, asUser, setMRs, doIPCTransfer
    "pspace_domain_valid"
  (wp: crunch_wps simp: zipWithM_x_mapM_x)

lemma switchIfRequiredTo_valid_queues:
  "\<lbrace>Invariants_H.valid_queues and valid_objs' and (\<lambda>s. sch_act_wf (ksSchedulerAction s) s) and st_tcb_at' runnable' t\<rbrace>
   switchIfRequiredTo t \<lbrace>\<lambda>_. Invariants_H.valid_queues\<rbrace>"
  apply (simp add: switchIfRequiredTo_def)
  apply wp
  done

lemma switchIfRequiredTo_valid_queues':
  "\<lbrace>valid_queues' and (\<lambda>s. sch_act_wf (ksSchedulerAction s) s) and st_tcb_at' runnable' t\<rbrace>
   switchIfRequiredTo t \<lbrace>\<lambda>_. valid_queues'\<rbrace>"
  by (simp add: switchIfRequiredTo_def, wp)

crunch ksDomScheduleIdx[wp]: setupCallerCap, switchIfRequiredTo, doIPCTransfer, attemptSwitchTo "\<lambda>s. P (ksDomScheduleIdx s)"
  (wp: crunch_wps simp: zipWithM_x_mapM)

crunch invs'[wp]: switchIfRequiredTo "invs'"

lemma setThreadState_not_rct[wp]:
  "\<lbrace>\<lambda>s. ksSchedulerAction s \<noteq> ResumeCurrentThread \<rbrace>
   setThreadState st t
   \<lbrace>\<lambda>_ s. ksSchedulerAction s \<noteq> ResumeCurrentThread \<rbrace>"
  apply (simp add: setThreadState_def)
  apply (wp)
       apply (rule hoare_post_imp [OF _ rescheduleRequired_notresume], simp)
      apply (simp)
      apply (wp)+
  apply simp
  done

lemma cancelAllIPC_not_rct[wp]:
  "\<lbrace>\<lambda>s. ksSchedulerAction s \<noteq> ResumeCurrentThread \<rbrace>
   cancelAllIPC epptr
   \<lbrace>\<lambda>_ s. ksSchedulerAction s \<noteq> ResumeCurrentThread \<rbrace>"
  apply (simp add: cancelAllIPC_def)
  apply (wp | wpc)+
       apply (rule hoare_post_imp [OF _ rescheduleRequired_notresume], simp)
      apply simp
      apply (rule mapM_x_wp_inv)
      apply (wp)+
     apply (rule hoare_post_imp [OF _ rescheduleRequired_notresume], simp)
    apply simp
    apply (rule mapM_x_wp_inv)
    apply (wp)+
  apply (wp hoare_vcg_all_lift hoare_drop_imp)
    apply (simp_all)
  done

lemma cancelAllSignals_not_rct[wp]:
  "\<lbrace>\<lambda>s. ksSchedulerAction s \<noteq> ResumeCurrentThread \<rbrace>
   cancelAllSignals epptr
   \<lbrace>\<lambda>_ s. ksSchedulerAction s \<noteq> ResumeCurrentThread \<rbrace>"
  apply (simp add: cancelAllSignals_def)
  apply (wp | wpc)+
     apply (rule hoare_post_imp [OF _ rescheduleRequired_notresume], simp)
    apply simp
    apply (rule mapM_x_wp_inv)
    apply (wp)+
  apply (wp hoare_vcg_all_lift hoare_drop_imp)
    apply (simp_all)
  done

crunch not_rct[wp]: finaliseCapTrue_standin "\<lambda>s. ksSchedulerAction s \<noteq> ResumeCurrentThread"
(simp: Let_def)

declare setEndpoint_ct' [wp]

lemma cancelIPC_ResumeCurrentThread_imp_notct[wp]:
  "\<lbrace>\<lambda>s. ksSchedulerAction s = ResumeCurrentThread \<longrightarrow> ksCurThread s \<noteq> t'\<rbrace>
   cancelIPC t
   \<lbrace>\<lambda>_ s. ksSchedulerAction s = ResumeCurrentThread \<longrightarrow> ksCurThread s \<noteq> t'\<rbrace>"
  (is "\<lbrace>?PRE t'\<rbrace> _ \<lbrace>_\<rbrace>")
proof -
  have aipc: "\<And>t t' ntfn.
    \<lbrace>\<lambda>s. ksSchedulerAction s = ResumeCurrentThread \<longrightarrow> ksCurThread s \<noteq> t'\<rbrace>
    cancelSignal t ntfn
    \<lbrace>\<lambda>_ s. ksSchedulerAction s = ResumeCurrentThread \<longrightarrow> ksCurThread s \<noteq> t'\<rbrace>"
    apply (simp add: cancelSignal_def)
    apply (wp)[1]
        apply (wp hoare_convert_imp)+
        apply (rule_tac P="\<lambda>s. ksSchedulerAction s \<noteq> ResumeCurrentThread"
                 in hoare_weaken_pre)
          apply (wpc)
           apply (wp | simp)+
       apply (wpc, wp+)
     apply (rule_tac Q="\<lambda>_. ?PRE t'" in hoare_post_imp, clarsimp)
     apply (wp)
    apply simp
    done
  have cdo: "\<And>t t' slot.
    \<lbrace>\<lambda>s. ksSchedulerAction s = ResumeCurrentThread \<longrightarrow> ksCurThread s \<noteq> t'\<rbrace>
    cteDeleteOne slot
    \<lbrace>\<lambda>_ s. ksSchedulerAction s = ResumeCurrentThread \<longrightarrow> ksCurThread s \<noteq> t'\<rbrace>"
    apply (simp add: cteDeleteOne_def unless_def split_def)
    apply (wp)
        apply (wp hoare_convert_imp)[1]
       apply (wp)
      apply (rule_tac Q="\<lambda>_. ?PRE t'" in hoare_post_imp, clarsimp)
      apply (wp hoare_convert_imp | simp)+
     done
  show ?thesis
  apply (simp add: cancelIPC_def Let_def)
  apply (wp, wpc)
          prefer 4 -- "state = Running"
          apply wp
         prefer 7 -- "state = Restart"
         apply wp
        apply (wp)+
           apply (wp hoare_convert_imp)[1]
          apply (wpc, wp+)
        apply (rule_tac Q="\<lambda>_. ?PRE t'" in hoare_post_imp, clarsimp)
        apply (wp cdo)+
         apply (rule_tac Q="\<lambda>_. ?PRE t'" in hoare_post_imp, clarsimp)
         apply ((wp aipc hoare_convert_imp)+)[6]
    apply (wp)
       apply (wp hoare_convert_imp)[1]
      apply (wpc, wp+)
    apply (rule_tac Q="\<lambda>_. ?PRE t'" in hoare_post_imp, clarsimp)
    apply (wp)
   apply (rule_tac Q="\<lambda>_. ?PRE t'" in hoare_post_imp, clarsimp)
   apply (wp)
  apply simp
  done
qed

lemma ntfn_q_refs_no_TCBBound':
  "(x, TCBBound) \<notin> ntfn_q_refs_of' ntfn"
  by (simp add: ntfn_q_refs_of'_def split: ntfn.splits)

crunch nosch[wp]: setMRs "\<lambda>s. P (ksSchedulerAction s)" 

lemma sai_invs'[wp]:
  "\<lbrace>invs' and ex_nonz_cap_to' ntfnptr\<rbrace>
     sendSignal ntfnptr badge \<lbrace>\<lambda>y. invs'\<rbrace>"
  unfolding sendSignal_def
  including no_pre
  apply (rule hoare_seq_ext[OF _ get_ntfn_sp'])
  apply (case_tac "ntfnObj nTFN", simp_all)
    prefer 3
    apply (rename_tac list)
    apply (case_tac list,
           simp_all split del: if_split
                          add: setMessageInfo_def)[1]
    apply (wp hoare_convert_imp [OF asUser_nosch]
              hoare_convert_imp [OF setMRs_nosch])+
     apply (clarsimp simp:conj_comms)
     apply (simp add: invs'_def valid_state'_def)
     apply (wp valid_irq_node_lift sts_valid_objs' setThreadState_ct_not_inQ
               sts_valid_queues [where st="Structures_H.thread_state.Running", simplified]
               set_ntfn_valid_objs' cur_tcb_lift sts_st_tcb'
               hoare_convert_imp [OF setNotification_nosch]
           | simp)+
                                   apply (rule impI)
                                   apply (simp add: invs'_def valid_state'_def)
                                   apply (elim conjE)
                                   apply (drule(1) ct_not_in_ntfnQueue)
                                     apply (simp)+
                                  apply (simp_all add: invs'_def valid_state'_def
                                             split del: if_split)[23]
               apply (clarsimp simp: valid_pspace'_def)
               apply (frule(1) ko_at_valid_objs')
                apply (simp add: projectKOs)
               apply (clarsimp simp: valid_obj'_def valid_ntfn'_def
                          split: list.splits)
              apply clarsimp+
             apply (clarsimp simp: st_tcb_at_refs_of_rev' valid_idle'_def pred_tcb_at'_def
                            dest!: sym_refs_ko_atD' sym_refs_st_tcb_atD' sym_refs_obj_atD'
                           split: list.splits)
            apply (clarsimp simp: valid_pspace'_def)
            apply (frule(1) ko_at_valid_objs')
             apply (simp add: projectKOs)
            apply (clarsimp simp: valid_obj'_def valid_ntfn'_def
                        split: list.splits option.splits)
           apply clarsimp
          apply (clarsimp elim!: if_live_then_nonz_capE' simp:invs'_def valid_state'_def)
          apply (drule(1) sym_refs_ko_atD')
          apply (clarsimp elim!: ko_wp_at'_weakenE
                      intro!: refs_of_live')
         apply (clarsimp split del: if_split)+
        apply (frule ko_at_valid_objs')
          apply (clarsimp simp: valid_pspace'_def)
         apply (simp add: projectKOs)
        apply (clarsimp simp: valid_obj'_def valid_ntfn'_def split del: if_split)
        apply (frule invs_sym')
        apply (drule(1) sym_refs_obj_atD')
        apply (clarsimp split del: if_split cong: if_cong
                           simp: st_tcb_at_refs_of_rev' ep_redux_simps' ntfn_bound_refs'_def)
        apply (frule st_tcb_at_state_refs_ofD')
        apply (erule delta_sym_refs)
         apply (fastforce simp: ntfn_q_refs_no_TCBBound' split: if_split_asm)
        apply (fastforce simp: tcb_bound_refs'_def set_eq_subset symreftype_inverse'
                        split: if_split_asm)
       apply (clarsimp simp: valid_pspace'_def)
      apply clarsimp
     apply (clarsimp simp:invs'_def)
     apply (frule ko_at_valid_objs')
       apply (clarsimp simp: valid_pspace'_def valid_state'_def)
      apply (simp add: projectKOs)
     apply (clarsimp simp: valid_obj'_def valid_ntfn'_def split del: if_split)
    apply (clarsimp simp:invs'_def valid_state'_def valid_pspace'_def)
    apply (frule(1) ko_at_valid_objs')
     apply (simp add: projectKOs)
    apply (clarsimp simp: valid_obj'_def valid_ntfn'_def
                  split: list.splits option.splits)
   apply (case_tac "ntfnBoundTCB nTFN", simp_all)
    apply (wp set_ntfn_minor_invs')
    apply (fastforce simp: valid_ntfn'_def invs'_def valid_state'_def
                    elim!: obj_at'_weakenE
                    dest!: global'_no_ex_cap)
   apply (wp add: hoare_convert_imp [OF asUser_nosch]
             hoare_convert_imp [OF setMRs_nosch]
             setThreadState_nonqueued_state_update sts_st_tcb'
             del: cancelIPC_simple)
     apply (clarsimp | wp cancelIPC_ct')+
    apply (wp set_ntfn_minor_invs' gts_wp' | clarsimp)+
   apply (frule pred_tcb_at')
   by (wp set_ntfn_minor_invs'
        | rule conjI
        | clarsimp elim!: st_tcb_ex_cap''
        | fastforce simp: invs'_def valid_state'_def receiveBlocked_def projectKOs
                          valid_obj'_def valid_ntfn'_def
                   split: thread_state.splits
                   dest!: global'_no_ex_cap st_tcb_ex_cap'' ko_at_valid_objs'
        | fastforce simp: receiveBlocked_def projectKOs pred_tcb_at'_def obj_at'_def
                   dest!: invs_rct_ct_activatable'
                   split: thread_state.splits)+

lemma ncof_invs' [wp]:
  "\<lbrace>invs'\<rbrace> nullCapOnFailure (lookupCap t ref) \<lbrace>\<lambda>rv. invs'\<rbrace>"
  by (simp add: nullCapOnFailure_def | wp)+

lemma ncof_corres:
  "ref = to_bl ref' \<Longrightarrow>
   corres cap_relation (invs and tcb_at t) (invs' and tcb_at' t)
   (null_cap_on_failure (lookup_cap t ref))
   (nullCapOnFailure (lookupCap t ref'))"  
  apply (simp add: nullCapOnFailure_def ncof_is_a_catch)
  apply (rule corres_guard_imp)
    apply (rule corres_split_catch)
       apply (rule corres_trivial, simp)
      apply (rule lc_corres)
     apply wp+
   apply fastforce
  apply fastforce
  done

lemma rfk_corres:
  "corres dc (tcb_at t and invs) (tcb_at' t and invs')
             (reply_from_kernel t r) (replyFromKernel t r)"
  apply (case_tac r)
  apply (clarsimp simp: replyFromKernel_def reply_from_kernel_def
                        badge_register_def badgeRegister_def)
  apply (rule corres_guard_imp)
    apply (rule corres_split_eqr [OF _ lipcb_corres])
      apply (rule corres_split [OF _ user_setreg_corres])
        apply (rule corres_split_eqr [OF _ set_mrs_corres])
           apply (rule set_mi_corres)
           apply (wp hoare_case_option_wp hoare_valid_ipc_buffer_ptr_typ_at'
                  | clarsimp)+
  done

lemma rfk_invs': 
  "\<lbrace>invs' and tcb_at' t\<rbrace> replyFromKernel t r \<lbrace>\<lambda>rv. invs'\<rbrace>"
  apply (simp add: replyFromKernel_def)
  apply (cases r)
   apply (wp guarded_lookup_valid_cap'
           | clarsimp)+
  done

crunch nosch[wp]: replyFromKernel "\<lambda>s. P (ksSchedulerAction s)"

lemma complete_signal_corres:
  "corres dc (ntfn_at ntfnptr and tcb_at tcb and pspace_aligned and valid_objs(* and obj_at (\<lambda>ko. ko = Notification ntfn \<and> Ipc_A.isActive ntfn) ntfnptr*))
             (ntfn_at' ntfnptr and tcb_at' tcb and valid_pspace' and obj_at' isActive ntfnptr)
             (complete_signal ntfnptr tcb) (completeSignal ntfnptr tcb)"
  apply (simp add: complete_signal_def completeSignal_def)
  apply (rule corres_guard_imp)
    apply (rule_tac R'="\<lambda>ntfn. ntfn_at' ntfnptr and tcb_at' tcb and valid_pspace'
                         and valid_ntfn' ntfn and (\<lambda>_. isActive ntfn)"
                                in corres_split [OF _ get_ntfn_corres])
      apply (rule corres_gen_asm2)
      apply (case_tac "ntfn_obj rv")
        apply (clarsimp simp: ntfn_relation_def isActive_def
                       split: ntfn.splits Structures_H.notification.splits)+
      apply (rule corres_guard2_imp)
       apply (simp add: badgeRegister_def badge_register_def)
       apply (rule corres_split[OF set_ntfn_corres user_setreg_corres])
         apply (clarsimp simp: ntfn_relation_def)
        apply (wp set_ntfn_valid_objs get_ntfn_wp getNotification_wp | clarsimp simp: valid_ntfn'_def)+
  apply (clarsimp simp: valid_pspace'_def)
  apply (frule_tac P="(\<lambda>k. k = ntfn)" in obj_at_valid_objs', assumption)
  apply (clarsimp simp: projectKOs valid_obj'_def valid_ntfn'_def obj_at'_def)
  done


lemma do_nbrecv_failed_transfer_corres:
  "corres dc (tcb_at thread)
            (tcb_at' thread)
            (do_nbrecv_failed_transfer thread)
            (doNBRecvFailedTransfer thread)"
  unfolding do_nbrecv_failed_transfer_def doNBRecvFailedTransfer_def
  by (simp add: badgeRegister_def badge_register_def, rule user_setreg_corres)
  
lemma receive_ipc_corres:
  assumes "is_ep_cap cap" and "cap_relation cap cap'"
  shows "
   corres dc (einvs and valid_sched and tcb_at thread and valid_cap cap and ex_nonz_cap_to thread
              and cte_wp_at (\<lambda>c. c = cap.NullCap) (thread, tcb_cnode_index 3))
             (invs' and tcb_at' thread and valid_cap' cap')
             (receive_ipc thread cap isBlocking) (receiveIPC thread cap' isBlocking)"
  apply (insert assms)
  apply (simp add: receive_ipc_def receiveIPC_def
              split del: if_split)
  apply (case_tac cap, simp_all add: isEndpointCap_def)
  apply (rename_tac word1 word2 right)
  apply clarsimp
  apply (rule corres_guard_imp)
    apply (rule corres_split [OF _ get_ep_corres])
      apply (rule corres_guard_imp)
        apply (rule corres_split [OF _ gbn_corres])
          apply (rule_tac r'="ntfn_relation" in corres_split)
             apply (rule corres_if)
               apply (clarsimp simp: ntfn_relation_def Ipc_A.isActive_def Endpoint_H.isActive_def
                              split: Structures_A.ntfn.splits Structures_H.notification.splits)
              apply clarsimp
              apply (rule complete_signal_corres)
             apply (rule_tac P="einvs and valid_sched and tcb_at thread and 
                                       ep_at word1 and valid_ep ep and 
                                       obj_at (\<lambda>k. k = Endpoint ep) word1
                                       and cte_wp_at (\<lambda>c. c = cap.NullCap) (thread, tcb_cnode_index 3)
                                       and ex_nonz_cap_to thread" and 
                                 P'="invs' and tcb_at' thread and ep_at' word1 and 
                                           valid_ep' epa" 
                                 in corres_inst)
             apply (case_tac ep)
               -- "IdleEP"
               apply (simp add: ep_relation_def)
               apply (rule corres_guard_imp)
                 apply (case_tac isBlocking; simp)
                  apply (rule corres_split [OF _ sts_corres])
                     apply (rule set_ep_corres)
                     apply (simp add: ep_relation_def)
                    apply simp
                   apply wp+
                 apply (rule corres_guard_imp, rule do_nbrecv_failed_transfer_corres, simp)
                 apply simp
                apply (clarsimp simp add: invs_def valid_state_def valid_pspace_def
               valid_tcb_state_def st_tcb_at_tcb_at)
               apply auto[1]
       -- "SendEP"
       apply (simp add: ep_relation_def)
       apply (rename_tac list)
       apply (rule_tac F="list \<noteq> []" in corres_req)
        apply (clarsimp simp: valid_ep_def)
       apply (case_tac list, simp_all split del: if_split)[1]
       apply (rule corres_guard_imp)
         apply (rule corres_split [OF _ set_ep_corres])
            apply (rule corres_split [OF _ gts_corres])
              apply (rule_tac 
                       F="\<exists>data.
                           sender_state = 
                           Structures_A.thread_state.BlockedOnSend word1 data"
                       in corres_gen_asm)
              apply (clarsimp simp: isSend_def case_bool_If
                                    case_option_If if3_fold
                         split del: if_split cong: if_cong)
              apply (rule corres_split [OF _ dit_corres])
                apply (simp split del: if_split cong: if_cong)
                apply (fold dc_def)[1]
                apply (rule corres_split [OF _ threadget_fault_corres
                                             thread_get_inv threadGet_inv])
                apply (rule_tac P="valid_objs and valid_mdb and valid_list
                                        and valid_sched
                                        and cur_tcb
                                        and valid_reply_caps
                                        and pspace_aligned and pspace_distinct
                                        and st_tcb_at (Not \<circ> awaiting_reply) a
                                        and st_tcb_at (Not \<circ> halted) a
                                        and tcb_at thread and valid_reply_masters
                                        and cte_wp_at (\<lambda>c. c = cap.NullCap)
                                                      (thread, tcb_cnode_index 3)"
                            and P'="tcb_at' a and tcb_at' thread and cur_tcb'
                                              and Invariants_H.valid_queues
                                              and valid_queues'
                                              and valid_pspace'
                                              and valid_objs'
                                        and (\<lambda>s. weak_sch_act_wf (ksSchedulerAction s) s)"
                             in corres_guard_imp [OF corres_if])
                    apply (simp add: fault_rel_optionation_def)
                   apply (rule corres_if2 [OF _ setup_caller_corres sts_corres])
                           apply simp
                          apply simp
                         apply (rule corres_split [OF _ sts_corres])
                            apply (rule switchIfRequiredTo_corres)
                           apply simp
                          apply (wp sts_st_tcb_at' set_thread_state_runnable_weak_valid_sched_action
                               | simp)+
                         apply (wp sts_st_tcb_at'_cases sts_valid_queues setThreadState_valid_queues'
                                   setThreadState_st_tcb
                              | simp)+
                        apply (clarsimp simp: st_tcb_at_tcb_at st_tcb_def2 valid_sched_def
                                              valid_sched_action_def)
                       apply (clarsimp split: if_split_asm)
                      apply (clarsimp | wp do_ipc_transfer_tcb_caps)+
                     apply (rule_tac Q="\<lambda>_ s. sch_act_wf (ksSchedulerAction s) s"
                           in hoare_post_imp, erule sch_act_wf_weak)
               apply (wp sts_st_tcb' gts_st_tcb_at | simp)+
                  apply (case_tac lista, simp_all add: ep_relation_def)[1]
                 apply (simp cong: list.case_cong)
                 apply wp
                apply simp
         apply (wp weak_sch_act_wf_lift_linear setEndpoint_valid_mdb' set_ep_valid_objs')
               apply (clarsimp split: list.split)
               apply (clarsimp simp add: invs_def valid_state_def st_tcb_at_tcb_at)
               apply (clarsimp simp add: valid_ep_def valid_pspace_def)
               apply (drule(1) sym_refs_obj_atD[where P="\<lambda>ko. ko = Endpoint e" for e])
               apply (fastforce simp: st_tcb_at_refs_of_rev elim: st_tcb_weakenE)
              apply (auto simp: valid_ep'_def invs'_def valid_state'_def split: list.split)[1]
             -- "RecvEP"
             apply (simp add: ep_relation_def)
             apply (rule_tac corres_guard_imp)
               apply (case_tac isBlocking; simp)
                apply (rule corres_split [OF _ sts_corres])
                   apply (rule set_ep_corres)
                   apply (simp add: ep_relation_def)
                  apply simp
                 apply wp+
               apply (rule corres_guard_imp, rule do_nbrecv_failed_transfer_corres, simp)
               apply simp
              apply (clarsimp simp: valid_tcb_state_def)
             apply (clarsimp simp add: valid_tcb_state'_def)
            apply (rule corres_option_split[rotated 2])
              apply (rule get_ntfn_corres)
             apply clarsimp
            apply (rule corres_trivial, simp add: ntfn_relation_def default_notification_def
                                                  default_ntfn_def)
           apply (wp get_ntfn_wp getNotification_wp gbn_wp gbn_wp' hoare_vcg_all_lift hoare_vcg_imp_lift
                     hoare_vcg_if_lift
                | wpc | simp | clarsimp)+
   apply (clarsimp simp: valid_cap_def invs_psp_aligned invs_valid_objs pred_tcb_at_def
                         valid_obj_def valid_tcb_def valid_bound_ntfn_def
                  dest!: invs_valid_objs
                  elim!: obj_at_valid_objsE
                  split: option.splits)
  apply (auto simp: valid_cap'_def invs_valid_pspace' valid_obj'_def valid_tcb'_def
                    valid_bound_ntfn'_def obj_at'_def projectKOs pred_tcb_at'_def
             dest!: invs_valid_objs' obj_at_valid_objs'
             split: option.splits)
  done

lemma receive_signal_corres:
 "\<lbrakk> is_ntfn_cap cap; cap_relation cap cap' \<rbrakk> \<Longrightarrow>
  corres dc (invs and st_tcb_at active thread and valid_cap cap and ex_nonz_cap_to thread)
            (invs' and tcb_at' thread and valid_cap' cap')
            (receive_signal thread cap isBlocking) (receiveSignal thread cap' isBlocking)"
  apply (simp add: receive_signal_def receiveSignal_def)
  apply (case_tac cap, simp_all add: isEndpointCap_def)
  apply (rename_tac word1 word2 rights)
  apply (rule corres_guard_imp)
    apply (rule_tac R="\<lambda>rv. invs and tcb_at thread and st_tcb_at active thread and
                            ntfn_at word1 and ex_nonz_cap_to thread and
                            valid_ntfn rv and
                            obj_at (\<lambda>k. k = Notification rv) word1" and
                            R'="\<lambda>rv'. invs' and tcb_at' thread and ntfn_at' word1 and
                            valid_ntfn' rv'"
                         in corres_split [OF _ get_ntfn_corres])
      apply clarsimp
      apply (case_tac "ntfn_obj rv")
        -- "IdleNtfn"
        apply (simp add: ntfn_relation_def)
        apply (rule corres_guard_imp)
          apply (case_tac isBlocking; simp)
           apply (rule corres_split [OF _ sts_corres])
              apply (rule set_ntfn_corres)
              apply (simp add: ntfn_relation_def)
             apply simp
            apply wp+
          apply (rule corres_guard_imp, rule do_nbrecv_failed_transfer_corres, simp+)
       -- "WaitingNtfn"
       apply (simp add: ntfn_relation_def)
       apply (rule corres_guard_imp)
         apply (case_tac isBlocking; simp)
          apply (rule corres_split[OF _ sts_corres])
             apply (rule set_ntfn_corres)
             apply (simp add: ntfn_relation_def)
            apply simp
           apply wp+
         apply (rule corres_guard_imp)
           apply (rule do_nbrecv_failed_transfer_corres, simp+)
      -- "ActiveNtfn"
      apply (simp add: ntfn_relation_def)
      apply (rule corres_guard_imp)
        apply (simp add: badgeRegister_def badge_register_def)
        apply (rule corres_split [OF _ user_setreg_corres])
          apply (rule set_ntfn_corres)
          apply (simp add: ntfn_relation_def)
         apply wp+
       apply (fastforce simp: invs_def valid_state_def valid_pspace_def
                       elim!: st_tcb_weakenE)
      apply (clarsimp simp: invs'_def valid_state'_def valid_pspace'_def)
     apply wp+
   apply (clarsimp simp add: valid_cap_def st_tcb_at_tcb_at)
  apply (clarsimp simp add: valid_cap'_def)
  done

lemma tg_sp':
  "\<lbrace>P\<rbrace> threadGet f p \<lbrace>\<lambda>t. obj_at' (\<lambda>t'. f t' = t) p and P\<rbrace>"
  including no_pre
  apply (simp add: threadGet_def)
  apply wp
  apply (rule hoare_strengthen_post)
   apply (rule getObject_tcb_sp)
  apply clarsimp
  apply (erule obj_at'_weakenE)
  apply simp
  done

declare lookup_cap_valid' [wp]
  
lemma send_fault_ipc_corres:
  "valid_fault f \<Longrightarrow> fr f f' \<Longrightarrow>
  corres (fr \<oplus> dc) 
         (einvs and st_tcb_at active thread and ex_nonz_cap_to thread)
         (invs' and sch_act_not thread and tcb_at' thread)
         (send_fault_ipc thread f) (sendFaultIPC thread f')"
  apply (simp add: send_fault_ipc_def sendFaultIPC_def
                   liftE_bindE Let_def)
  apply (rule corres_guard_imp)
    apply (rule corres_split [where r'="\<lambda>fh fh'. fh = to_bl fh'"])
       apply simp
       apply (rule corres_splitEE)
          prefer 2
          apply (rule corres_cap_fault)
          apply (rule lookup_cap_corres, rule refl)
         apply (rule_tac P="einvs and st_tcb_at active thread
                                 and valid_cap handler_cap and ex_nonz_cap_to thread" 
                     and P'="invs' and tcb_at' thread and sch_act_not thread
                                   and valid_cap' handlerCap" 
                     in corres_inst)
         apply (case_tac handler_cap,
                simp_all add: isCap_defs lookup_failure_map_def
                              case_bool_If If_rearrage
                   split del: if_split cong: if_cong)[1]
          apply (rule corres_guard_imp)
            apply (rule corres_if2 [OF refl])
             apply (simp add: dc_def[symmetric])
             apply (rule corres_split [OF send_ipc_corres threadset_corres], simp_all)[1]
               apply (simp add: tcb_relation_def fault_rel_optionation_def exst_same_def)+
              apply (wp thread_set_invs_trivial thread_set_no_change_tcb_state
                        thread_set_typ_at ep_at_typ_at ex_nonz_cap_to_pres
                        thread_set_cte_wp_at_trivial thread_set_not_state_valid_sched
                   | simp add: tcb_cap_cases_def)+
             apply ((wp threadSet_invs_trivial threadSet_tcb'
                   | simp add: tcb_cte_cases_def
                   | wp_once sch_act_sane_lift)+)[1]
            apply (rule corres_trivial, simp add: lookup_failure_map_def)
           apply (clarsimp simp: st_tcb_at_tcb_at split: if_split)
           apply (simp add: valid_cap_def)
          apply (clarsimp simp: valid_cap'_def inQ_def)
          apply auto[1]
         apply (clarsimp simp: lookup_failure_map_def)
        apply wp+
      apply (rule threadget_corres)
      apply (simp add: tcb_relation_def)
     apply wp+
   apply (fastforce elim: st_tcb_at_tcb_at)
  apply fastforce
  done

lemma gets_the_noop_corres:
  assumes P: "\<And>s. P s \<Longrightarrow> f s \<noteq> None"
  shows "corres dc P P' (gets_the f) (return x)"
  apply (clarsimp simp: corres_underlying_def gets_the_def
                        return_def gets_def bind_def get_def)
  apply (clarsimp simp: assert_opt_def return_def dest!: P)
  done

lemma hdf_corres:
  "corres dc (tcb_at thread)
             (tcb_at' thread and (\<lambda>s. weak_sch_act_wf (ksSchedulerAction s) s))
             (handle_double_fault thread f ft) 
             (handleDoubleFault thread f' ft')"
  apply (simp add: handle_double_fault_def handleDoubleFault_def)
  apply (rule corres_guard_imp)
    apply (subst bind_return [symmetric],
           rule corres_split' [OF sts_corres])
       apply simp
      apply (rule corres_noop2)
         apply (simp add: exs_valid_def return_def)
        apply (rule hoare_eq_P)
        apply wp
        apply (rule asUser_inv)
        apply (rule getRestartPC_inv)
       apply (wp no_fail_getRestartPC)+
    apply (wp|simp)+
  done

crunch tcb' [wp]: sendFaultIPC "tcb_at' t" (wp: crunch_wps)

lemma possibleSwitchTo_weak_sch_act[wp]:
  "\<lbrace>\<lambda>s. weak_sch_act_wf (ksSchedulerAction s) s \<and> st_tcb_at' runnable' t s \<and> tcb_in_cur_domain' t s\<rbrace>
      possibleSwitchTo t b
   \<lbrace>\<lambda>rv s. weak_sch_act_wf (ksSchedulerAction s) s\<rbrace>"
  apply (simp add: possibleSwitchTo_def setSchedulerAction_def curDomain_def)
  apply (wp static_imp_wp rescheduleRequired_weak_sch_act_wf threadGet_wp | wpc)+
  apply (clarsimp simp: obj_at'_def projectKOs weak_sch_act_wf_def
                        objBits_simps ps_clear_def)
  done

crunch typ_at'[wp]: receiveIPC "\<lambda>s. P (typ_at' T p s)"
  (wp: crunch_wps)

lemmas receiveIPC_typ_ats[wp] = typ_at_lifts [OF receiveIPC_typ_at']

crunch typ_at'[wp]: receiveSignal "\<lambda>s. P (typ_at' T p s)"
  (wp: crunch_wps)

lemmas receiveAIPC_typ_ats[wp] = typ_at_lifts [OF receiveSignal_typ_at']

declare cart_singleton_empty[simp]

lemma cte_wp_at_queues[simp]:
  "cte_wp_at' P p (ksReadyQueues_update f s) = cte_wp_at' P p s"
  by (fastforce intro: cte_wp_at'_pspaceI)

declare cart_singleton_empty2[simp]

crunch aligned'[wp]: setupCallerCap "pspace_aligned'"
  (wp: crunch_wps)
crunch distinct'[wp]: setupCallerCap "pspace_distinct'"
  (wp: crunch_wps)
crunch cur_tcb[wp]: setupCallerCap "cur_tcb'"
  (wp: crunch_wps)

lemma setupCallerCap_valid_objs[wp]:
  "\<lbrace>valid_objs' and tcb_at' sender\<rbrace> setupCallerCap sender receiver \<lbrace>\<lambda>rv. valid_objs'\<rbrace>"
  apply (simp add: setupCallerCap_def getThreadCallerSlot_def
                   getThreadReplySlot_def)
  apply (rule hoare_pre)
   apply wp
   apply (wp sts_valid_objs' hoare_drop_imps hoare_vcg_all_lift)+
  apply (clarsimp simp: valid_cap'_def valid_tcb_state'_def)
  apply (drule obj_at_aligned')
   apply (simp add: objBits_simps capAligned_def word_bits_conv isCap_simps)+
  done

lemma setupCallerCap_state_refs_of[wp]:
  "\<lbrace>\<lambda>s. P ((state_refs_of' s) (sender := {r \<in> state_refs_of' s sender. snd r = TCBBound}))\<rbrace>
     setupCallerCap sender rcvr
   \<lbrace>\<lambda>rv s. P (state_refs_of' s)\<rbrace>"
  apply (simp add: setupCallerCap_def getThreadCallerSlot_def
                   getThreadReplySlot_def)
  apply (wp hoare_drop_imps)
  apply (simp add: fun_upd_def cong: if_cong)
  done

crunch sch_act_wf: setupCallerCap
  "\<lambda>s. sch_act_wf (ksSchedulerAction s) s"
  (wp: crunch_wps ssa_sch_act sts_sch_act rule: sch_act_wf_lift ignore:setObject)

lemma setCTE_valid_queues[wp]:
  "\<lbrace>Invariants_H.valid_queues\<rbrace> setCTE ptr val \<lbrace>\<lambda>rv. Invariants_H.valid_queues\<rbrace>"
  by (wp valid_queues_lift setCTE_pred_tcb_at')

crunch vq[wp]: cteInsert "Invariants_H.valid_queues"
  (wp: crunch_wps)

crunch vq[wp]: getThreadCallerSlot "Invariants_H.valid_queues"
  (wp: crunch_wps)

crunch vq[wp]: getThreadReplySlot "Invariants_H.valid_queues"
  (wp: crunch_wps)

lemma setupCallerCap_vq[wp]:
  "\<lbrace>Invariants_H.valid_queues and (\<lambda>s. \<forall>p. send \<notin> set (ksReadyQueues s p))\<rbrace>
   setupCallerCap send recv \<lbrace>\<lambda>_. Invariants_H.valid_queues\<rbrace>"
  apply (simp add: setupCallerCap_def)
  apply (wp crunch_wps sts_valid_queues)
  apply (fastforce simp: valid_queues_def obj_at'_def inQ_def)
  done

crunch vq'[wp]: setupCallerCap "valid_queues'"
  (wp: crunch_wps)

lemma is_derived_ReplyCap' [simp]:
  "\<And>m p. is_derived' m p (capability.ReplyCap t False) = (\<lambda>c. c = capability.ReplyCap t True)"
  apply (subst fun_eq_iff)
  apply clarsimp
  apply (case_tac x, simp_all add: is_derived'_def isCap_simps
                                   badge_derived'_def
                                   vsCapRef_def)
  done

lemma unique_master_reply_cap':
  "\<And>c t. (isReplyCap c \<and> capReplyMaster c \<and> capTCBPtr c = t) = (c = capability.ReplyCap t True)"
  by (fastforce simp: isCap_simps conj_comms)

lemma getSlotCap_cte_wp_at:
  "\<lbrace>\<top>\<rbrace> getSlotCap sl \<lbrace>\<lambda>rv. cte_wp_at' (\<lambda>c. cteCap c = rv) sl\<rbrace>"
  apply (simp add: getSlotCap_def)
  apply (wp getCTE_wp)
  apply (clarsimp simp: cte_wp_at_ctes_of)
  done

crunch no_0_obj'[wp]: setThreadState no_0_obj'

lemma setupCallerCap_vp[wp]:
  "\<lbrace>valid_pspace' and tcb_at' sender and tcb_at' rcvr\<rbrace>
   setupCallerCap sender rcvr \<lbrace>\<lambda>rv. valid_pspace'\<rbrace>"
  apply (simp add: valid_pspace'_def setupCallerCap_def getThreadCallerSlot_def
                   getThreadReplySlot_def locateSlot_conv getSlotCap_def)
  apply (wp getCTE_wp)
  apply (rule_tac Q="\<lambda>_. valid_pspace' and
                         tcb_at' sender and tcb_at' rcvr"
                  in hoare_post_imp)
   apply (clarsimp simp: valid_cap'_def o_def cte_wp_at_ctes_of isCap_simps
                         valid_pspace'_def)
   apply (frule(1) ctes_of_valid', simp add: valid_cap'_def capAligned_def)
   apply clarsimp
  apply (wp | simp add: valid_pspace'_def valid_tcb_state'_def)+
  done

declare haskell_assert_inv[wp del]

lemma setupCallerCap_iflive[wp]:
  "\<lbrace>if_live_then_nonz_cap' and ex_nonz_cap_to' sender\<rbrace>
   setupCallerCap sender rcvr
   \<lbrace>\<lambda>rv. if_live_then_nonz_cap'\<rbrace>"
  unfolding setupCallerCap_def getThreadCallerSlot_def
            getThreadReplySlot_def locateSlot_conv
  by (wp getSlotCap_cte_wp_at
          | simp add: unique_master_reply_cap'
          | strengthen eq_imp_strg)+

lemma setupCallerCap_ifunsafe[wp]:
  "\<lbrace>if_unsafe_then_cap' and valid_objs' and
    ex_nonz_cap_to' rcvr and tcb_at' rcvr\<rbrace>
   setupCallerCap sender rcvr
   \<lbrace>\<lambda>rv. if_unsafe_then_cap'\<rbrace>"
  unfolding setupCallerCap_def getThreadCallerSlot_def
            getThreadReplySlot_def locateSlot_conv
  apply (wp getSlotCap_cte_wp_at
       | simp add: unique_master_reply_cap' | strengthen eq_imp_strg)+
   apply (rule_tac Q="\<lambda>rv. valid_objs' and tcb_at' rcvr and ex_nonz_cap_to' rcvr"
                in hoare_post_imp)
    apply (clarsimp simp: ex_nonz_tcb_cte_caps' tcbCallerSlot_def
                          objBits_def objBitsKO_def dom_def cte_level_bits_def)
   apply (wp sts_valid_objs' | simp)+
     apply (clarsimp simp: valid_tcb_state'_def)+
  done

lemma setupCallerCap_global_refs'[wp]:
  "\<lbrace>valid_global_refs'\<rbrace>
   setupCallerCap sender rcvr \<lbrace>\<lambda>rv. valid_global_refs'\<rbrace>"
  unfolding setupCallerCap_def getThreadCallerSlot_def
            getThreadReplySlot_def locateSlot_conv
  by (wp getSlotCap_cte_wp_at
    | simp add: o_def unique_master_reply_cap'
    | strengthen eq_imp_strg
    | wp_once getCTE_wp | clarsimp simp: cte_wp_at_ctes_of)+

crunch valid_arch'[wp]: setupCallerCap "valid_arch_state'"
  (wp: hoare_drop_imps)

crunch typ'[wp]: setupCallerCap "\<lambda>s. P (typ_at' T p s)"

crunch irq_node'[wp]: setupCallerCap "\<lambda>s. P (irq_node' s)"
  (wp: hoare_drop_imps)

lemma setupCallerCap_irq_handlers'[wp]:
  "\<lbrace>valid_irq_handlers'\<rbrace>
   setupCallerCap sender rcvr
   \<lbrace>\<lambda>rv. valid_irq_handlers'\<rbrace>"
  unfolding setupCallerCap_def getThreadCallerSlot_def
            getThreadReplySlot_def locateSlot_conv
  by (wp hoare_drop_imps | simp)+

lemma cteInsert_cap_to':
  "\<lbrace>ex_nonz_cap_to' p and cte_wp_at' (\<lambda>c. cteCap c = NullCap) dest\<rbrace>
     cteInsert cap src dest
   \<lbrace>\<lambda>rv. ex_nonz_cap_to' p\<rbrace>"
  apply (simp    add: cteInsert_def ex_nonz_cap_to'_def
                      updateCap_def setUntypedCapAsFull_def
           split del: if_split)
  apply (rule hoare_pre, rule hoare_vcg_ex_lift)
   apply (wp updateMDB_weak_cte_wp_at
             setCTE_weak_cte_wp_at
           | simp
           | rule hoare_drop_imps)+
  apply (wp getCTE_wp)
  apply clarsimp
  apply (rule_tac x=cref in exI)
  apply (rule conjI)
   apply (clarsimp simp: cte_wp_at_ctes_of)+
  done

crunch cap_to'[wp]: setExtraBadge "ex_nonz_cap_to' p"

crunch cap_to'[wp]: doIPCTransfer "ex_nonz_cap_to' p"
  (ignore: transferCapsToSlots 
       wp: crunch_wps transferCapsToSlots_pres2 cteInsert_cap_to' hoare_vcg_const_Ball_lift 
     simp: zipWithM_x_mapM ball_conj_distrib)

lemma st_tcb_idle':
  "\<lbrakk>valid_idle' s; st_tcb_at' P t s\<rbrakk> \<Longrightarrow>
   (t = ksIdleThread s) \<longrightarrow> P IdleThreadState"
  by (clarsimp simp: valid_idle'_def pred_tcb_at'_def obj_at'_def)

crunch idle'[wp]: getThreadCallerSlot "valid_idle'"
crunch idle'[wp]: getThreadReplySlot "valid_idle'"

crunch it[wp]: setupCallerCap "\<lambda>s. P (ksIdleThread s)"
  (simp: updateObject_cte_inv wp: crunch_wps)

lemma setupCallerCap_idle'[wp]:
  "\<lbrace>valid_idle' and valid_pspace' and
    (\<lambda>s. st \<noteq> ksIdleThread s \<and> rt \<noteq> ksIdleThread s)\<rbrace>
   setupCallerCap st rt
   \<lbrace>\<lambda>_. valid_idle'\<rbrace>"
  by (simp add: setupCallerCap_def capRange_def | wp hoare_drop_imps)+

crunch idle'[wp]: doIPCTransfer "valid_idle'"
  (wp: crunch_wps simp: crunch_simps ignore: transferCapsToSlots)

crunch it[wp]: setExtraBadge "\<lambda>s. P (ksIdleThread s)"
crunch it[wp]: receiveIPC "\<lambda>s. P (ksIdleThread s)"
  (ignore: transferCapsToSlots 
       wp: transferCapsToSlots_pres2 crunch_wps hoare_vcg_const_Ball_lift
     simp: crunch_simps ball_conj_distrib)

crunch irq_states' [wp]: setupCallerCap valid_irq_states'
  (wp: crunch_wps)

crunch pde_mappings' [wp]: setupCallerCap valid_pde_mappings'
  (wp: crunch_wps)

crunch irqs_masked' [wp]: receiveIPC "irqs_masked'"
  (wp: crunch_wps rule: irqs_masked_lift)

crunch ct_not_inQ[wp]: getThreadCallerSlot "ct_not_inQ"
crunch ct_not_inQ[wp]: getThreadReplySlot "ct_not_inQ"

lemma setupCallerCap_ct_not_inQ[wp]:
  "\<lbrace>ct_not_inQ\<rbrace> setupCallerCap sender receiver \<lbrace>\<lambda>_. ct_not_inQ\<rbrace>"
  apply (simp add: setupCallerCap_def)
  apply (wp hoare_drop_imp setThreadState_ct_not_inQ)
  done

lemma copyMRs_ksQ[wp]:
  "\<lbrace>\<lambda>s. P (ksReadyQueues s p)\<rbrace> copyMRs a b c d e
        \<lbrace>\<lambda>_ s. P (ksReadyQueues s p)\<rbrace>"
  apply (simp add: copyMRs_def msgRegisters_def)
by (case_tac b; case_tac d; simp; wp mapM_wp')

crunch ksQ'[wp]: copyMRs "\<lambda>s. P (ksReadyQueues s)"
  (wp: mapM_wp' hoare_drop_imps simp: crunch_simps)

crunch ksQ[wp]: doIPCTransfer "\<lambda>s. P (ksReadyQueues s)"
  (wp: hoare_drop_imps hoare_vcg_split_case_option
       mapM_wp'
   simp: split_def zipWithM_x_mapM)

crunch ct'[wp]: doIPCTransfer "\<lambda>s. P (ksCurThread s)"
  (wp: hoare_drop_imps hoare_vcg_split_case_option
       mapM_wp'
   simp: split_def zipWithM_x_mapM)

lemma asUser_ct_not_inQ[wp]:
  "\<lbrace>ct_not_inQ\<rbrace> asUser t m \<lbrace>\<lambda>rv. ct_not_inQ\<rbrace>"
  apply (simp add: asUser_def split_def)
  apply (wp hoare_drop_imps threadSet_not_inQ | simp)+
  done

crunch ct_not_inQ[wp]: copyMRs "ct_not_inQ"
  (wp: mapM_wp' hoare_drop_imps simp: crunch_simps)

crunch ct_not_inQ[wp]: doIPCTransfer "ct_not_inQ"
  (ignore: getRestartPC setRegister transferCapsToSlots
   wp: hoare_drop_imps hoare_vcg_split_case_option
       mapM_wp'
   simp: split_def zipWithM_x_mapM)

lemma ntfn_q_refs_no_bound_refs': "rf : ntfn_q_refs_of' (ntfnObj ob) \<Longrightarrow> rf ~: ntfn_bound_refs' (ntfnBoundTCB ob')"
  by (auto simp add: ntfn_q_refs_of'_def ntfn_bound_refs'_def
           split: Structures_H.ntfn.splits)

lemma completeSignal_invs:
  "\<lbrace>invs' and tcb_at' tcb\<rbrace>
     completeSignal ntfnptr tcb
   \<lbrace>\<lambda>_. invs'\<rbrace>"
  apply (simp add: completeSignal_def)
  apply (rule hoare_seq_ext[OF _ get_ntfn_sp'])
  apply (rule hoare_pre)
   apply (wp set_ntfn_minor_invs' | wpc | simp)+
    apply (rule_tac Q="\<lambda>_ s. (state_refs_of' s ntfnptr = ntfn_bound_refs' (ntfnBoundTCB ntfn)) 
                           \<and> ntfn_at' ntfnptr s 
                           \<and> valid_ntfn' (ntfnObj_update (\<lambda>_. Structures_H.ntfn.IdleNtfn) ntfn) s 
                           \<and> ((\<exists>y. ntfnBoundTCB ntfn = Some y) \<longrightarrow> ex_nonz_cap_to' ntfnptr s)
                           \<and> ntfnptr \<noteq> ksIdleThread s"
                          in hoare_strengthen_post)
     apply ((wp hoare_vcg_ex_lift static_imp_wp | wpc | simp add: valid_ntfn'_def)+)[1]
    apply (clarsimp simp: obj_at'_def state_refs_of'_def typ_at'_def ko_wp_at'_def  projectKOs split: option.splits)
    apply (blast dest: ntfn_q_refs_no_bound_refs')
   apply wp
  apply (subgoal_tac "valid_ntfn' ntfn s")
   apply (subgoal_tac "ntfnptr \<noteq> ksIdleThread s")
    apply (fastforce simp: valid_ntfn'_def valid_bound_tcb'_def projectKOs ko_at_state_refs_ofD'
                     elim: obj_at'_weakenE
                           if_live_then_nonz_capD'[OF invs_iflive'
                                                      obj_at'_real_def[THEN meta_eq_to_obj_eq,
                                                                       THEN iffD1]])
   apply (fastforce simp: valid_idle'_def pred_tcb_at'_def obj_at'_def projectKOs
                   dest!: invs_valid_idle')
  apply (fastforce dest: invs_valid_objs' ko_at_valid_objs'
                   simp: valid_obj'_def projectKOs)[1]
  done

lemma setupCallerCap_urz[wp]:
  "\<lbrace>untyped_ranges_zero' and valid_pspace' and tcb_at' sender\<rbrace>
    setupCallerCap sender t \<lbrace>\<lambda>rv. untyped_ranges_zero'\<rbrace>"
  apply (simp add: setupCallerCap_def getSlotCap_def
                   getThreadCallerSlot_def getThreadReplySlot_def
                   locateSlot_conv)
  apply (wp getCTE_wp')
  apply (rule_tac Q="\<lambda>_. untyped_ranges_zero' and valid_mdb' and valid_objs'" in hoare_post_imp)
   apply (clarsimp simp: cte_wp_at_ctes_of cteCaps_of_def untyped_derived_eq_def
                         isCap_simps)
  apply (wp sts_valid_pspace_hangers)
  apply (clarsimp simp: valid_tcb_state'_def)
  done

lemmas threadSet_urz = untyped_ranges_zero_lift[where f="cteCaps_of", OF _ threadSet_cteCaps_of]

crunch urz[wp]: doIPCTransfer "untyped_ranges_zero'"
  (ignore: threadSet wp: threadSet_urz crunch_wps simp: zipWithM_x_mapM)

crunch gsUntypedZeroRanges[wp]: receiveIPC "\<lambda>s. P (gsUntypedZeroRanges s)"
  (wp: crunch_wps transferCapsToSlots_pres1 simp: zipWithM_x_mapM ignore: constOnFailure)

crunch ctes_of[wp]: switchIfRequiredTo "\<lambda>s. P (ctes_of s)"
  (wp: crunch_wps ignore: constOnFailure)
lemmas switchIfRequiredTo_cteCaps_of[wp]
    = cteCaps_of_ctes_of_lift[OF switchIfRequiredTo_ctes_of]

(* t = ksCurThread s *)
lemma ri_invs' [wp]:
  "\<lbrace>invs' and sch_act_not t
          and ct_in_state' simple'
          and st_tcb_at' simple' t
          and (\<lambda>s. \<forall>p. t \<notin> set (ksReadyQueues s p))
          and ex_nonz_cap_to' t
          and (\<lambda>s. \<forall>r \<in> zobj_refs' cap. ex_nonz_cap_to' r s)\<rbrace>
  receiveIPC t cap isBlocking
  \<lbrace>\<lambda>_. invs'\<rbrace>" (is "\<lbrace>?pre\<rbrace> _ \<lbrace>_\<rbrace>")
  apply (clarsimp simp: receiveIPC_def) 
  apply (rule hoare_seq_ext [OF _ get_ep_sp'])
  apply (rule hoare_seq_ext [OF _ gbn_sp'])
  apply (rule hoare_seq_ext)
  (* set up precondition for old proof *)
   apply (rule_tac R="ko_at' ep (capEPPtr cap) and ?pre" in hoare_vcg_split_if)
    apply (wp completeSignal_invs)
   apply (case_tac ep)
     -- "endpoint = RecvEP"
     apply (simp add: invs'_def valid_state'_def)
     apply (rule hoare_pre, wpc, wp valid_irq_node_lift)
      apply (simp add: valid_ep'_def)
      apply (wp sts_sch_act' hoare_vcg_const_Ball_lift valid_irq_node_lift
                sts_valid_queues setThreadState_ct_not_inQ
                asUser_urz
           | simp add: doNBRecvFailedTransfer_def cteCaps_of_def)+
     apply (clarsimp simp: valid_tcb_state'_def pred_tcb_at' o_def)
     apply (rule conjI, clarsimp elim!: obj_at'_weakenE)
     apply (frule obj_at_valid_objs')
      apply (clarsimp simp: valid_pspace'_def)
     apply (drule(1) sym_refs_ko_atD')
     apply (drule simple_st_tcb_at_state_refs_ofD')
     apply (drule bound_tcb_at_state_refs_ofD')
     apply (clarsimp simp: st_tcb_at_refs_of_rev' valid_ep'_def
                           valid_obj'_def projectKOs tcb_bound_refs'_def
                    dest!: isCapDs)
     apply (rule conjI, clarsimp)
      apply (drule (1) bspec)
      apply (clarsimp dest!: st_tcb_at_state_refs_ofD')
      apply (clarsimp simp: set_eq_subset)
     apply (rule conjI, erule delta_sym_refs)
       apply (clarsimp split: if_split_asm)
        apply (rename_tac list one two three fur five six seven eight nine ten)
        apply (subgoal_tac "set list \<times> {EPRecv} \<noteq> {}")
         apply safe[1]
                apply (auto dest!: symreftype_inverse')[10]
      apply (clarsimp split: if_split_asm)
     apply (fastforce simp: valid_pspace'_def global'_no_ex_cap idle'_not_queued)
   -- "endpoint = IdleEP"
    apply (simp add: invs'_def valid_state'_def)
    apply (rule hoare_pre, wpc, wp valid_irq_node_lift)
     apply (simp add: valid_ep'_def)
     apply (wp sts_sch_act' valid_irq_node_lift
               sts_valid_queues setThreadState_ct_not_inQ
               asUser_urz
          | simp add: doNBRecvFailedTransfer_def cteCaps_of_def)+
    apply (clarsimp simp: pred_tcb_at' valid_tcb_state'_def o_def)
    apply (rule conjI, clarsimp elim!: obj_at'_weakenE)
    apply (subgoal_tac "t \<noteq> capEPPtr cap")
     apply (drule simple_st_tcb_at_state_refs_ofD')
     apply (drule ko_at_state_refs_ofD')
     apply (drule bound_tcb_at_state_refs_ofD')
     apply (clarsimp dest!: isCapDs)
     apply (rule conjI, erule delta_sym_refs)
       apply (clarsimp split: if_split_asm)
      apply (clarsimp simp: tcb_bound_refs'_def
                      dest: symreftype_inverse'
                     split: if_split_asm)
     apply (fastforce simp: global'_no_ex_cap)
    apply (clarsimp simp: obj_at'_def pred_tcb_at'_def projectKOs)
   -- "endpoint = SendEP"
   apply (simp add: invs'_def valid_state'_def)
   apply (rename_tac list)
   apply (case_tac list, simp_all split del: if_split)
   apply (rename_tac sender queue)
   apply (rule hoare_pre)
    apply (wp valid_irq_node_lift hoare_drop_imps setEndpoint_valid_mdb'
              set_ep_valid_objs' sts_st_tcb' sts_sch_act' sts_valid_queues
              setThreadState_ct_not_inQ switchIfRequiredTo_valid_queues
              switchIfRequiredTo_valid_queues'
              switchIfRequiredTo_ct_not_inQ hoare_vcg_all_lift
              setEndpoint_ksQ setEndpoint_ct'
         | simp add: valid_tcb_state'_def case_bool_If
                     case_option_If
              split del: if_split cong: if_cong
        | wp_once sch_act_sane_lift hoare_vcg_conj_lift hoare_vcg_all_lift
                  untyped_ranges_zero_lift)+
   apply (clarsimp split del: if_split simp: pred_tcb_at')
   apply (frule obj_at_valid_objs')
    apply (clarsimp simp: valid_pspace'_def)
   apply (frule(1) ct_not_in_epQueue, clarsimp, clarsimp)
   apply (drule(1) sym_refs_ko_atD')
   apply (drule simple_st_tcb_at_state_refs_ofD')
   apply (clarsimp simp: projectKOs valid_obj'_def valid_ep'_def
                         st_tcb_at_refs_of_rev' conj_ac
              split del: if_split
                   cong: if_cong)
   apply (frule_tac t=sender in valid_queues_not_runnable'_not_ksQ)
    apply (erule pred_tcb'_weakenE, clarsimp)
   apply (subgoal_tac "sch_act_not sender s")
    prefer 2
    apply (clarsimp simp: pred_tcb_at'_def obj_at'_def)
   apply (drule st_tcb_at_state_refs_ofD')
   apply (simp only: conj_ac(1, 2)[where Q="sym_refs R" for R])
   apply (subgoal_tac "distinct (ksIdleThread s # capEPPtr cap # t # sender # queue)")
    apply (rule conjI)
     apply (clarsimp simp: ep_redux_simps' cong: if_cong)
     apply (erule delta_sym_refs)
      apply (clarsimp split: if_split_asm)
     apply (fastforce simp: tcb_bound_refs'_def
                      dest: symreftype_inverse'
                     split: if_split_asm)
    apply (clarsimp simp: singleton_tuple_cartesian split: list.split
            | rule conjI | drule(1) bspec
            | drule st_tcb_at_state_refs_ofD' bound_tcb_at_state_refs_ofD'
            | clarsimp elim!: if_live_state_refsE)+
    apply (case_tac cap, simp_all add: isEndpointCap_def)
    apply (clarsimp simp: global'_no_ex_cap)
   apply (rule conjI
           | clarsimp simp: singleton_tuple_cartesian split: list.split
           | clarsimp elim!: if_live_state_refsE
           | clarsimp simp: global'_no_ex_cap idle'_not_queued' idle'_no_refs tcb_bound_refs'_def
           | drule(1) bspec | drule st_tcb_at_state_refs_ofD'
           | clarsimp simp: set_eq_subset dest!: bound_tcb_at_state_refs_ofD' )+
  apply (rule hoare_pre)
   apply (wp getNotification_wp | wpc | clarsimp)+
  done

(* t = ksCurThread s *)
lemma rai_invs'[wp]:
  "\<lbrace>invs' and sch_act_not t
          and st_tcb_at' simple' t
          and (\<lambda>s. \<forall>p. t \<notin> set (ksReadyQueues s p))
          and ex_nonz_cap_to' t
          and (\<lambda>s. \<forall>r \<in> zobj_refs' cap. ex_nonz_cap_to' r s)
          and (\<lambda>s. \<exists>ntfnptr. isNotificationCap cap
                 \<and> capNtfnPtr cap = ntfnptr
                 \<and> obj_at' (\<lambda>ko. ntfnBoundTCB ko = None \<or> ntfnBoundTCB ko = Some t)
                           ntfnptr s)\<rbrace>
    receiveSignal t cap isBlocking
   \<lbrace>\<lambda>_. invs'\<rbrace>"
  apply (simp add: receiveSignal_def)
  apply (rule hoare_seq_ext [OF _ get_ntfn_sp'])
  apply (rename_tac ep)
  apply (case_tac "ntfnObj ep")
    -- "ep = IdleNtfn"
    apply (simp add: invs'_def valid_state'_def)
    apply (rule hoare_pre)
     apply (wp valid_irq_node_lift sts_sch_act' typ_at_lifts
               sts_valid_queues setThreadState_ct_not_inQ
               asUser_urz
            | simp add: valid_ntfn'_def doNBRecvFailedTransfer_def | wpc)+
    apply (clarsimp simp: pred_tcb_at' valid_tcb_state'_def)
    apply (rule conjI, clarsimp elim!: obj_at'_weakenE)
    apply (subgoal_tac "capNtfnPtr cap \<noteq> t")
     apply (frule valid_pspace_valid_objs')
     apply (frule (1) ko_at_valid_objs')
      apply (clarsimp simp: projectKOs)
     apply (clarsimp simp: valid_obj'_def valid_ntfn'_def)
     apply (rule conjI, clarsimp simp: obj_at'_def split: option.split)
     apply (drule simple_st_tcb_at_state_refs_ofD'
                  ko_at_state_refs_ofD' bound_tcb_at_state_refs_ofD')+
     apply (clarsimp dest!: isCapDs)
     apply (rule conjI, erule delta_sym_refs)
       apply (clarsimp split: if_split_asm)
      apply (fastforce simp: tcb_bound_refs'_def symreftype_inverse'
                      split: if_split_asm)
     apply (clarsimp dest!: global'_no_ex_cap)
    apply (clarsimp simp: pred_tcb_at'_def obj_at'_def projectKOs)
   -- "ep = ActiveNtfn"
   apply (simp add: invs'_def valid_state'_def)
   apply (rule hoare_pre)
    apply (wp valid_irq_node_lift sts_valid_objs' typ_at_lifts static_imp_wp
              asUser_urz
         | simp add: valid_ntfn'_def)+
   apply (clarsimp simp: pred_tcb_at' valid_pspace'_def)
   apply (frule (1) ko_at_valid_objs')
    apply (clarsimp simp: projectKOs)
   apply (clarsimp simp: valid_obj'_def valid_ntfn'_def isCap_simps)
   apply (drule simple_st_tcb_at_state_refs_ofD'
                 ko_at_state_refs_ofD')+
   apply (erule delta_sym_refs)
    apply (clarsimp split: if_split_asm simp: global'_no_ex_cap)+
  -- "ep = WaitingNtfn"
  apply (simp add: invs'_def valid_state'_def)
  apply (rule hoare_pre)
   apply (wp hoare_vcg_const_Ball_lift valid_irq_node_lift sts_sch_act'
             sts_valid_queues setThreadState_ct_not_inQ typ_at_lifts
             asUser_urz
        | simp add: valid_ntfn'_def doNBRecvFailedTransfer_def | wpc)+
  apply (clarsimp simp: valid_tcb_state'_def)
  apply (frule_tac t=t in not_in_ntfnQueue)
     apply (simp)
    apply (simp)
   apply (erule pred_tcb'_weakenE, clarsimp)
  apply (frule ko_at_valid_objs')
    apply (clarsimp simp: valid_pspace'_def)
   apply (simp add: projectKOs)
  apply (clarsimp simp: valid_obj'_def)
  apply (clarsimp simp: valid_ntfn'_def pred_tcb_at')
  apply (rule conjI, clarsimp elim!: obj_at'_weakenE)
  apply (rule conjI, clarsimp simp: obj_at'_def split: option.split)
  apply (drule(1) sym_refs_ko_atD')
  apply (drule simple_st_tcb_at_state_refs_ofD')
  apply (drule bound_tcb_at_state_refs_ofD')
  apply (clarsimp simp: st_tcb_at_refs_of_rev'
                 dest!: isCapDs)
  apply (rule conjI, erule delta_sym_refs)
    apply (clarsimp split: if_split_asm)
    apply (rename_tac list one two three four five six seven eight nine)
    apply (subgoal_tac "set list \<times> {NTFNSignal} \<noteq> {}")
     apply safe[1]
        apply (auto simp: symreftype_inverse' ntfn_bound_refs'_def tcb_bound_refs'_def)[5]
   apply (fastforce simp: tcb_bound_refs'_def
                   split: if_split_asm)
  apply (clarsimp dest!: global'_no_ex_cap)
  done

lemma zobj_refs_maskCapRights[simp]:
  "zobj_refs' (maskCapRights msk cap) = zobj_refs' cap"
  by (cases cap;
      clarsimp
          simp add: maskCapRights_def isCap_simps
                    Let_def ARM_H.maskCapRights_def
             split: arch_capability.split)

lemma getCTE_cap_to_refs[wp]:
  "\<lbrace>\<top>\<rbrace> getCTE p \<lbrace>\<lambda>rv s. \<forall>r\<in>zobj_refs' (cteCap rv). ex_nonz_cap_to' r s\<rbrace>"
  apply (rule hoare_strengthen_post [OF getCTE_sp])
  apply (clarsimp simp: ex_nonz_cap_to'_def)
  apply (fastforce elim: cte_wp_at_weakenE')
  done

lemma lookupCap_cap_to_refs[wp]:
  "\<lbrace>\<top>\<rbrace> lookupCap t cref \<lbrace>\<lambda>rv s. \<forall>r\<in>zobj_refs' rv. ex_nonz_cap_to' r s\<rbrace>,-"
  apply (simp add: lookupCap_def lookupCapAndSlot_def split_def
                   getSlotCap_def)
  apply (wp | simp)+
  done

lemma arch_stt_objs' [wp]:
  "\<lbrace>valid_objs'\<rbrace> Arch.switchToThread t \<lbrace>\<lambda>rv. valid_objs'\<rbrace>"
  apply (simp add: ARM_H.switchToThread_def)
  apply wp
  done

(* FIXME: arch_split: is there a better way to refer to the Thread_H.switchToThread_def? *)
lemma stt_objs' [wp]:
  "\<lbrace>valid_objs'\<rbrace> switchToThread t \<lbrace>\<lambda>rv. valid_objs'\<rbrace>"
  apply (simp add: Thread_H.switchToThread_def setCurThread_def)
  apply (wp threadSet_valid_objs' | simp)+
  done

declare zipWithM_x_mapM [simp]

lemma cteInsert_invs_bits[wp]:
  "\<lbrace>\<lambda>s. sch_act_wf (ksSchedulerAction s) s\<rbrace>
      cteInsert a b c
   \<lbrace>\<lambda>rv s. sch_act_wf (ksSchedulerAction s) s\<rbrace>"
  "\<lbrace>Invariants_H.valid_queues\<rbrace> cteInsert a b c \<lbrace>\<lambda>rv. Invariants_H.valid_queues\<rbrace>"
  "\<lbrace>cur_tcb'\<rbrace> cteInsert a b c \<lbrace>\<lambda>rv. cur_tcb'\<rbrace>"
  "\<lbrace>\<lambda>s. P (state_refs_of' s)\<rbrace>
      cteInsert a b c
   \<lbrace>\<lambda>rv s. P (state_refs_of' s)\<rbrace>"
apply (wp sch_act_wf_lift valid_queues_lift
          cur_tcb_lift tcb_in_cur_domain'_lift)+
done

crunch cap_to'[wp]: attemptSwitchTo "ex_nonz_cap_to' p"
  (wp: crunch_wps)
crunch objs'[wp]: attemptSwitchTo valid_objs'
  (wp: crunch_wps)
crunch ct[wp]: attemptSwitchTo cur_tcb'
  (wp: cur_tcb_lift crunch_wps)

lemma setupCallerCap_cap_to' [wp]:
  "\<lbrace>ex_nonz_cap_to' p\<rbrace> setupCallerCap a b \<lbrace>\<lambda>rv. ex_nonz_cap_to' p\<rbrace>"
  apply (simp add: setupCallerCap_def getThreadCallerSlot_def getThreadReplySlot_def)
  apply (wp cteInsert_cap_to')
       apply (rule_tac Q="\<lambda>rv. ex_nonz_cap_to' p
                           and cte_wp_at' (\<lambda>c. (cteCap c) = rv) callerSlot"
                    in hoare_post_imp)
        apply (clarsimp simp: cte_wp_at_ctes_of)
       apply (wp getSlotCap_cte_wp_at hoare_drop_imps)+
  apply simp
  done

lemma setupCaller_pred_tcb_recv':
  "\<lbrace>pred_tcb_at' proj P r and K (s \<noteq> r)\<rbrace> setupCallerCap s r \<lbrace>\<lambda>_. pred_tcb_at' proj P r\<rbrace>"
  apply (simp add: setupCallerCap_def getThreadCallerSlot_def getSlotCap_def
                   getThreadReplySlot_def locateSlot_conv) 
  apply (wp getCTE_wp' hoare_drop_imps hoare_vcg_all_lift sts_pred_tcb_neq')
  apply clarsimp
  done

lemma possibleSwitchTo_sch_act_not:
  "\<lbrace>sch_act_not t' and K (t \<noteq> t')\<rbrace> possibleSwitchTo t b \<lbrace>\<lambda>rv. sch_act_not t'\<rbrace>"
  apply (simp add: possibleSwitchTo_def setSchedulerAction_def curDomain_def)
  apply (wp hoare_drop_imps | wpc | simp)+
  done

lemmas attemptSwitchTo_sch_act_not
    = possibleSwitchTo_sch_act_not[where b=True, folded attemptSwitchTo_def]

crunch vms'[wp]: attemptSwitchTo valid_machine_state'
crunch pspace_domain_valid[wp]: attemptSwitchTo pspace_domain_valid
crunch ct_idle_or_in_cur_domain'[wp]: attemptSwitchTo ct_idle_or_in_cur_domain'

crunch ct'[wp]: attemptSwitchTo "\<lambda>s. P (ksCurThread s)"
crunch it[wp]: attemptSwitchTo "\<lambda>s. P (ksIdleThread s)"
crunch irqs_masked'[wp]: attemptSwitchTo "irqs_masked'"
crunch urz[wp]: attemptSwitchTo "untyped_ranges_zero'"
  (simp: crunch_simps unless_def wp: crunch_wps)

lemma si_invs'[wp]: 
  "\<lbrace>invs' and st_tcb_at' simple' t
          and (\<lambda>s. \<forall>p. t \<notin> set (ksReadyQueues s p))
          and sch_act_not t
          and ex_nonz_cap_to' ep and ex_nonz_cap_to' t\<rbrace>
  sendIPC bl call ba cg t ep
  \<lbrace>\<lambda>rv. invs'\<rbrace>"
  apply (simp add: sendIPC_def split del: if_split)
  apply (rule hoare_seq_ext [OF _ get_ep_sp'])
  apply (case_tac epa)
    -- "epa = RecvEP"
    apply simp
    apply (rename_tac list)
    apply (case_tac list)
     apply simp
    apply (simp split del: if_split add: invs'_def valid_state'_def)
    apply (rule hoare_pre)
     apply (rule_tac P="a\<noteq>t" in hoare_gen_asm)
     apply (wp valid_irq_node_lift setupCaller_pred_tcb_recv'
               sts_valid_objs' set_ep_valid_objs' setEndpoint_valid_mdb' sts_st_tcb' sts_sch_act'
               attemptSwitchTo_sch_act_not sts_valid_queues setThreadState_ct_not_inQ
               attemptSwitchTo_ksQ attemptSwitchTo_ct_not_inQ hoare_vcg_all_lift sts_ksQ'
               hoare_convert_imp [OF doIPCTransfer_nosch doIPCTransfer_ct']
               hoare_convert_imp [OF getThreadState_nosch getThreadState_ct']
               hoare_convert_imp [OF setEndpoint_nosch setEndpoint_ct']
               hoare_drop_imp [where f="threadGet tcbFault t"]
             | rule_tac f="getThreadState a" in hoare_drop_imp
             | simp    add: valid_tcb_state'_def case_bool_If
                            case_option_If
                      cong: if_cong
                 split del: if_split
             | wp_once sch_act_sane_lift tcb_in_cur_domain'_lift)+
    apply (clarsimp simp: pred_tcb_at'
               split del: if_split)
    apply (frule obj_at_valid_objs', clarsimp)
    apply (frule(1) sym_refs_ko_atD')
    apply (clarsimp simp: projectKOs valid_obj'_def valid_ep'_def
                          st_tcb_at_refs_of_rev' pred_tcb_at'
                          conj_comms fun_upd_def[symmetric]
               split del: if_split)
    apply (frule pred_tcb_at')
    apply (drule simple_st_tcb_at_state_refs_ofD' st_tcb_at_state_refs_ofD')+
    apply (subst fun_upd_idem[where x=t])
     apply clarsimp
     apply (rule conjI, clarsimp simp: obj_at'_def projectKOs)
     apply (drule bound_tcb_at_state_refs_ofD')
     apply (fastforce simp: tcb_bound_refs'_def)
    apply (clarsimp split del: if_split)
    apply (rule conjI, clarsimp)+
    apply (rule conjI)
     apply (clarsimp elim!: if_live_state_refsE)
    apply (rule conjI)
     apply (drule bound_tcb_at_state_refs_ofD')
     apply (fastforce simp: tcb_bound_refs'_def set_eq_subset)
    apply (rule conjI, clarsimp simp: idle'_no_refs)
    apply (rule conjI, clarsimp simp: global'_no_ex_cap)
    apply (rule conjI)
     apply (rule impI)
     apply (frule(1) ct_not_in_epQueue, clarsimp, clarsimp)
     apply (clarsimp)
    apply (simp add: ep_redux_simps')
    apply (rule conjI, fastforce simp: tcb_bound_refs'_def set_eq_subset)
    apply (clarsimp, rule conjI, erule delta_sym_refs)
      apply (auto simp: symreftype_inverse' tcb_bound_refs'_def split: if_split_asm)[2]
    apply (rule conjI, clarsimp split: list.splits)
    apply (erule delta_sym_refs)
     apply (auto simp: symreftype_inverse' tcb_bound_refs'_def split: if_split_asm)[2]
   -- "epa = IdleEP"
   apply (cases bl)
    apply (simp add: invs'_def valid_state'_def)
    apply (rule hoare_pre, wp valid_irq_node_lift)
     apply (simp add: valid_ep'_def)
     apply (wp valid_irq_node_lift sts_sch_act' sts_valid_queues
               setThreadState_ct_not_inQ)
    apply (clarsimp simp: valid_tcb_state'_def pred_tcb_at')
    apply (rule conjI, clarsimp elim!: obj_at'_weakenE)
    apply (subgoal_tac "ep \<noteq> t")
     apply (drule simple_st_tcb_at_state_refs_ofD' ko_at_state_refs_ofD'
                  bound_tcb_at_state_refs_ofD')+
     apply (rule conjI, erule delta_sym_refs)
       apply (auto simp: tcb_bound_refs'_def symreftype_inverse'
                  split: if_split_asm)[2]
     apply (fastforce simp: global'_no_ex_cap)
    apply (clarsimp simp: pred_tcb_at'_def obj_at'_def projectKOs)
   apply simp
   apply wp
   apply simp
  -- "epa = SendEP"
  apply (cases bl)
   apply (simp add: invs'_def valid_state'_def)
   apply (rule hoare_pre, wp valid_irq_node_lift)
    apply (simp add: valid_ep'_def)
    apply (wp hoare_vcg_const_Ball_lift valid_irq_node_lift sts_sch_act'
              sts_valid_queues setThreadState_ct_not_inQ)
   apply (clarsimp simp: valid_tcb_state'_def pred_tcb_at')
   apply (rule conjI, clarsimp elim!: obj_at'_weakenE)
   apply (frule obj_at_valid_objs', clarsimp)
   apply (frule(1) sym_refs_ko_atD')
   apply (frule pred_tcb_at')
   apply (drule simple_st_tcb_at_state_refs_ofD')
   apply (drule bound_tcb_at_state_refs_ofD')
   apply (clarsimp simp: valid_obj'_def valid_ep'_def
                         projectKOs st_tcb_at_refs_of_rev')
   apply (rule conjI, clarsimp)
    apply (drule (1) bspec)
    apply (clarsimp dest!: st_tcb_at_state_refs_ofD' bound_tcb_at_state_refs_ofD'
                     simp: tcb_bound_refs'_def)
    apply (clarsimp simp: set_eq_subset)
   apply (rule conjI, erule delta_sym_refs)
     subgoal by (fastforce simp: obj_at'_def projectKOs symreftype_inverse'
                     split: if_split_asm)
    apply (fastforce simp: tcb_bound_refs'_def symreftype_inverse'
                    split: if_split_asm)
   apply (fastforce simp: global'_no_ex_cap idle'_not_queued)
  apply (simp | wp)+
  done

lemma sfi_invs_plus':
  "\<lbrace>invs' and st_tcb_at' simple' t
          and sch_act_not t
          and (\<lambda>s. \<forall>p. t \<notin> set (ksReadyQueues s p))
          and ex_nonz_cap_to' t\<rbrace>
      sendFaultIPC t f
   \<lbrace>\<lambda>rv. invs'\<rbrace>, \<lbrace>\<lambda>rv. invs' and st_tcb_at' simple' t
                      and (\<lambda>s. \<forall>p. t \<notin> set (ksReadyQueues s p))
                      and sch_act_not t and (\<lambda>s. ksIdleThread s \<noteq> t)\<rbrace>"
  apply (simp add: sendFaultIPC_def)
  apply (wp threadSet_invs_trivial threadSet_pred_tcb_no_state
            threadSet_cap_to'
           | wpc | simp)+
   apply (rule_tac Q'="\<lambda>rv s. invs' s \<and> sch_act_not t s 
                             \<and> st_tcb_at' simple' t s
                             \<and> (\<forall>p. t \<notin> set (ksReadyQueues s p))
                             \<and> ex_nonz_cap_to' t s
                             \<and> t \<noteq> ksIdleThread s
                             \<and> (\<forall>r\<in>zobj_refs' rv. ex_nonz_cap_to' r s)"
                 in hoare_post_imp_R)
    apply wp
   apply (clarsimp simp: inQ_def pred_tcb_at')
  apply (wp | simp)+
  apply (clarsimp simp: eq_commute)
  apply (subst(asm) global'_no_ex_cap, auto)
  done

lemma hf_corres:
  "fr f f' \<Longrightarrow>
   corres dc (einvs and  st_tcb_at active thread and ex_nonz_cap_to thread
                   and (%_. valid_fault f))
             (invs' and sch_act_not thread
                    and (\<lambda>s. \<forall>p. thread \<notin> set(ksReadyQueues s p))
                    and st_tcb_at' simple' thread and ex_nonz_cap_to' thread)
             (handle_fault thread f) (handleFault thread f')"
  apply (simp add: handle_fault_def handleFault_def)
  apply (rule corres_guard_imp)
    apply (subst return_bind [symmetric], 
               rule corres_split [where P="tcb_at thread", 
                                  OF _ gets_the_noop_corres [where x="()"]])
       apply (rule corres_split_catch)
          apply (rule hdf_corres)
          apply (rule_tac F="valid_fault f" in corres_gen_asm)
         apply (rule send_fault_ipc_corres, assumption)
         apply simp
        apply wp+
       apply (rule hoare_post_impErr, rule sfi_invs_plus', simp_all)[1]
       apply clarsimp
      apply (simp add: tcb_at_def)
     apply wp+
   apply (clarsimp simp: st_tcb_at_tcb_at st_tcb_def2 invs_def
                         valid_state_def valid_idle_def)
  apply auto
  done

lemma sts_invs_minor'':
  "\<lbrace>st_tcb_at' (\<lambda>st'. tcb_st_refs_of' st' = tcb_st_refs_of' st
                   \<and> (st \<noteq> Inactive \<and> \<not> idle' st \<longrightarrow>
                      st' \<noteq> Inactive \<and> \<not> idle' st')) t
      and (\<lambda>s. t = ksIdleThread s \<longrightarrow> idle' st)
      and (\<lambda>s. (\<exists>p. t \<in> set (ksReadyQueues s p)) \<longrightarrow> runnable' st)
      and (\<lambda>s. runnable' st \<and> obj_at' tcbQueued t s
                                      \<longrightarrow> st_tcb_at' runnable' t s)
      and (\<lambda>s. \<not> runnable' st \<longrightarrow> sch_act_not t s)
      and invs'\<rbrace>
     setThreadState st t
   \<lbrace>\<lambda>rv. invs'\<rbrace>"
  apply (simp add: invs'_def valid_state'_def)
  apply (rule hoare_pre)
   apply (wp valid_irq_node_lift sts_sch_act' sts_valid_queues
             setThreadState_ct_not_inQ)
  apply clarsimp
  apply (rule conjI)
   apply fastforce
  apply (rule conjI)
   apply (clarsimp simp: pred_tcb_at'_def)
   apply (drule obj_at_valid_objs')
    apply (clarsimp simp: valid_pspace'_def)
   apply (clarsimp simp: valid_obj'_def valid_tcb'_def projectKOs)
   subgoal by (cases st, auto simp: valid_tcb_state'_def
                        split: Structures_H.thread_state.splits)[1]
  apply (rule conjI)
   apply (clarsimp dest!: st_tcb_at_state_refs_ofD'
                   elim!: rsubst[where P=sym_refs]
                  intro!: ext)
  apply (clarsimp elim!: st_tcb_ex_cap'')
  done

lemma hf_invs' [wp]: 
  "\<lbrace>invs' and sch_act_not t
          and (\<lambda>s. \<forall>p. t \<notin> set(ksReadyQueues s p))
          and st_tcb_at' simple' t
          and ex_nonz_cap_to' t and (\<lambda>s. t \<noteq> ksIdleThread s)\<rbrace>
   handleFault t f \<lbrace>\<lambda>r. invs'\<rbrace>"
  apply (simp add: handleFault_def)
  apply wp
   apply (simp add: handleDoubleFault_def)   
   apply (wp sts_invs_minor'' dmo_invs')+
  apply (rule hoare_post_impErr, rule sfi_invs_plus',
         simp_all)
  apply (strengthen no_refs_simple_strg')
  apply clarsimp
  done

declare zipWithM_x_mapM [simp del]

lemma receive_not_active [simp]:
  "(isReceive st \<and> active' st) = False"
  by (cases st, auto simp: isReceive_def)

lemma send_not_active [simp]:
  "(isSend st \<and> active' st) = False"
  by (cases st, auto simp: isSend_def)

lemma gts_st_tcb':
  "\<lbrace>\<top>\<rbrace> getThreadState t \<lbrace>\<lambda>r. st_tcb_at' (\<lambda>st. st = r) t\<rbrace>"
  apply (rule hoare_strengthen_post)
  apply (rule gts_sp')
  apply simp
  done

declare setEndpoint_ct' [wp]

lemma setupCallerCap_pred_tcb_unchanged:
  "\<lbrace>pred_tcb_at' proj P t and K (t \<noteq> t')\<rbrace>
     setupCallerCap t' t''
   \<lbrace>\<lambda>rv. pred_tcb_at' proj P t\<rbrace>"
  apply (simp add: setupCallerCap_def getThreadCallerSlot_def
                   getThreadReplySlot_def)
  apply (wp sts_pred_tcb_neq' hoare_drop_imps)
  apply clarsimp
  done

lemma si_blk_makes_simple':
  "\<lbrace>st_tcb_at' simple' t and K (t \<noteq> t')\<rbrace>
     sendIPC True call bdg x t' ep
   \<lbrace>\<lambda>rv. st_tcb_at' simple' t\<rbrace>"
  apply (simp add: sendIPC_def)
  apply (rule hoare_seq_ext [OF _ get_ep_inv'])
  apply (case_tac xa, simp_all)
    apply (rename_tac list)
    apply (case_tac list, simp_all add: case_bool_If case_option_If
                             split del: if_split cong: if_cong)
    apply (rule hoare_pre)
     apply (wp sts_st_tcb_at'_cases setupCallerCap_pred_tcb_unchanged
               hoare_drop_imps)
    apply (clarsimp simp: pred_tcb_at' del: disjCI)
   apply (wp sts_st_tcb_at'_cases)
   apply clarsimp
  apply (wp sts_st_tcb_at'_cases)
  apply clarsimp
  done

lemma si_blk_makes_runnable':
  "\<lbrace>st_tcb_at' runnable' t and K (t \<noteq> t')\<rbrace>
     sendIPC True call bdg x t' ep
   \<lbrace>\<lambda>rv. st_tcb_at' runnable' t\<rbrace>"
  apply (simp add: sendIPC_def)
  apply (rule hoare_seq_ext [OF _ get_ep_inv'])
  apply (case_tac xa, simp_all)
    apply (rename_tac list)
    apply (case_tac list, simp_all add: case_bool_If case_option_If
                             split del: if_split cong: if_cong)
    apply (rule hoare_pre)
     apply (wp sts_st_tcb_at'_cases setupCallerCap_pred_tcb_unchanged
               hoare_vcg_const_imp_lift hoare_drop_imps
              | simp)+
    apply (clarsimp del: disjCI simp: pred_tcb_at')
   apply (wp sts_st_tcb_at'_cases)
   apply clarsimp
  apply (wp sts_st_tcb_at'_cases)
  apply clarsimp
  done

lemma sfi_makes_simple':
  "\<lbrace>st_tcb_at' simple' t and K (t \<noteq> t')\<rbrace>
     sendFaultIPC t' ft
   \<lbrace>\<lambda>rv. st_tcb_at' simple' t\<rbrace>"
  apply (rule hoare_gen_asm)
  apply (simp add: sendFaultIPC_def
             cong: if_cong capability.case_cong bool.case_cong)
  apply (wp si_blk_makes_simple' threadSet_pred_tcb_no_state hoare_drop_imps
       | wpc | simp)+
  done

lemma sfi_makes_runnable':
  "\<lbrace>st_tcb_at' runnable' t and K (t \<noteq> t')\<rbrace>
     sendFaultIPC t' ft
   \<lbrace>\<lambda>rv. st_tcb_at' runnable' t\<rbrace>"
  apply (rule hoare_gen_asm)
  apply (simp add: sendFaultIPC_def
             cong: if_cong capability.case_cong bool.case_cong)
  apply (wp si_blk_makes_runnable' threadSet_pred_tcb_no_state hoare_drop_imps
       | wpc | simp)+
  done

lemma hf_makes_runnable_simple':
  "\<lbrace>st_tcb_at' P t' and K (t \<noteq> t') and K (P = runnable' \<or> P = simple')\<rbrace>
     handleFault t ft
   \<lbrace>\<lambda>rv. st_tcb_at' P t'\<rbrace>"
  apply (safe intro!: hoare_gen_asm)
  apply (simp_all add: handleFault_def handleDoubleFault_def)
   apply (wp sfi_makes_runnable' sfi_makes_simple' sts_st_tcb_at'_cases
           | simp add: handleDoubleFault_def)+
  done

crunch pred_tcb_at'[wp]: switchIfRequiredTo, completeSignal "pred_tcb_at' proj P t"

lemma ri_makes_runnable_simple':
  "\<lbrace>st_tcb_at' P t' and K (t \<noteq> t') and K (P = runnable' \<or> P = simple')\<rbrace>
     receiveIPC t cap isBlocking
   \<lbrace>\<lambda>rv. st_tcb_at' P t'\<rbrace>"
  including no_pre
  apply (rule hoare_gen_asm)+
  apply (simp add: receiveIPC_def)
  apply (case_tac cap, simp_all add: isEndpointCap_def)
  apply (rule hoare_seq_ext [OF _ get_ep_inv'])
  apply (rule hoare_seq_ext [OF _ gbn_sp'])
  apply wp
   apply (rename_tac ep q r)
   apply (case_tac ep, simp_all)
     apply (wp sts_st_tcb_at'_cases | wpc | simp add: doNBRecvFailedTransfer_def)+
   apply (rename_tac list)
   apply (case_tac list, simp_all add: case_bool_If case_option_If
                            split del: if_split cong: if_cong)
   apply (rule hoare_pre)
    apply (wp sts_st_tcb_at'_cases setupCallerCap_pred_tcb_unchanged
              hoare_vcg_const_imp_lift)+
        apply (rule_tac Q="\<lambda>_. st_tcb_at' P t' and K (a \<noteq> t')"
                     in hoare_post_imp)
         apply (clarsimp simp: pred_tcb_at'_def obj_at'_def)
       apply (wp threadGet_inv static_imp_wp)+
     apply (simp, simp only: imp_conv_disj)
     apply (wp hoare_vcg_disj_lift)+
   apply clarsimp
   apply (clarsimp simp: pred_tcb_at'_def obj_at'_def projectKOs)
   apply (fastforce simp: pred_tcb_at'_def obj_at'_def isSend_def
                  split: Structures_H.thread_state.split_asm)
  apply (rule hoare_pre)
   apply (wp | wpc | clarsimp)+
  done

lemma rai_makes_runnable_simple':
  "\<lbrace>st_tcb_at' P t' and K (t \<noteq> t') and K (P = runnable' \<or> P = simple')\<rbrace>
     receiveSignal t cap isBlocking
   \<lbrace>\<lambda>rv. st_tcb_at' P t'\<rbrace>"
  apply (rule hoare_gen_asm)
  apply (simp add: receiveSignal_def)
  apply (rule hoare_pre)
   by (wp sts_st_tcb_at'_cases getNotification_wp | wpc | simp add: doNBRecvFailedTransfer_def)+

lemma sendSignal_st_tcb'_Running:
  "\<lbrace>st_tcb_at' (\<lambda>st. st = Running \<or> P st) t\<rbrace>
     sendSignal ntfnptr bdg
   \<lbrace>\<lambda>_. st_tcb_at' (\<lambda>st. st = Running \<or> P st) t\<rbrace>"
  apply (simp add: sendSignal_def)
  apply (wp sts_st_tcb_at'_cases cancelIPC_st_tcb_at' gts_wp' getNotification_wp static_imp_wp
       | wpc | clarsimp simp: pred_tcb_at')+
  done

lemma sai_st_tcb':
  "\<lbrace>st_tcb_at' P t and K (P Running)\<rbrace>
     sendSignal ntfn bdg
   \<lbrace>\<lambda>rv. st_tcb_at' P t\<rbrace>"
  apply (rule hoare_gen_asm)
  apply (subgoal_tac "\<exists>Q. P = (\<lambda>st. st = Running \<or> Q st)")
   apply (clarsimp intro!: sendSignal_st_tcb'_Running)
  apply (fastforce intro!: exI[where x=P])
  done

end

end
