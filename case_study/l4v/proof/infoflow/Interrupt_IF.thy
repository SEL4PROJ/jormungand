(*
 * Copyright 2014, NICTA
 *
 * This software may be distributed and modified according to the terms of
 * the GNU General Public License version 2. Note that NO WARRANTY is provided.
 * See "LICENSE_GPLv2.txt" for details.
 *
 * @TAG(NICTA_GPL)
 *)

theory Interrupt_IF
imports Finalise_IF
begin

context begin interpretation Arch . (*FIXME: arch_split*)

subsection "reads respects"

(* invs comes from cap_delete_one *)
lemma invoke_irq_handler_reads_respects_f:
  "reads_respects_f aag l (silc_inv aag st and pas_refined aag and invs and pas_refined aag and irq_handler_inv_valid irq_inv and K (authorised_irq_hdl_inv aag irq_inv)) (invoke_irq_handler irq_inv)"
  apply(case_tac irq_inv)
    apply(simp)
    apply(rule equiv_valid_guard_imp)
     apply(rule reads_respects_f[OF dmo_maskInterrupt_reads_respects, where Q="\<top>" and st=st], wp)
     apply(simp)
    apply(simp)
   apply(simp)
   apply(wp reads_respects_f[OF cap_insert_reads_respects] cap_delete_one_reads_respects_f[where st=st]
         reads_respects_f[OF get_irq_slot_reads_respects, where Q="\<top>"] cap_insert_silc_inv''
         cap_delete_one_silc_inv cap_delete_one_cte_wp_at_other static_imp_wp
         hoare_vcg_ex_lift slots_holding_overlapping_caps_from_silc_inv[where aag=aag and st=st]| simp | simp add: get_irq_slot_def)+
   apply (clarsimp simp: pas_refined_def irq_map_wellformed_aux_def)
   apply ((rule conjI, assumption) | clarsimp simp: conj_comms authorised_irq_hdl_inv_def)+
   apply (drule_tac p="(a,b)" in cte_wp_at_eqD)
   apply (elim exE conjE, rename_tac cap')
   apply (drule_tac cap=cap' in silc_invD)
     apply assumption
    apply(fastforce simp: intra_label_cap_def cap_points_to_label_def interrupt_derived_ntfn_cap_identical_refs)
   apply(fastforce simp: slots_holding_overlapping_caps_def2 ctes_wp_at_def interrupt_derived_ntfn_cap_identical_refs)
  apply(clarsimp)
  apply(wp reads_respects_f[OF get_irq_slot_reads_respects, where Q="\<top>" and st=st] cap_delete_one_reads_respects_f | simp)+
  apply(auto simp: authorised_irq_hdl_inv_def)[1]
  done

lemma invoke_irq_control_reads_respects:
  "reads_respects aag l (K (authorised_irq_ctl_inv aag irq_ctl_inv)) (invoke_irq_control irq_ctl_inv)"
  apply(case_tac irq_ctl_inv)
   apply(wp cap_insert_reads_respects set_irq_state_reads_respects | simp)+
   apply(clarsimp simp: authorised_irq_ctl_inv_def)
  apply(simp)
  apply(unfold arch_invoke_irq_control_def)
  apply(wp)
  done


subsection "globals equiv"

crunch valid_ko_at_arm[wp]:  set_irq_state "valid_ko_at_arm"

lemma invoke_irq_control_globals_equiv:
  "\<lbrace>globals_equiv st and valid_ko_at_arm and valid_global_objs \<rbrace> invoke_irq_control a \<lbrace>\<lambda>_. globals_equiv st\<rbrace>"
  apply (induct a)
   apply (wp set_irq_state_valid_ko_at_arm set_irq_state_globals_equiv cap_insert_globals_equiv'' set_irq_state_valid_global_objs | simp add: arch_invoke_irq_control_def)+
done

crunch valid_ko_at_arm[wp]: cap_delete_one "valid_ko_at_arm" (simp: unless_def)
crunch valid_global_objs[wp]: cap_delete_one "valid_global_objs" (wp: dxo_wp_weak simp: unless_def ignore: empty_slot_ext)

lemma invoke_irq_handler_globals_equiv:
  "\<lbrace>globals_equiv st and valid_ko_at_arm  and valid_global_objs \<rbrace>
    invoke_irq_handler a
   \<lbrace>\<lambda>_. globals_equiv st\<rbrace>"
  apply (induct a)
    by (wp dmo_no_mem_globals_equiv modify_wp cap_insert_globals_equiv'' 
           cap_delete_one_globals_equiv cap_delete_one_valid_ko_at_arm 
           cap_delete_one_valid_global_objs 
            | simp add: maskInterrupt_def)+

subsection "reads_respects_g"


lemma invoke_irq_handler_reads_respects_f_g:
  "reads_respects_f_g aag l (silc_inv aag st and invs and pas_refined aag and irq_handler_inv_valid irq_inv and K (authorised_irq_hdl_inv aag irq_inv)) (invoke_irq_handler irq_inv)"
  apply(rule equiv_valid_guard_imp[OF reads_respects_f_g])
   apply(rule invoke_irq_handler_reads_respects_f)
  apply(rule doesnt_touch_globalsI)
   apply(wp invoke_irq_handler_globals_equiv | simp)+
  apply(simp add: invs_valid_ko_at_arm invs_valid_global_objs)
  by auto

lemma invoke_irq_control_reads_respects_g:
  "reads_respects_g aag l (valid_global_objs and valid_ko_at_arm and K (authorised_irq_ctl_inv aag irq_ctl_inv)) (invoke_irq_control irq_ctl_inv)"
  apply(rule equiv_valid_guard_imp[OF reads_respects_g])
   apply(rule invoke_irq_control_reads_respects)
  apply(rule doesnt_touch_globalsI)
   apply(wp invoke_irq_control_globals_equiv | simp)+
  done

end

end
