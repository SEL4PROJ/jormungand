(*
 * Copyright 2014, NICTA
 *
 * This software may be distributed and modified according to the terms of
 * the GNU General Public License version 2. Note that NO WARRANTY is provided.
 * See "LICENSE_GPLv2.txt" for details.
 *
 * @TAG(NICTA_GPL)
 *)

theory Schedule_DR
imports Finalise_DR
begin

context begin interpretation Arch . (*FIXME: arch_split*)

(* getActiveTCBs returns a subset of CapDL's all_active_tcbs. *)
lemma getActiveTCBs_subset:
  "\<lbrakk> getActiveTCB x s' = Some y; invs s'; valid_etcbs s' \<rbrakk> \<Longrightarrow>
   x \<in> all_active_tcbs (transform s')"
  apply (clarsimp simp: all_active_tcbs_def getActiveTCB_def)
  apply (clarsimp simp: transform_def transform_objects_def map_add_def domIff)
  apply (clarsimp dest!: get_tcb_SomeD split: option.splits if_split_asm)
  apply (rule context_conjI)
   apply (clarsimp simp: restrict_map_def)
   apply (frule invs_valid_idle)
   apply (clarsimp simp: valid_idle_def pred_tcb_def2 get_tcb_def)
  apply (clarsimp simp: restrict_map_def split: if_split_asm)
  apply (clarsimp simp: transform_object_def transform_tcb_def)
  apply (clarsimp simp: infer_tcb_pending_op_def)
  apply (frule(1) valid_etcbs_tcb_etcb)
  apply (case_tac "tcb_state y", auto simp: tcb_pending_op_slot_def tcb_boundntfn_slot_def)
  done


(* allActiveTCBs should be a subset of those allowed in CapDL. *)
definition
  allActiveTCBs_relation :: "cdl_object_id set \<Rightarrow> word32 set \<Rightarrow> bool"
where
  "allActiveTCBs_relation a b \<equiv> b \<subseteq> a"

(* allActiveTCBs correspond *)
lemma allActiveTCBs_corres:
  "dcorres allActiveTCBs_relation \<top> (invs and valid_etcbs) (gets all_active_tcbs) allActiveTCBs"
  apply (clarsimp simp: allActiveTCBs_def gets_def)
  apply (clarsimp simp: corres_underlying_def)
  apply (clarsimp simp: exec_get split_def return_def)
  apply (clarsimp simp: allActiveTCBs_relation_def)
  apply (auto simp: getActiveTCBs_subset)
  done

crunch idle_thread[wp]: switch_to_idle_thread "\<lambda>s. P (idle_thread s)"

lemma dcorres_arch_switch_to_idle_thread_return: "dcorres dc \<top> (invs and valid_etcbs) (return ()) arch_switch_to_idle_thread"
  by (clarsimp simp: arch_switch_to_idle_thread_def)

lemma change_current_domain_same: "\<lbrace>op = s\<rbrace> change_current_domain \<exists>\<lbrace>\<lambda>r. op = s\<rbrace>"
  apply (clarsimp simp: change_current_domain_def exs_valid_def bind_def return_def gets_def modify_def put_def fst_def snd_def get_def select_def)
  apply (rule_tac x="cdl_current_domain s" in exI)
  apply clarsimp
  done

lemma switch_to_idle_thread_dcorres:
  "dcorres dc \<top> (invs and valid_etcbs) (Schedule_D.switch_to_thread None) switch_to_idle_thread"
   apply (clarsimp simp: Schedule_D.switch_to_thread_def switch_to_idle_thread_def)
   apply (rule dcorres_symb_exec_r)
   apply (rule corres_guard_imp)
   apply (rule corres_split_noop_rhs)
         apply (clarsimp simp: corres_underlying_def gets_def modify_def get_def put_def do_machine_op_def select_f_def split_def bind_def in_return)
         apply (clarsimp simp: transform_def transform_current_thread_def transform_asid_table_def)
         apply assumption
        apply (rule dcorres_arch_switch_to_idle_thread_return)
      apply (wp | simp)+
  done


(* Switching to the idle thread and switching to "None" are equivalent. *)
lemma change_current_domain_and_switch_to_idle_thread_dcorres:
  "dcorres dc \<top> (invs and valid_etcbs)
                (do _ \<leftarrow> change_current_domain;
                    Schedule_D.switch_to_thread None
                 od)
                switch_to_idle_thread"
  including no_pre
  apply (clarsimp simp: Schedule_D.switch_to_thread_def switch_to_idle_thread_def)
  apply (rule dcorres_symb_exec_r)
  apply (rule corres_guard_imp)
  apply (rule corres_symb_exec_l)
  apply (rule_tac R=\<top> in corres_split_noop_rhs)
        apply (clarsimp simp: corres_underlying_def gets_def modify_def get_def put_def do_machine_op_def select_f_def split_def bind_def in_return)
        apply (clarsimp simp: transform_def transform_current_thread_def transform_asid_table_def)
        apply assumption
       apply (rule dcorres_arch_switch_to_idle_thread_return)
      apply (wp change_current_domain_same | simp)+
  done

lemma arch_switch_to_thread_dcorres:
  "dcorres dc \<top> (invs and (\<lambda>s. idle_thread s \<noteq> t) and valid_etcbs)
     (return ())
     (arch_switch_to_thread t)"
  apply (clarsimp simp: arch_switch_to_thread_def)
  apply (rule corres_dummy_return_pl)
  apply (rule corres_guard_imp)
    apply (rule corres_split [OF _ dcorres_set_vm_root])
      apply simp
      apply (rule dcorres_machine_op_noop)
      apply (simp add: ARM.clearExMonitor_def, wp)[1]
      apply (wp|simp)+
  done

crunch idle_thread [wp]: arch_switch_to_thread "\<lambda>s. P (idle_thread s)"
  (simp: crunch_simps wp: crunch_wps ignore: ARM.clearExMonitor)

(*
 * Setting the current thread.
 *)
lemma switch_to_thread_corres:
  "dcorres dc \<top> (invs and (\<lambda>s. idle_thread s \<noteq> x) and valid_etcbs)
           (Schedule_D.switch_to_thread (Some x)) (Schedule_A.switch_to_thread x)"
  apply (clarsimp simp: Schedule_D.switch_to_thread_def Schedule_A.switch_to_thread_def)
  apply (rule corres_dummy_return_pl)
  apply (rule corres_symb_exec_r)
     apply (rule corres_symb_exec_r)
        apply (rule corres_guard_imp)
          apply (rule corres_split [OF _ arch_switch_to_thread_dcorres])
            apply simp
            apply (rule dcorres_rhs_noop_above[OF tcb_sched_action_dcorres])
              apply (rule corres_modify [where P=\<top> and P'="\<lambda>s. idle_thread s \<noteq> x"])
              apply (clarsimp simp: transform_def)
              apply (simp add: transform_current_thread_def transform_asid_table_def)
             apply (wp+)[4]
         apply simp
        apply assumption
       apply (clarsimp|wp)+
  done

lemma corrupt_intents_current_thread:
  "cdl_current_thread (corrupt_intents x p s) = cdl_current_thread s"
  by (simp add: corrupt_intents_def)

crunch cdl_cur: corrupt_frame "\<lambda>s. cdl_current_thread s = x"
  (wp: select_wp simp: corrupt_intents_current_thread)

(* Switching to the active thread has no effect. *)
lemma switch_to_thread_idempotent_corres:
  "dcorres dc (\<lambda>s. cdl_current_thread s = x) \<top> (Schedule_D.switch_to_thread x) (return ())"
  apply (clarsimp simp: Schedule_D.switch_to_thread_def)
  apply (clarsimp simp: modify_def)
  apply (clarsimp simp: corres_underlying_def)
  apply (clarsimp simp: transform_def transform_current_thread_def)
  apply (clarsimp simp: in_return)
  apply (auto simp: in_return get_def put_def split_def bind_def)[1]
  done

(* getActiveTCB on the idle thread always returns None. *)
lemma getActiveTCB_idle: "invs s \<Longrightarrow> getActiveTCB (idle_thread s) s = None"
  apply (frule invs_valid_idle)
  apply (clarsimp simp: valid_idle_def getActiveTCB_def)
  apply (clarsimp simp: pred_tcb_at_def get_tcb_def get_obj_def obj_at_def)
  done

lemma switch_to_thread_same_corres:
  "dcorres dc (\<lambda>s. x = y) (invs and (\<lambda>s. idle_thread s \<noteq> x) and valid_etcbs)
           (Schedule_D.switch_to_thread (Some y)) (Schedule_A.switch_to_thread x)"
  apply (clarsimp simp: Schedule_D.switch_to_thread_def
                        Schedule_A.switch_to_thread_def)
  apply (rule corres_dummy_return_pl)
  apply (rule corres_symb_exec_r)
     apply (rule corres_symb_exec_r)
        apply (rule corres_guard_imp)
          apply (rule corres_split [OF _ arch_switch_to_thread_dcorres])
            apply simp
            apply (rule dcorres_rhs_noop_above[OF tcb_sched_action_dcorres])
              apply (rule corres_modify [where P'="\<lambda>s. idle_thread s \<noteq> x"])
              apply (clarsimp simp: transform_def transform_current_thread_def transform_asid_table_def)
              apply (simp add: transform_current_thread_def transform_asid_table_def)
             apply (wp+)[4]
         apply simp
        apply assumption
       apply (clarsimp|wp)+
  done

lemma set_scheduler_action_dcorres:
   "dcorres dc \<top> \<top> (return ()) (set_scheduler_action sa)"
  by (clarsimp simp: corres_underlying_def set_scheduler_action_def modify_def get_def put_def bind_def return_def)

lemma switch_to_thread_None_dcorres_L:
   "dcorres dc (\<lambda>s. cdl_current_thread s = None) \<top>
               (do _ \<leftarrow> change_current_domain;
                   Schedule_D.switch_to_thread None
                od)
               (return ())"
  apply (auto simp: Schedule_D.switch_to_thread_def modify_def corres_underlying_def get_def put_def bind_def return_def
                    change_current_domain_def gets_def select_def transform_def)
  done


lemma switch_to_thread_None_dcorres:
  "dcorres dc \<top> (\<lambda>s. cur_thread s = idle_thread s)
                (do _ \<leftarrow> change_current_domain;
                    Schedule_D.switch_to_thread None
                 od)
               (return ())"
  apply (rule_tac Q="\<lambda>s. cdl_current_thread s = None" and Q'="\<top>" in stronger_corres_guard_imp)
    apply (rule switch_to_thread_None_dcorres_L)
   apply (clarsimp simp: transform_def transform_current_thread_def)+
  done

lemma schedule_resume_cur_thread_dcorres_L:
    "\<And>cur cur_ts. dcorres dc ((\<lambda>s. \<exists>t tcb. cdl_current_thread s = Some t \<and>
                                           (\<exists>d. s = s \<lparr>cdl_current_domain := d\<rparr>) \<and>
                                           t \<in> active_tcbs_in_domain (cdl_current_domain s) s)
                                   or (\<lambda>s. cdl_current_thread s = None)) \<top>
        Schedule_D.schedule
       (do idle_t \<leftarrow> gets idle_thread;
           assert (runnable cur_ts \<or> cur = idle_t)
         od)"
  unfolding Schedule_D.schedule_def
  apply (rule corres_either_alternate2)
   apply (rule corres_guard_imp)
     apply (rule corres_symb_exec_l_Ex)
     apply (clarsimp)
     apply (rule corres_symb_exec_l_Ex)
     apply (rule corres_symb_exec_l_Ex)
     apply (rule corres_symb_exec_l_Ex)
     apply (rule dcorres_symb_exec_r)
       apply (clarsimp simp: assert_def)
       apply (rule conjI, clarsimp)
        apply (fold dc_def)
        apply (rule switch_to_thread_idempotent_corres)
       apply (rule conjI, clarsimp)
        apply (rule switch_to_thread_idempotent_corres)
       apply (clarsimp simp: corres_underlying_def fail_def)
      apply (wp | simp)+
    apply (fastforce simp: select_def gets_def active_tcbs_in_domain_def bind_def return_def domIff
                           get_def fst_def modify_def put_def change_current_domain_def)
   apply simp
  apply (rule corres_guard_imp)
    apply (rule dcorres_symb_exec_r)
      apply (clarsimp simp: assert_def)
      apply (rule conjI, clarsimp)
       apply (rule switch_to_thread_None_dcorres_L)
      apply (rule conjI, clarsimp)
       apply (rule switch_to_thread_None_dcorres_L)
      apply (clarsimp simp: corres_underlying_def fail_def)
     apply (wp | simp | fastforce)+
  done


lemma schedule_resume_cur_thread_dcorres:
         "\<And>cur cur_ts. dcorres dc \<top> (\<lambda>s. cur = cur_thread s \<and> st_tcb_at (op = cur_ts) cur s \<and> valid_etcbs s \<and> valid_sched s \<and> invs s \<and> scheduler_action s = resume_cur_thread)
        Schedule_D.schedule
       (do idle_t \<leftarrow> gets idle_thread;
           assert (runnable cur_ts \<or> cur = idle_t)
         od)"
  apply (rule stronger_corres_guard_imp)
    apply (rule schedule_resume_cur_thread_dcorres_L)
   apply (case_tac "cur \<noteq> idle_thread s'")
    apply (clarsimp simp: valid_sched_def valid_sched_action_def is_activatable_def invs_def valid_state_def
                          pred_tcb_at_def obj_at_def ct_in_cur_domain_def in_cur_domain_def)
    apply (frule(1) valid_etcbs_tcb_etcb)
    apply (auto simp: transform_def transform_current_thread_def all_active_tcbs_def transform_objects_def active_tcbs_in_domain_def etcb_at_def tcb_boundntfn_slot_def tcb_pending_op_slot_def
                          map_add_def restrict_map_def option_map_def transform_object_def transform_tcb_def valid_idle_def st_tcb_def2 get_tcb_def
                          transform_cnode_contents_def infer_tcb_pending_op_def transform_cap_def domIff st_tcb_at_kh_def obj_at_def only_idle_def
                    split: option.splits if_split Structures_A.kernel_object.splits Structures_A.thread_state.splits)[1]
     (* cur = idle_thread s' *)
   apply (subgoal_tac "cdl_current_thread s = None")
    apply (clarsimp simp: transform_def transform_current_thread_def)+
  done

lemma schedule_switch_thread_helper:
            "\<lbrakk> valid_etcbs s;
               valid_sched s;
               invs s;
               scheduler_action s = switch_thread t
             \<rbrakk>
             \<Longrightarrow> t \<in> active_tcbs_in_domain (cur_domain s) (transform s)"
  apply (clarsimp simp: valid_sched_def valid_sched_action_def weak_valid_sched_action_def is_activatable_def invs_def
                        valid_state_def pred_tcb_at_def obj_at_def switch_in_cur_domain_def in_cur_domain_def only_idle_def)
  apply (frule(1) valid_etcbs_tcb_etcb)
  apply (clarsimp simp: valid_idle_def pred_tcb_at_def)
  apply (drule_tac s="idle_thread s" in sym)
  apply (auto simp: transform_def transform_current_thread_def all_active_tcbs_def transform_objects_def active_tcbs_in_domain_def etcb_at_def
                        map_add_def restrict_map_def option_map_def transform_object_def transform_tcb_def valid_idle_def pred_tcb_at_def get_tcb_def tcb_pending_op_slot_def tcb_boundntfn_slot_def
                        transform_cnode_contents_def infer_tcb_pending_op_def transform_cap_def domIff st_tcb_at_kh_def obj_at_def only_idle_def
                  split: option.splits if_split Structures_A.kernel_object.splits Structures_A.thread_state.splits)
  done

lemma schedule_switch_thread_dcorres:
      "\<And>cur_ts. dcorres dc \<top>
        (\<lambda>s. cur = cur_thread s \<and> st_tcb_at (op = cur_ts) cur s \<and> valid_etcbs s \<and> valid_sched s \<and> invs s \<and> scheduler_action s = switch_thread t)
        Schedule_D.schedule
        (do y \<leftarrow> when (runnable cur_ts) (tcb_sched_action tcb_sched_enqueue cur);
            y \<leftarrow> guarded_switch_to t;
            set_scheduler_action resume_cur_thread
         od)"
  unfolding Schedule_D.schedule_def
  apply (rule_tac Q="\<top>" in corres_guard_imp)
    apply (rule_tac Pa'="\<lambda>s. valid_etcbs s \<and> valid_sched s \<and> invs s \<and> scheduler_action s = switch_thread t \<and> t \<noteq> idle_thread s"
                and Pb'="\<lambda>s. valid_etcbs s \<and> valid_sched s \<and> invs s \<and> scheduler_action s = switch_thread t \<and> t = idle_thread s"
                in corres_either_alternate)
     (* t \<noteq> idle_thread s *)
     apply (rule stronger_corres_guard_imp)
       apply (rule dcorres_symb_exec_r)
         apply (clarsimp simp: guarded_switch_to_def bind_assoc)
         apply (rule dcorres_symb_exec_r)
           apply (rule dcorres_symb_exec_r)
             apply (rule dcorres_rhs_noop_below_True[OF set_scheduler_action_dcorres])
             apply (rule corres_symb_exec_l_Ex)
             apply (rule corres_symb_exec_l_Ex)
             apply (rule corres_symb_exec_l_Ex)
             apply (rule corres_symb_exec_l_Ex)
             apply (rule switch_to_thread_same_corres)
            apply (wp gts_wp tcb_sched_action_transform hoare_drop_imp hoare_vcg_all_lift | clarsimp)+
      apply (frule schedule_switch_thread_helper, simp,simp,simp)
      apply (auto simp: select_def gets_def get_def bind_def return_def active_tcbs_in_domain_def
                        invs_def valid_state_def valid_objs_def change_current_domain_def
                    Schedule_D.switch_to_thread_def modify_def put_def
                    option_map_def restrict_map_def map_add_def get_tcb_def
                    transform_def transform_current_thread_def cur_tcb_def tcb_at_def)[1]
     apply simp
     apply fastforce
    (* t = idle_thread s *)
    apply (rule dcorres_symb_exec_r)
      apply (clarsimp simp: guarded_switch_to_def bind_assoc)
      apply (rule_tac Q'="\<lambda>ts s. idle ts" in dcorres_symb_exec_r)
        apply (clarsimp simp: assert_def)
        apply (rule conjI, clarsimp)
         apply (fold dc_def, rule dcorres_rhs_noop_below_True[OF set_scheduler_action_dcorres])
         apply (clarsimp simp: corres_underlying_def) (* contradiction *)
        apply (clarsimp simp: corres_underlying_def fail_def)
       apply (wp tcb_sched_action_transform| fastforce simp: invs_def valid_state_def)+
  done

lemma schedule_choose_new_thread_helper:
            "\<lbrakk> ready_queues s (cur_domain s) prio \<noteq> [];
               t = hd (ready_queues s (cur_domain s) prio);
               valid_sched_except_blocked s;
               invs s;
               scheduler_action s = choose_new_thread
             \<rbrakk>
             \<Longrightarrow> (\<exists>y. cdl_objects (transform s) t = Some y) \<and> t \<in> active_tcbs_in_domain (cur_domain s) (transform s)"
  apply (clarsimp simp: valid_sched_def valid_sched_action_def is_activatable_def invs_def
                        valid_state_def pred_tcb_at_def obj_at_def DetSchedInvs_AI.valid_queues_def
                        max_non_empty_queue_def only_idle_def)
  apply (erule_tac x="cur_domain s" in allE)
  apply (erule_tac x="prio" in allE)
  apply clarsimp
  apply (erule_tac x="hd (ready_queues s (cur_domain s) prio)" in ballE)
  apply (clarsimp simp: valid_idle_def pred_tcb_at_def)
  apply (drule_tac s="idle_thread s" in sym)
  apply (auto simp: transform_def transform_current_thread_def all_active_tcbs_def transform_objects_def active_tcbs_in_domain_def etcb_at_def
                       is_etcb_at_def
                        map_add_def restrict_map_def option_map_def transform_object_def transform_tcb_def valid_idle_def st_tcb_def2 get_tcb_def
                        transform_cnode_contents_def infer_tcb_pending_op_def transform_cap_def domIff st_tcb_at_kh_def obj_at_def only_idle_def tcb_pending_op_slot_def tcb_boundntfn_slot_def
                  split: option.splits if_split Structures_A.kernel_object.splits Structures_A.thread_state.splits)
  done

lemma idle_thread_not_in_queue:
  "\<lbrakk> valid_idle s; DetSchedInvs_AI.valid_queues s; ready_queues s d p \<noteq> [] \<rbrakk> \<Longrightarrow> idle_thread s \<noteq> hd (ready_queues s d p)"
  apply (clarsimp simp: valid_idle_def DetSchedInvs_AI.valid_queues_def pred_tcb_at_def obj_at_def)
  apply (erule_tac x="d" in allE)
  apply (erule_tac x="p" in allE)
  apply clarsimp
  apply (erule_tac x="idle_thread s" in ballE)
   apply clarsimp
  apply (frule hd_in_set)
  apply clarsimp
  done

lemma change_current_domain_dcorres: "dcorres dc \<top> \<top> change_current_domain next_domain"
  by (auto simp: corres_underlying_def change_current_domain_def next_domain_def bind_def return_def modify_def Let_def put_def select_def
                    get_def transform_def trans_state_def transform_objects_def transform_cdt_def transform_current_thread_def 
                    transform_asid_table_def)

lemma max_set_not_empty:
  "\<And>x::'a::{linorder,finite}. f x \<noteq> [] \<Longrightarrow> f (Max {x. f x \<noteq> []}) \<noteq> []"
  apply (rule_tac S="{x. f x \<noteq> []}" in Max_prop)
   apply auto
  done

lemma next_domain_valid_sched_except_blocked[wp]:
  "\<lbrace> valid_sched_except_blocked and (\<lambda>s. scheduler_action s  = choose_new_thread)\<rbrace> next_domain \<lbrace> \<lambda>_. valid_sched_except_blocked \<rbrace>"
  apply (simp add: next_domain_def Let_def)
  apply (wp, simp add: valid_sched_def valid_sched_action_2_def ct_not_in_q_2_def)
  done


lemma schedule_def_2:
  "Schedule_D.schedule \<equiv> do
     change_current_domain;
     (do
       next_domain \<leftarrow> gets cdl_current_domain;
       threads     \<leftarrow> gets (active_tcbs_in_domain next_domain);
       next_thread \<leftarrow> select threads;
       Schedule_D.switch_to_thread (Some next_thread)
     od \<sqinter> Schedule_D.switch_to_thread None)
   od"
  unfolding Schedule_D.schedule_def
  apply (subst alternative_bind_distrib_2, simp)
  done

lemma schedule_choose_new_thread_dcorres_fragment:
  "dcorres dc \<top>
        (\<lambda>s. valid_etcbs s \<and> valid_sched_except_blocked s \<and> invs s \<and> scheduler_action s = choose_new_thread)
        Schedule_D.schedule
        (do dom_time \<leftarrow> gets domain_time;
            y \<leftarrow> when (dom_time = 0) next_domain;
            y \<leftarrow> choose_thread;
            set_scheduler_action resume_cur_thread
         od)"
  apply (clarsimp simp: guarded_switch_to_def bind_assoc choose_thread_def)
  apply (rule dcorres_symb_exec_r, rename_tac dom_t)
    apply (case_tac "dom_t \<noteq> 0")
     apply (clarsimp)
     apply (rule dcorres_symb_exec_r, rename_tac cur_dom)
       apply (rule dcorres_symb_exec_r, rename_tac rq)
         apply (rule dcorres_rhs_noop_below_True[OF set_scheduler_action_dcorres])
         (* No threads in ready_queues *)
         apply (rule corres_guard_imp)
           apply (rule corres_if_rhs)
            apply (clarsimp simp: Schedule_D.schedule_def)
            apply (rule corres_alternate2)
            apply (rule change_current_domain_and_switch_to_idle_thread_dcorres)
           (* Threads in ready_queues *)
           apply (simp only: Schedule_D.schedule_def)
           unfolding max_non_empty_queue_def
           apply (rule corres_alternate1)
           apply (rule dcorres_symb_exec_r)
             apply (rule dcorres_symb_exec_r)
               apply (rule_tac P'="\<lambda>s. ready_queues s (cur_domain s) = rq \<and> valid_etcbs s \<and> valid_sched_except_blocked s \<and> invs s \<and> scheduler_action s = choose_new_thread"
                               in stronger_corres_guard_imp)
                 apply (rule corres_symb_exec_l_Ex)
                 apply (clarsimp)
                 apply (rule corres_symb_exec_l_Ex)
                 apply (rule corres_symb_exec_l_Ex)
                 apply (rule corres_symb_exec_l_Ex)
                 apply (rule switch_to_thread_same_corres)
                apply clarsimp
                apply (frule_tac prio="(Max {prio. ready_queues s' (cur_domain s') prio \<noteq> []})" in schedule_choose_new_thread_helper,simp,simp,simp,simp,simp)
                apply (clarsimp simp: valid_sched_def DetSchedInvs_AI.valid_queues_def max_non_empty_queue_def)
                apply (auto simp: select_def gets_def get_def bind_def return_def active_tcbs_in_domain_def
                        invs_def valid_state_def valid_objs_def change_current_domain_def
                    Schedule_D.switch_to_thread_def modify_def put_def
                    option_map_def restrict_map_def map_add_def get_tcb_def
                    transform_def transform_current_thread_def cur_tcb_def tcb_at_def)[1]
               apply (clarsimp simp: invs_def valid_state_def valid_sched_def max_non_empty_queue_def)
               apply (frule_tac p="Max {prio. ready_queues s' (cur_domain s') prio \<noteq> []}" in idle_thread_not_in_queue,simp,simp)
               apply (clarsimp)
              apply (wp hoare_drop_imp| simp | clarsimp simp: valid_sched_def)+
          apply (frule max_set_not_empty, fastforce)
         apply (wp hoare_drop_imp| simp)+
    apply (clarsimp simp: valid_sched_def)
    (* dom_t = 0 *)
    apply (simp only: schedule_def_2)
    apply (rule corres_guard_imp)
      apply (rule_tac r'="\<lambda>_ _. True" and  P=\<top> and P'=\<top> and R="\<lambda>_. \<top>" and R'="\<lambda>_ s. valid_etcbs s \<and> valid_sched_except_blocked s \<and> invs s \<and> scheduler_action s = choose_new_thread" in corres_split)
         apply (clarsimp)
         apply (rule dcorres_symb_exec_r)
           apply (rule dcorres_symb_exec_r, rename_tac rq)
             apply (fold dc_def, rule dcorres_rhs_noop_below_True[OF set_scheduler_action_dcorres])
             apply (rule corres_guard_imp)

               apply (rule corres_if_rhs)
                (* No threads in ready queues *)
                apply (rule corres_alternate2)
                apply (rule switch_to_idle_thread_dcorres)
               (* threads in ready queues *)
               apply (rule corres_alternate1)
               apply (rule dcorres_symb_exec_r)
                 apply (rule dcorres_symb_exec_r)
                   apply (rule_tac P'="\<lambda>s. ready_queues s (cur_domain s) = rq \<and> valid_etcbs s \<and> valid_sched_except_blocked s \<and> invs s \<and> scheduler_action s = choose_new_thread"
                          in stronger_corres_guard_imp)
                     apply (rule corres_symb_exec_l_Ex)
                     apply (rule corres_symb_exec_l_Ex)
                     apply (rule corres_symb_exec_l_Ex)
                     apply (rule switch_to_thread_same_corres)
                    apply clarsimp
                    apply (frule_tac prio="(Max {prio. ready_queues s' (cur_domain s') prio \<noteq> []})" in schedule_choose_new_thread_helper,simp,simp,simp,simp,simp)
                    apply (clarsimp simp: invs_def valid_state_def valid_sched_def)
                    apply (auto simp: select_def gets_def get_def bind_def return_def active_tcbs_in_domain_def
                        invs_def valid_state_def valid_objs_def change_current_domain_def
                        Schedule_D.switch_to_thread_def modify_def put_def
                        option_map_def restrict_map_def map_add_def get_tcb_def
                        transform_def transform_current_thread_def cur_tcb_def tcb_at_def)[1]
                   apply (clarsimp simp: invs_def valid_state_def valid_sched_def max_non_empty_queue_def)
                   apply (frule_tac p="Max {prio. ready_queues s' (cur_domain s') prio \<noteq> []}" in idle_thread_not_in_queue,simp,simp)
                   apply (clarsimp)
                  apply (wp hoare_drop_imp | clarsimp)+
              apply (frule max_set_not_empty, fastforce)
             apply (wp hoare_drop_imp | clarsimp)+
             apply simp
            apply (wp | clarsimp)+
        apply (rule change_current_domain_dcorres)
       unfolding dc_def
       apply (wp next_domain_valid_etcbs | simp)+
    apply (wp tcb_sched_action_transform | clarsimp simp: valid_sched_def)+
  done

lemma schedule_choose_new_thread_dcorres:
  "\<And>cur_ts cur. dcorres dc \<top>
        (\<lambda>s. cur = cur_thread s \<and> st_tcb_at (op = cur_ts) cur s \<and> valid_etcbs s \<and> valid_sched s \<and> invs s \<and> scheduler_action s = choose_new_thread)
        Schedule_D.schedule
        (do y \<leftarrow> when (runnable cur_ts) (tcb_sched_action tcb_sched_enqueue cur);
            dom_time \<leftarrow> gets domain_time;
            y \<leftarrow> when (dom_time = 0) next_domain;
            y \<leftarrow> choose_thread;
            set_scheduler_action resume_cur_thread
         od)"
  apply (rule dcorres_symb_exec_r)
    apply (rule corres_guard_imp)
      apply (rule schedule_choose_new_thread_dcorres_fragment)
     apply (wp tcb_sched_action_transform| simp add: valid_sched_def st_tcb_at_def obj_at_def not_cur_thread_def| clarsimp simp: transform_def)+
  done


(*
 * The schedulers correspond.
 *
 * Most of the difficulties in this proof arise from needing to dance
 * around differences in switching to the idle thread: The CapDL spec
 * switches to "None", while the abstract spec switches to an actual
 * thread.
 *)

lemma schedule_dcorres:
  "dcorres dc \<top> (invs and valid_sched and valid_etcbs) Schedule_D.schedule Schedule_A.schedule"
  apply (clarsimp simp: Schedule_A.schedule_def)
  apply (rule dcorres_symb_exec_r)
    apply (rename_tac cur)
    apply (rule dcorres_symb_exec_r)
      apply (rename_tac cur_ts)
      apply (rule dcorres_symb_exec_r)
        apply (rename_tac "sa", case_tac "sa")
          (* sa = resume_cur_thread *)
          apply clarsimp
          apply (rule schedule_resume_cur_thread_dcorres)
         (* sa = switch_thread *)
         apply clarsimp
         apply (rule schedule_switch_thread_dcorres)
        (* sa = choose_new_thread *)
        apply clarsimp
        apply (rule schedule_choose_new_thread_dcorres)
       apply (wp gts_st_tcb | simp )+
  done

(*
 * The next few lemmas show that updating the register LR_svc in the
 * tcb context of a thread does affect the state translation to capDL
 *)
lemma get_tcb_message_info_nextPC [simp]:
  "get_tcb_message_info (tcb_arch_update (tcb_context_update (\<lambda>ctx. ctx(LR_svc := pc))) tcb) =
   get_tcb_message_info tcb"
  by (simp add: get_tcb_message_info_def
                arch_tcb_context_get_def
                msg_info_register_def
                ARM.msgInfoRegister_def)

lemma map_msg_registers_nextPC [simp]:
  "map ((tcb_context tcb)(LR_svc := pc)) msg_registers =
   map (tcb_context tcb) msg_registers"
  by (simp add: msg_registers_def ARM.msgRegisters_def
                upto_enum_red fromEnum_def toEnum_def enum_register)

lemma get_ipc_buffer_words_nextPC [simp]:
  "get_ipc_buffer_words m (tcb_arch_update (tcb_context_update (\<lambda>ctx. ctx(LR_svc := pc))) tcb) =
   get_ipc_buffer_words m tcb"
  by (rule ext) (simp add: get_ipc_buffer_words_def)

lemma get_tcb_mrs_nextPC [simp]:
  "get_tcb_mrs m (tcb_arch_update (tcb_context_update (\<lambda>ctx. ctx(LR_svc := pc))) tcb) =
   get_tcb_mrs m tcb"
  by (simp add: get_tcb_mrs_def Let_def arch_tcb_context_get_def)

lemma transform_tcb_LR_svc:
  "transform_tcb m t (tcb_arch_update (tcb_context_update (\<lambda>ctx. ctx(LR_svc := pc))) tcb)
  = transform_tcb m t tcb"
  by (auto simp add: transform_tcb_def transform_full_intent_def Let_def
                     cap_register_def ARM.capRegister_def
                     arch_tcb_context_get_def)

(*
 * setNextPC in the tcb context is not observable on the capDL level.
 *)
lemma as_user_setNextPC_corres:
  "dcorres dc \<top> \<top> (return x) (as_user t (setNextPC pc))"
  apply (clarsimp simp: corres_underlying_def gets_the_def
                   as_user_def setNextPC_def get_tcb_def
                   setRegister_def simpler_modify_def
                   select_f_def return_def in_monad
                   set_object_def
                  split: option.splits Structures_A.kernel_object.splits)
  apply (subst tcb_context_update_aux)
  apply (simp add: transform_def transform_current_thread_def)
  apply (clarsimp simp: transform_objects_update_kheap_same_caps
                        transform_tcb_LR_svc transform_objects_update_same
                        arch_tcb_update_aux3)
  done

crunch transform_inv[wp]: set_thread_state_ext "\<lambda>s. transform s = cs"

lemma dcorres_dummy_set_thread_state_runnable:
  "dcorres dc \<top>
  (not_idle_thread ptr and st_tcb_at (\<lambda>t. (infer_tcb_pending_op ptr t) = (infer_tcb_pending_op ptr st)) ptr)
  (return ())
  (set_thread_state ptr st)"
  apply (rule wp_to_dcorres)
  apply (clarsimp simp:set_thread_state_def not_idle_thread_def set_object_def | wp)+
  apply (clarsimp simp:transform_def transform_current_thread_def st_tcb_at_def obj_at_def
       | rule ext)+
  apply (clarsimp simp:transform_objects_def not_idle_thread_def dest!:get_tcb_SomeD)
  apply (case_tac "x = ptr")
   apply (clarsimp simp:transform_tcb_def)
  apply (clarsimp simp:restrict_map_def Map.map_add_def)
  done

(*
 * Activating threads is not observable on the capDL level.
 *)
lemma activate_thread_corres:
  "dcorres dc \<top> (ct_in_state activatable and invs and valid_etcbs)
  (do t \<leftarrow> gets cdl_current_thread;
      case t of Some thread \<Rightarrow> do
       restart \<leftarrow> has_restart_cap thread;
       when restart $  KHeap_D.set_cap (thread,tcb_pending_op_slot) RunningCap
      od | None \<Rightarrow> return ()
  od)
  activate_thread"
  apply (simp add: activate_thread_def has_restart_cap_def gets_def bind_assoc)
  apply (rule dcorres_absorb_get_r)
  apply (rule dcorres_absorb_get_l)
  apply (simp add:get_thread_state_def bind_assoc thread_get_def)
  apply (rule dcorres_absorb_gets_the)
  apply (case_tac "cdl_current_thread (transform s'a) = None")
   apply (clarsimp simp: ct_in_state_def pred_tcb_at_def obj_at_def
     cdl_current_thread transform_current_thread_def valid_idle_def
     arch_activate_idle_thread_def
     split : if_splits dest!:get_tcb_SomeD invs_valid_idle)
  apply clarsimp
  apply (subgoal_tac "not_idle_thread (cur_thread s'b) s'b")
   prefer 2
   apply (clarsimp simp:transform_def transform_current_thread_def)
   apply (clarsimp simp:not_idle_thread_def)+
  apply (frule(1) valid_etcbs_get_tcb_get_etcb, clarsimp)
  apply (frule opt_object_tcb)
    apply simp
   apply simp
  apply (clarsimp simp:transform_tcb_def gets_def gets_the_def has_restart_cap_def
    get_thread_def bind_assoc cdl_current_thread transform_current_thread_def)
  apply (rule dcorres_absorb_get_l)
  apply (simp add:assert_opt_def when_def)
  apply (case_tac  "tcb_state obj'")
         apply (clarsimp simp:infer_tcb_pending_op_def tcb_pending_op_slot_def tcb_boundntfn_slot_def
           when_def pred_tcb_at_def ct_in_state_def obj_at_def
           dest!:get_tcb_SomeD)+
       apply (rule corres_guard_imp)
         apply (rule dcorres_symb_exec_r)
           apply (rule dcorres_symb_exec_r)
             apply (rule set_thread_state_corres[unfolded tcb_pending_op_slot_def])
            apply simp
            apply (wp dcorres_to_wp[OF as_user_setNextPC_corres,simplified])+
       apply (simp add:invs_mdb pred_tcb_at_def obj_at_def invs_valid_idle
         generates_pending_def not_idle_thread_def)
      apply (clarsimp simp:infer_tcb_pending_op_def arch_activate_idle_thread_def
             when_def pred_tcb_at_def ct_in_state_def obj_at_def tcb_pending_op_slot_def tcb_boundntfn_slot_def
             dest!:get_tcb_SomeD)+
  done

end

end
