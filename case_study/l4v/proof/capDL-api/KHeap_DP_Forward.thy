(*
 * Copyright 2014, NICTA
 *
 * This software may be distributed and modified according to the terms of
 * the GNU General Public License version 2. Note that NO WARRANTY is provided.
 * See "LICENSE_GPLv2.txt" for details.
 *
 * @TAG(NICTA_GPL)
 *)

theory KHeap_DP_Forward
imports ProofHelpers_DP
        "../../lib/Hoare_Sep_Tactics/Sep_SP"
begin

declare hoare_add_K[sp]

lemma strong_sep_coimpl_sep_wp[sep_sp]:
    "\<And>sep_lift.
     (\<And>R. \<lbrace>(\<lambda>s. (P \<leadsto>* R) (sep_lift s) )\<rbrace> f \<lbrace>\<lambda>rv. (\<lambda>s. (Q rv \<and>* R) (sep_lift s))\<rbrace>) \<Longrightarrow>
     \<lbrace>(\<lambda>s. (R) (sep_lift s))\<rbrace> f \<lbrace>\<lambda>rv s. ( Q rv \<and>* (P -* R) ) (sep_lift s)\<rbrace>"
  apply (atomize, erule allE,  
erule hoare_weaken_pre, erule (1) sep_snake_septraction)
done

declare hoare_strengthen_post[sp_pre]
declare hoare_seq_ext[rotated, sp] 
declare put_sp [sp] hoare_return_sp [sp] get_sp [sp] assert_sp [sp]

lemma gets_sp[sp]: "\<lbrace>\<lambda>s. P (f s) s\<rbrace> gets f \<lbrace>\<lambda>rv s. P rv s \<and> rv = f s\<rbrace>"
  apply (clarsimp simp: gets_def, sp)
  apply (fastforce)
done 

lemma gets_the_sp[]: "\<lbrace>\<lambda>s. Q s\<rbrace> gets_the f \<lbrace>\<lambda>rv s . Q s \<and> f s \<noteq> None \<and> rv = the (f s) \<rbrace>"
  apply (clarsimp simp: gets_the_def, sp sp: gets_sp)
  apply (case_tac x;  clarsimp simp: assert_opt_def)
  apply (sp, clarsimp)
  apply (intro conjI)
  apply (rule_tac x=a in exI)
  apply (clarsimp)
  by (metis option.sel)


lemma sep_state_eqI:"sep_heap x = sep_heap y \<Longrightarrow> sep_irq_node x = sep_irq_node y \<Longrightarrow> x = y"
  by (metis plus_sep_state_def sep_add_zero sep_state_add_def)

declare sep_disj_positive[simp] 
instantiation sep_state :: cancellative_sep_algebra 
begin
instance
 apply (intro_classes)
 apply (clarsimp simp: zero_sep_state_def)
 apply (clarsimp simp: sep_disj_sep_state_def)
 apply (clarsimp simp: plus_sep_state_def sep_state_add_def)
 apply (rule sep_state_eqI; simp add: sep_state_disj_def map_add_self)
apply (rule sep_state_eqI )
apply (clarsimp simp: plus_sep_state_def sep_state_add_def sep_disj_sep_state_def sep_state_disj_def)
  using map_add_left_eq apply blast
apply (clarsimp simp: plus_sep_state_def sep_state_add_def sep_disj_sep_state_def sep_state_disj_def)
  using map_add_left_eq apply blast
done


lemma precise_sep_any_map_c: "precise (sep_any_map_c p)"
apply (clarsimp simp: sep_any_def)
apply (subst surjective_pairing)
apply (unfold sep_map_c_def_alt)
  apply (clarsimp simp: precise_def sep_any_def   split: prod.splits)
 apply (rule sep_state_eqI)
  apply (clarsimp simp: sep_substate_def plus_sep_state_def sep_state_add_def)
apply (rule ext)
apply (drule_tac x=x in fun_cong)
apply (drule_tac x=x in fun_cong)
apply (drule_tac x=x in fun_cong)
apply (clarsimp)
apply (clarsimp simp: cap_to_sep_state_def split: if_splits)
apply (clarsimp simp: map_add_def split: option.splits; clarsimp 
simp: sep_disj_sep_state_def sep_state_disj_def )
  apply (meson map_disj_common)
  apply (meson map_disj_common)
  apply (meson map_disj_common)
apply (clarsimp)
done

lemma has_slots_simps:
  "has_slots (Tcb tcb)"
  "has_slots (CNode cnode)"
  "has_slots (AsidPool ap)"
  "has_slots (PageTable pt)"
  "has_slots (PageDirectory pd)"
  "\<not> has_slots Endpoint"
  "\<not> has_slots Notification"
  "\<not> has_slots (Frame f)"
  "\<not> has_slots Untyped"
  by (simp add: has_slots_def)+

lemma reset_cap_asid_id:
  "reset_cap_asid cap = reset_cap_asid cap'
  \<Longrightarrow> cap = cap'
     \<or> (\<exists>a b c d e f. cap = FrameCap f a b c d e)
     \<or> (\<exists>a b c. cap = PageTableCap a b c)
     \<or> (\<exists>a b c. cap = PageDirectoryCap a b c)"
  by (case_tac cap, (clarsimp simp: reset_cap_asid_def split: cdl_cap.splits)+)

(* Move to Helpers_SD *)
definition is_memory_cap :: "cdl_cap \<Rightarrow> bool"
where
    "is_memory_cap cap \<equiv>
       (case cap of
           FrameCap _ _ _ _ _ _     \<Rightarrow> True
         | PageTableCap _ _ _     \<Rightarrow> True
         | PageDirectoryCap _ _ _ \<Rightarrow> True
         | _                      \<Rightarrow> False)"

lemma reset_cap_asid_memory_cap [simp]:
  "\<not>is_memory_cap cap \<Longrightarrow> reset_cap_asid cap = cap"
  by (clarsimp simp: is_memory_cap_def reset_cap_asid_def
              split: cdl_cap.splits)

lemma is_memory_cap_reset_cap_asid [simp]:
  "is_memory_cap (reset_cap_asid cap) = is_memory_cap cap"
  by (clarsimp simp: is_memory_cap_def reset_cap_asid_def
              split: cdl_cap.splits)

lemmas reset_cap_asid_simps[simp] = reset_cap_asid_def
    [THEN meta_eq_to_obj_eq, THEN fun_cong,split_simps cdl_cap.split]

lemma reset_cap_asid_simps2:
  "reset_cap_asid cap = NullCap \<Longrightarrow> cap = NullCap"
  "reset_cap_asid cap = RunningCap \<Longrightarrow> cap = RunningCap"
  "reset_cap_asid cap = (UntypedCap dev a ra) \<Longrightarrow> cap = UntypedCap dev a ra"
  "reset_cap_asid cap = (EndpointCap b c d) \<Longrightarrow> cap = EndpointCap b c d"
  "reset_cap_asid cap = (NotificationCap e f g) \<Longrightarrow> cap = NotificationCap e f g"
  "reset_cap_asid cap = (ReplyCap h) \<Longrightarrow> cap = ReplyCap h"
  "reset_cap_asid cap = (MasterReplyCap i) \<Longrightarrow> cap = MasterReplyCap i"
  "reset_cap_asid cap = (CNodeCap j k l sz) \<Longrightarrow> cap = CNodeCap j k l sz"
  "reset_cap_asid cap = (TcbCap m) \<Longrightarrow> cap = TcbCap m"
  "reset_cap_asid cap = DomainCap \<Longrightarrow> cap = DomainCap"
  "reset_cap_asid cap = RestartCap \<Longrightarrow> cap = RestartCap"
  "reset_cap_asid cap = (PendingSyncSendCap n p q r s) \<Longrightarrow> cap = (PendingSyncSendCap n p q r s)"
  "reset_cap_asid cap = (PendingSyncRecvCap t isf ) \<Longrightarrow> cap = (PendingSyncRecvCap t isf)"
  "reset_cap_asid cap = (PendingNtfnRecvCap u) \<Longrightarrow> cap = (PendingNtfnRecvCap u)"
  "reset_cap_asid cap = IrqControlCap \<Longrightarrow> cap = IrqControlCap"
  "reset_cap_asid cap = (IrqHandlerCap v) \<Longrightarrow> cap = (IrqHandlerCap v)"
  "reset_cap_asid cap = AsidControlCap \<Longrightarrow> cap = AsidControlCap"
  "reset_cap_asid cap = (AsidPoolCap w x) \<Longrightarrow> cap = (AsidPoolCap w x)"
  "reset_cap_asid cap = (IOPortsCap y z) \<Longrightarrow> cap = (IOPortsCap y z)"
  "reset_cap_asid cap = IOSpaceMasterCap \<Longrightarrow> cap = IOSpaceMasterCap"
  "reset_cap_asid cap = (IOSpaceCap a1) \<Longrightarrow> cap = (IOSpaceCap a1)"
  "reset_cap_asid cap = (IOPageTableCap a2) \<Longrightarrow> cap = (IOPageTableCap a2)"
  "reset_cap_asid cap = (ZombieCap a3) \<Longrightarrow> cap = (ZombieCap a3)"
  "reset_cap_asid cap = (BoundNotificationCap a4) \<Longrightarrow> cap = (BoundNotificationCap a4)"
  "reset_cap_asid cap = (FrameCap dev aa rghts sz rset ma) \<Longrightarrow> \<exists>asid. cap = FrameCap dev aa rghts sz rset asid"
  "reset_cap_asid cap = (PageTableCap aa rights ma) \<Longrightarrow> \<exists>asid. cap = PageTableCap aa rights asid"
  "reset_cap_asid cap = (PageDirectoryCap aa rights as) \<Longrightarrow> \<exists>asid. cap = PageDirectoryCap aa rights asid"
by (clarsimp simp: reset_cap_asid_def split: cdl_cap.splits)+

lemma sep_map_c_any:
  "(p \<mapsto>c cap \<and>* R) s \<Longrightarrow> (p \<mapsto>c - \<and>* R) s"
  by (fastforce simp: sep_any_def sep_conj_exists)

lemma pure_extract:
  "\<lbrakk> <P \<and>* Q> s; pure P \<rbrakk> \<Longrightarrow> <P> s"
  by (fastforce simp: pure_def sep_state_projection_def sep_conj_def)

lemma throw_on_none_rv:
  "\<lbrace>\<lambda>s. case x of Some y \<Rightarrow> P y s | otherwise \<Rightarrow> False\<rbrace> throw_on_none x \<lbrace>P\<rbrace>, \<lbrace>Q\<rbrace>"
  apply (clarsimp simp: throw_on_none_def split: option.splits)
   apply (wp)+
  done

lemma oseq:
  "\<lbrakk> \<lbrace>P\<rbrace> gets_the f \<lbrace>Q\<rbrace>; \<forall>x. \<lbrace>Q x\<rbrace> gets_the $ g x \<lbrace>R\<rbrace> \<rbrakk> \<Longrightarrow> \<lbrace>P\<rbrace> gets_the (f |>> g) \<lbrace>R\<rbrace>"
  apply (fastforce simp: gets_def fail_def get_def return_def gets_the_def obind_def valid_def split_def
    Let_def bind_def assert_opt_def split:option.splits)
  done

lemma hoare_ex_all:
     "(\<forall>x. \<lbrace>P x\<rbrace> f \<lbrace>Q\<rbrace>) = \<lbrace>\<lambda>s. \<exists>x. P x s\<rbrace> f \<lbrace>Q\<rbrace>"
  apply (rule iffI)
  apply (fastforce simp: valid_def)+
done


lemma sep_any_All: "\<lbrace><ptr \<mapsto>c - \<and>* R>\<rbrace> f \<lbrace>Q\<rbrace> = (\<forall>x. \<lbrace><ptr \<mapsto>c x \<and>* R>\<rbrace> f \<lbrace>Q\<rbrace>)"
  apply (clarsimp simp: sep_any_def sep_conj_exists hoare_ex_all)
done

(* validE reasoning *)

lemma gets_the_wpE:
  "\<lbrace>\<lambda>s. case (f s) of None \<Rightarrow> True | Some (Inl e) \<Rightarrow> E e s | Some (Inr r) \<Rightarrow> Q r s \<rbrace> gets_the f \<lbrace>Q\<rbrace>,\<lbrace>E\<rbrace>"
  apply (clarsimp simp: validE_def )
  apply (sp sp: gets_the_sp)
  apply (clarsimp)
done
  

lemma gets_the_invE : "\<lbrace>P\<rbrace> gets_the f \<lbrace>\<lambda>_. P\<rbrace>, -"
  apply (wp)
  apply (clarsimp)
  done

lemma return_rv :"\<lbrace>P r\<rbrace> return (Inr r) \<lbrace>\<lambda>rv s. P rv s\<rbrace>, \<lbrace>\<lambda>_ _. True\<rbrace>"
  by (clarsimp simp: validE_def, wp, simp split: option.splits)

crunch inv[wp]: throw_on_none P

lemma hoare_if_simp:
  "\<lbrace>P\<rbrace> f \<lbrace>Q\<rbrace> \<Longrightarrow> \<lbrace>P\<rbrace> f \<lbrace>\<lambda>rv s. (if x then (\<lambda>rv s. Q rv s) else (\<lambda>rv s. Q rv s)) rv s\<rbrace>"
  by (clarsimp)

lemma hoare_if_simpE:
  "\<lbrakk>\<And>x. Q x = R x; \<lbrace>P\<rbrace> f \<lbrace>Q\<rbrace>,-\<rbrakk>
  \<Longrightarrow> \<lbrace>P\<rbrace> f \<lbrace>\<lambda>rv s. (if x rv s then (\<lambda>s. Q rv s) else (\<lambda>s. R rv s)) s\<rbrace>,-"
  by (clarsimp simp: validE_R_def validE_def split: sum.splits)

lemma hoare_gen_asmEx: "(P \<Longrightarrow> \<lbrace>P'\<rbrace> f \<lbrace>Q\<rbrace>, \<lbrace>E\<rbrace>) \<Longrightarrow> \<lbrace>P' and K P\<rbrace> f \<lbrace>Q\<rbrace>, \<lbrace>E\<rbrace>"
  by (fastforce simp: valid_def validE_def)

lemma unless_wp_not: "\<lbrace>\<lambda>s. P s \<and> Q\<rbrace> unless Q f \<lbrace>\<lambda>_. P\<rbrace>"
  by (clarsimp simp: unless_def when_def)

lemma false_e_explode:
  "\<lbrace>P\<rbrace> f \<lbrace>Q\<rbrace>,\<lbrace>\<lambda>_ _ . False\<rbrace> \<Longrightarrow> \<lbrace>P\<rbrace> f \<lbrace>Q\<rbrace>,\<lbrace>R\<rbrace>"
  by (fastforce simp: validE_def valid_def split: sum.splits)

(* sep rules *)
lemma sep_any_map_c_imp: "(dest \<mapsto>c cap) s \<Longrightarrow> (dest \<mapsto>c -) s"
  by (fastforce simp: sep_any_def)

lemma obj_exists_map_i:
  "<obj_id \<mapsto>o obj \<and>* R> s \<Longrightarrow> \<exists>obj'. (opt_object obj_id s = Some obj'
  \<and> object_clean obj = object_clean obj')"
  apply (clarsimp simp: opt_object_def sep_map_o_conj)
  apply (case_tac "cdl_objects s obj_id")
   apply (drule_tac x = "(obj_id,Fields)" in fun_cong)
    apply (clarsimp simp: lift_def object_to_sep_state_def object_project_def
      object_at_heap_def sep_state_projection_def
      sep_conj_def Let_unfold)
  apply (rule_tac x = a in exI,simp)
  apply (rule object_eqI)
   apply (drule_tac x = "(obj_id,Fields)" in fun_cong)
   apply (clarsimp simp: lift_def object_to_sep_state_def object_project_def
      object_at_heap_def sep_state_projection_def
      Let_unfold)
  apply (rule ext)
  apply (drule_tac x= "(obj_id,Slot x)" in fun_cong)
  apply (clarsimp simp: lift_def object_to_sep_state_def
      object_project_def sep_state_projection_def
      Let_unfold)
  done

lemma obj_exists_map_f:
  "<obj_id \<mapsto>f obj \<and>* R> s \<Longrightarrow>
  \<exists>obj'. (opt_object obj_id s = Some obj' \<and> object_type obj = object_type obj')"
  apply (clarsimp simp: opt_object_def sep_map_f_conj Let_def)
  apply (case_tac "cdl_objects s obj_id")
   apply (clarsimp simp: lift_def object_to_sep_state_def object_project_def
      object_at_heap_def sep_state_projection_def
      sep_conj_def Let_unfold)
  apply (rule_tac x = a in exI,simp)
  apply (clarsimp simp: lift_def object_to_sep_state_def object_project_def
      object_at_heap_def sep_state_projection_def
      Let_unfold)
  apply (drule_tac f = object_type in arg_cong)
  apply simp
  done

lemma object_slots_asid_reset:
  "object_slots (asid_reset obj) = reset_cap_asid \<circ>\<^sub>M (object_slots obj)"
  by (clarsimp simp: object_slots_def asid_reset_def update_slots_def
              split: cdl_object.splits)

lemma reset_cap_asid_idem [simp]:
  "reset_cap_asid (reset_cap_asid cap) = reset_cap_asid cap"
  by (simp add: reset_cap_asid_def split: cdl_cap.splits)

lemma opt_cap_sep_imp:
  "\<lbrakk><p \<mapsto>c cap \<and>* R> s\<rbrakk>
  \<Longrightarrow> \<exists>cap'. opt_cap p s = Some cap' \<and> reset_cap_asid cap' = reset_cap_asid cap"
  apply (clarsimp simp: opt_cap_def sep_map_c_conj Let_def)
  apply (clarsimp simp:  sep_map_c_def lift_def
    opt_object_def split_def
    sep_any_def sep_map_general_def slots_of_def
    sep_state_projection_def object_project_def
    object_slots_object_clean
    Let_unfold split:sep_state.splits option.splits)
done

thm set_cap_wp 

lemma opt_cap_sep_any_imp:
  "\<lbrakk><dest \<mapsto>c - \<and>* R> s\<rbrakk> \<Longrightarrow> \<exists>cap. opt_cap (dest) s = Some cap"
  apply (clarsimp simp: sep_any_exist
    opt_cap_def sep_map_c_conj Let_def)
  apply (clarsimp simp:  sep_map_c_def lift_def
    opt_object_def split_def object_slots_object_clean
    sep_any_def sep_map_general_def slots_of_def
    sep_state_projection_def object_project_def
    Let_unfold split:sep_state.splits option.splits)
done

lemma sep_f_size_opt_cnode:
  "\<lbrakk>< cap_object cnode_cap \<mapsto>f CNode (empty_cnode r) \<and>* R> s;
    (opt_cnode (cap_object cnode_cap) s) = Some obj \<rbrakk>
  \<Longrightarrow> r = cdl_cnode_size_bits obj"
  apply (clarsimp simp:sep_map_f_conj Let_def)
  apply (case_tac obj)
  apply (auto simp: intent_reset_def empty_cnode_def
    opt_cnode_def update_slots_def sep_state_projection_def
    opt_object_def object_wipe_slots_def
    object_project_def object_clean_def asid_reset_def
    split:cdl_cap.splits cdl_object.splits)
  done


(* concerete wp rules *)


lemma swap_parents_wp:
  "\<lbrace><R>\<rbrace>
   swap_parents src dest
  \<lbrace>\<lambda>_.  <R>\<rbrace>"
  by (clarsimp simp: swap_parents_def lift_def sep_state_projection_def)

lemma sep_snake_map_o_exists: "cdl.lift (x1 \<mapsto>o - \<leadsto>* R) s \<Longrightarrow> opt_object x1 s = Some y \<Longrightarrow> 
     <(x1 \<mapsto>o y \<and>* R)> s"
  apply (subgoal_tac "<(x1 \<mapsto>o y \<and>* sep_true)> s")
  apply (metis sep_any_exist sep_coimpl_def sep_snake_mp)
  apply (clarsimp simp: sep_map_o_conj)
  apply (clarsimp simp: opt_object_def)
  apply (clarsimp simp: object_to_sep_state_def sep_state_projection_def)
  apply (rule ext, clarsimp)
done

lemma sep_snake_map_o_exists': "cdl.lift (x1 \<mapsto>o y \<leadsto>* R) s \<Longrightarrow> opt_object x1 s = Some y \<Longrightarrow> 
     <(x1 \<mapsto>o y \<and>* R)> s"
  apply (subgoal_tac "<(x1 \<mapsto>o y \<and>* sep_true)> s")
  apply (metis sep_snake_mp)
  apply (clarsimp simp: sep_map_o_conj)
  apply (clarsimp simp: opt_object_def)
  apply (clarsimp simp: object_to_sep_state_def sep_state_projection_def)
  apply (rule ext, clarsimp)
done

lemma get_object_sp: "\<lbrace>ALLS x. <ptr \<mapsto>o x \<leadsto>* (ptr \<mapsto>o x \<longrightarrow>* R x) >\<rbrace> get_object ptr \<lbrace>\<lambda>rv. <R rv>\<rbrace>"
  apply (wp)
  apply (clarsimp)
  apply (erule_tac x=y in allE)
  apply (drule (1)  sep_snake_map_o_exists')
  apply (sep_solve)
  done




lemma map_add_disj_alt: "x \<bottom> y \<Longrightarrow> x ++ y \<bottom> z \<Longrightarrow> x \<bottom> y ++ z "
  using map_add_disj map_add_disj' by blast

lemma object_to_sep_state_minus_disj[simp]:
    "object_to_sep_state x1 y x \<bottom> object_to_sep_state x1 y (UNIV - x)"
    "object_to_sep_state x1 y x ++ object_to_sep_state x1 y (UNIV - x) =
     object_to_sep_state x1 y UNIV"
  apply (clarsimp simp: object_to_sep_state_def, rule map_disjI, rule set_eqI,
         clarsimp split: option.splits if_splits)
  apply (clarsimp simp: object_to_sep_state_def, rule ext, clarsimp simp: map_add_def)
done


lemma "Separation_Algebra.precise (sep_map_o p v)"
  apply (clarsimp simp: sep_map_o_def)
  by (simp add: sep_map_general_precise) 


lemma opt_object_the_simp: "(x = Some y) \<Longrightarrow> ( the x = y)"
  apply (clarsimp split: option.splits)
done

lemma get_cap_rv:
  "\<lbrace>\<lambda>s. <ptr \<mapsto>c cap \<and>* (ptr \<mapsto>c cap \<longrightarrow>* R cap)> s \<rbrace>
    get_cap ptr
   \<lbrace>\<lambda>rv. <R cap> \<rbrace>"
   apply (wp)
   apply (safe)
   apply (frule opt_cap_sep_imp)
   apply (clarsimp)
   apply (sep_mp)
   apply (clarsimp simp: split_def dest!: opt_cap_sep_imp)
  done


lemma sep_any_map_c_lift: "\<exists>v. <p \<mapsto>c v \<and>* R> s \<Longrightarrow> < p \<mapsto>c - \<and>* R> s"
 by (clarsimp simp: sep_any_def sep_conj_exists1)

 lemma sep_map_c_exists: "object_slots obj y = Some cap \<Longrightarrow> opt_object x s = Some obj \<Longrightarrow> 
       <((x,y) \<mapsto>c - \<and>* sep_true)> s "
   apply (rule sep_any_map_c_lift)
   apply (rule_tac x= cap in exI)
   apply (clarsimp simp:  sep_map_c_conj sep_heap_def sep_state_projection_def 
    object_project_def opt_object_def object_clean_def reset_cap_asid_def asid_reset_def
    update_slots_def object_slots_def intent_reset_def split: cdl_object.splits)
done

lemma set_cap_sp:
 "\<lbrace><(dest) \<mapsto>c - \<leadsto>* R>\<rbrace> set_cap dest cap
 \<lbrace>\<lambda>_.  <(dest) \<mapsto>c cap \<and>* R>\<rbrace>"
 apply (clarsimp simp: set_cap_def  split: prod.splits)
  apply (wp)
  apply (rule_tac obj=obj in set_object_slot_wp)
  apply (wpc; wp select_wp)
  apply (wp select_wp assert_wp get_object_sp get_cap_rv)
  apply (rule assert_wp)
  apply (wp) 
  apply (clarsimp simp: opt_object_def )
apply (intro impI conjI; (clarsimp simp: update_slots_def has_slots_def split: cdl_object.splits)?)
defer 
  apply (frule sep_map_c_exists[simplified opt_object_def] , assumption)
  apply (simp add: sep_snake_mp)
  apply (rule_tac x="CNode x4" in exI)
  apply (clarsimp)
  apply (fold fun_upd_def)
  apply (clarsimp simp: object_slots_def opt_object_def)
 apply (frule sep_map_c_exists[simplified opt_object_def], assumption)
  apply (simp add: sep_snake_mp)
apply (fastforce)
 apply (frule sep_map_c_exists[simplified opt_object_def], assumption)
  apply (simp add: sep_snake_mp)
apply (clarsimp simp: opt_object_def)
apply (fastforce)
apply (frule sep_map_c_exists[simplified opt_object_def], assumption)
  apply (simp add: sep_snake_mp)
apply (fastforce)
apply (frule sep_map_c_exists[simplified opt_object_def], assumption)
  apply (simp add: sep_snake_mp)
  apply (fastforce simp: opt_object_def)+
apply (intro impI conjI allI)
apply (frule sep_map_c_exists[simplified opt_object_def], assumption)
  apply (simp add: sep_snake_mp)
apply (rule_tac x = "Tcb (x3\<lparr>cdl_tcb_intent := x\<rparr>)" in exI)
apply (clarsimp)
apply (intro conjI)
 apply (clarsimp simp: object_clean_def intent_reset_def asid_reset_def
                             update_slots_def object_slots_def)
defer
apply (frule sep_map_c_exists[simplified opt_object_def], assumption)
  apply (simp add: sep_snake_mp)
apply (rule_tac x = "Tcb (x3)" in exI)
apply (clarsimp)
apply (clarsimp simp: object_slots_def)
done

lemma opt_cap_sep_map_c_exists: "opt_cap ptr s = Some cap \<Longrightarrow> 
       <((ptr) \<mapsto>c cap \<and>* sep_true)> s " 
 apply (clarsimp simp: sep_map_c_conj opt_cap_def split: prod.splits)
  apply (clarsimp simp: sep_state_projection_def 
         slots_of_def opt_object_def object_project_def object_clean_def split: option.splits)
  by (simp add: object_slots_asid_reset)

lemma sep_conj_sep_true_septraction: "R s \<Longrightarrow> (P \<and>* sep_true) s \<Longrightarrow> (P \<and>* (P -* R)) s"
  apply (clarsimp simp: sep_conj_def septraction_def pred_neg_def sep_impl_def)
  using sep_add_commute sep_disj_commuteI by fastforce

lemma get_cap_sp: "\<lbrace><R>\<rbrace> get_cap ptr 
   \<lbrace>\<lambda>rv s. <(ptr \<mapsto>c rv \<and>* (ptr \<mapsto>c rv -* R))> s \<rbrace>"
 apply (sp sp: gets_the_sp)
apply (clarsimp)
apply (drule opt_cap_sep_map_c_exists)
apply (erule (1) sep_conj_sep_true_septraction)
done

declare precise_sep_any_map_c[precise]


lemma  insert_cap_orphan_sp:
   "\<lbrace><dest \<mapsto>c - \<leadsto>* R>\<rbrace>
    insert_cap_orphan cap dest
   \<lbrace>\<lambda>_.<dest \<mapsto>c cap \<and>* R>\<rbrace>"
  apply (clarsimp simp: insert_cap_orphan_def)
  apply (sep_sp rl: get_cap_sp spec: set_cap_sp)+
  apply (clarsimp)
  apply (sep_forward_solve)
done

lemma insert_cap_orphan_valid:
   "\<lbrace><dest \<mapsto>c - \<and>* R>\<rbrace>
    insert_cap_orphan cap dest
   \<lbrace>\<lambda>_.<dest \<mapsto>c cap \<and>* R>\<rbrace>"
  apply (clarsimp simp: insert_cap_orphan_def)
  apply (sep_sp rl: get_cap_sp spec: set_cap_sp)+
  apply (clarsimp)
  apply (sep_forward_solve)
done


lemma move_cap_wp:
 "\<lbrace><dest \<mapsto>c - \<and>* src \<mapsto>c cap \<and>* R>\<rbrace>
    move_cap cap' src dest
  \<lbrace>\<lambda>_. <dest \<mapsto>c cap'  \<and>* src \<mapsto>c NullCap \<and>* R>\<rbrace>"
  apply (simp add: move_cap_def)
  apply (sep_sp rl: swap_parents_wp get_cap_sp spec: insert_cap_orphan_sp set_cap_sp)
  by (sep_forward_solve)

lemma move_cap_sp:
 "\<lbrace><R>\<rbrace>
    move_cap cap' src dest
  \<lbrace>\<lambda>_. <(src \<mapsto>c NullCap  \<and>* (src \<mapsto>c - -* (dest \<mapsto>c cap' \<and>* (dest \<mapsto>c - -* R))))>\<rbrace>"
  apply (simp add: move_cap_def)
  by (sep_sp rl: swap_parents_wp get_cap_sp spec: insert_cap_orphan_sp set_cap_sp)


lemma sep_snake_septraction_trivial: "R s \<Longrightarrow> (P \<leadsto>* (P -* R)) s"
by (erule sep_snake_septraction)


lemma sep_conj_coimpl_precise: "(P \<and>* R) s \<Longrightarrow> precise P \<Longrightarrow> (P \<leadsto>* R) s" 
  by (simp add: precise_conj_coimpl)


method sep_snake_coimpl declares precise = 
           (match conclusion in "(Q \<leadsto>* R) (s :: 'a :: cancellative_sep_algebra)" for Q R s \<Rightarrow>
             \<open>rule sep_conj_coimpl_precise[where P= Q, simplified precise]; (rule TrueI)? \<close>) 


lemma sep_conj_sep_impl_spec: "\<lbrakk>(P \<and>* (Q -* R)) h; \<And>h. (Q -* R) h \<Longrightarrow> (P \<longrightarrow>* R') h\<rbrakk> \<Longrightarrow> R' h"
  by (metis (full_types) sep.mult_commute sep_conj_sep_impl2)


lemma swap_cap_valid:
  "\<lbrace><dest \<mapsto>c cap \<and>*  src \<mapsto>c cap' \<and>* R>\<rbrace>
    swap_cap cap' src cap dest
   \<lbrace>\<lambda>_.<dest \<mapsto>c cap' \<and>* src \<mapsto>c cap \<and>* R>\<rbrace>"
  apply (clarsimp simp add: swap_cap_def)
  apply (sep_sp spec: set_cap_sp swap_parents_wp )
  by (sep_forward_solve)
  


lemma swap_cap_sp:
  "\<lbrace><R>\<rbrace>
    swap_cap cap' src cap dest
   \<lbrace>\<lambda>_. <(dest \<mapsto>c cap' \<and>* (dest \<mapsto>c - -* src \<mapsto>c cap \<and>* (src \<mapsto>c - -* R)))>\<rbrace>"
  apply (clarsimp simp add: swap_cap_def)
  apply (sep_sp spec: set_cap_sp swap_parents_wp)
done

lemma set_parent_inv:
  "\<lbrace><P>\<rbrace>
    set_parent child parent
   \<lbrace>\<lambda>_.<P>\<rbrace>"
  apply (clarsimp simp: set_parent_def sep_state_projection_def)
  apply wp
  apply clarsimp
  done

lemma not_untyped_cap_set_full_sp:
  "\<lbrace>P\<rbrace> set_untyped_cap_as_full src_cap cap src \<lbrace>\<lambda>r. pred_imp (K (\<not> is_untyped_cap cap))  P\<rbrace>"
  apply (clarsimp simp:set_untyped_cap_as_full_def)
  apply (safe)
  apply (wp)
  apply (wp)
  apply (clarsimp)
  apply (wp, clarsimp)
  apply (erule notE)
  apply (wp, clarsimp)
  apply (erule notE)
  apply (wp, clarsimp)
  done





lemma hoare_propagate_K: "\<lbrace>P\<rbrace> f \<lbrace>Q\<rbrace> \<Longrightarrow> \<lbrace>P and K R\<rbrace> f \<lbrace>\<lambda>rv. Q rv and K R\<rbrace>"
  apply (clarsimp simp: pred_conj_def valid_def)
apply (fastforce)
done 

lemma hoare_add_imp_K[sp]: "\<lbrace>P\<rbrace> f \<lbrace>Q\<rbrace> \<Longrightarrow> \<lbrace>\<lambda>s. K (R) s \<longrightarrow> P s\<rbrace> f \<lbrace>\<lambda>rv s. K (R) s \<longrightarrow> Q rv s \<rbrace>"
apply (clarsimp simp: pred_conj_def valid_def)
apply (fastforce)
done 

lemma get_cap_inv: "\<lbrace>P\<rbrace> get_cap ptr \<lbrace>\<lambda>rv. P\<rbrace>" 
 by (rule gets_the_inv)


lemma insert_cap_sibling_wp:
  "\<lbrace><dest \<mapsto>c - \<and>* R and K (\<not> is_untyped_cap cap)>\<rbrace>
    insert_cap_sibling cap src dest
   \<lbrace>\<lambda>_. <dest \<mapsto>c cap \<and>* R>\<rbrace>"
  apply (clarsimp simp: insert_cap_sibling_def)
  apply (sp, rule get_cap_inv)
  apply (sp sp:  get_cap_sp not_untyped_cap_set_full_sp)
  apply (rule set_cap_sp[THEN sep_sp], rule sp, rule sp, rule sp, rule sp)
    apply (clarsimp split: option.splits)
apply (intro conjI impI)
apply (sp)
apply (clarsimp)
 apply (sep_forward_solve)
apply (intro impI allI, wp set_parent_inv)
apply (clarsimp)
apply (sep_forward_solve)
done


lemma insert_cap_sibling_sp:
  "\<lbrace><R>\<rbrace>
    insert_cap_sibling cap src dest
   \<lbrace>\<lambda>rv s. \<not> is_untyped_cap cap \<longrightarrow>  <dest \<mapsto>c cap \<and>* (dest \<mapsto>c NullCap -*  R)> s\<rbrace>"
  apply (clarsimp simp: insert_cap_sibling_def)
  apply (sp)
  apply (rule get_cap_inv)
  apply (sp sp: hoare_add_imp_K hoare_add_K get_cap_sp not_untyped_cap_set_full_sp)
 apply (rule set_cap_sp[THEN sep_sp], rule sp, rule sp, rule sp, rule sp)
    apply (clarsimp split: option.splits)
apply (intro conjI impI)
apply (sp)
apply (clarsimp)
apply (sp)
apply (clarsimp)
apply (sep_forward_solve)
apply (intro impI allI, wp set_parent_inv)
apply (clarsimp)
apply (sep_forward_solve)
done

lemma insert_cap_child_sp:
  "\<lbrace><R>\<rbrace>
    insert_cap_child cap src dest
   \<lbrace>\<lambda>rv s. \<not> is_untyped_cap cap \<longrightarrow>  <dest \<mapsto>c cap \<and>* (dest \<mapsto>c NullCap -*  R)> s\<rbrace>"
  apply (clarsimp simp: insert_cap_child_def)

  apply (sep_sp rl: get_cap_sp not_untyped_cap_set_full_sp set_parent_inv spec: set_cap_sp)+
  apply (clarsimp)
  apply (sep_invert)
  apply (sep_forward)
  apply (erule septract_impl_cancel)
  apply (sep_forward)+
  by (simp add: sep_map_c_strictly_exact) 

lemma remove_parent_wp:
  "\<lbrace><P>\<rbrace>
   remove_parent obj
   \<lbrace>\<lambda>_.  <P>\<rbrace>"
   by (clarsimp simp: remove_parent_def lift_def sep_state_projection_def)


lemma get_cap_wp_rv:
  "\<lbrace>\<lambda>s. <ptr \<mapsto>c cap \<and>* R> s \<and>
   (\<forall>c. ((reset_cap_asid c = reset_cap_asid cap ) \<longrightarrow> Q c s)) \<rbrace>
    get_cap ptr
   \<lbrace> Q \<rbrace>"
   apply (wp)
   apply (safe)
   apply (clarsimp simp: split_def dest!: opt_cap_sep_imp)
  done

lemma get_cap_rv':
  "\<lbrace>\<lambda>s. <ptr \<mapsto>c cap \<and>* R> s \<and> Q cap s \<and> \<not>is_memory_cap cap\<rbrace>
    get_cap ptr
   \<lbrace>Q\<rbrace>"
  by (wp get_cap_wp_rv, fastforce)

lemma decode_tcb_invocation:
  "\<lbrace>P\<rbrace>decode_tcb_invocation cap cap_ref caps (TcbWriteRegistersIntent resume flags count regs)
  \<lbrace>\<lambda>_. P\<rbrace>"
apply (clarsimp simp: decode_tcb_invocation_def)
apply (wp alternative_wp)
apply (clarsimp)
done

lemma get_object_wp:
  "\<lbrace>P\<rbrace>
    get_object ptr
   \<lbrace>\<lambda>_. P\<rbrace>"
  apply (wp gets_the_inv)
done

lemma empty_slot_valid:
  "\<lbrace><dest \<mapsto>c - \<and>* R>\<rbrace>
    empty_slot dest
   \<lbrace>\<lambda>_. <dest \<mapsto>c NullCap \<and>* R>\<rbrace>"
  apply (clarsimp simp: empty_slot_def)
  apply (sep_sp spec:  get_cap_sp)
  apply (clarsimp split: option.splits)
  apply (intro conjI impI)
  apply (sp)
  apply (clarsimp)
  apply (sep_forward_solve)
    apply (sep_sp spec: remove_parent_wp set_cap_sp)
  apply (sep_forward_solve)
done


lemma invoke_cnode_insert_valid:
  "\<lbrace><dest \<mapsto>c - \<and>* R> and K (\<not> is_untyped_cap cap)\<rbrace>
     invoke_cnode (InsertCall cap src dest)
   \<lbrace>\<lambda>_. <dest \<mapsto>c cap \<and>* R>\<rbrace>"
  apply (clarsimp simp: invoke_cnode_def)
  apply (clarsimp simp: liftE_def pred_conj_def)
  apply (sp sp: hoare_add_K alternative_valid insert_cap_sibling_sp insert_cap_child_sp)
  apply (clarsimp simp: pred_conj_def)
  apply (sep_forward_solve)
done

lemma invoke_cnode_move_cap:
  "\<lbrace><dest \<mapsto>c - \<and>* src \<mapsto>c cap \<and>* R> \<rbrace> invoke_cnode (MoveCall cap' src dest)
  \<lbrace>\<lambda>_. <dest \<mapsto>c cap' \<and>* src \<mapsto>c NullCap \<and>* R>\<rbrace>,\<lbrace>Q\<rbrace>"
  apply (simp add:validE_def)
  apply (clarsimp simp:invoke_cnode_def liftE_bindE validE_def[symmetric])
  apply (sp sp: move_cap_sp)
  apply (sep_forward_solve)
done

lemma invoke_cnode_rotate1_wp:
  "\<lbrace><dest \<mapsto>c cap1 \<and>* src \<mapsto>c cap2 \<and>* R> \<rbrace>
     invoke_cnode (RotateCall cap1 cap2 dest src dest)
   \<lbrace>\<lambda>_. <dest \<mapsto>c cap2 \<and>* src \<mapsto>c cap1 \<and>* R>\<rbrace>"
  apply (clarsimp simp: invoke_cnode_def liftE_def)
  apply (sep_sp spec: swap_cap_sp)
  apply (clarsimp, sep_forward_solve)
  done

lemma invoke_cnode_rotate2_wp:
   "(dest) \<noteq> (rnd) \<Longrightarrow>
  \<lbrace><dest \<mapsto>c cap1 \<and>* src \<mapsto>c cap2 \<and>*
    rnd \<mapsto>c - \<and>* R>\<rbrace>
     invoke_cnode (RotateCall cap1 cap2 dest src rnd)
  \<lbrace>\<lambda>_. <dest \<mapsto>c NullCap \<and>* src \<mapsto>c cap1 \<and>*
    rnd \<mapsto>c cap2 \<and>* R>\<rbrace>"
  apply (clarsimp simp: invoke_cnode_def liftE_def)
  apply (sep_sp spec: swap_cap_sp move_cap_sp)
  apply (clarsimp, sep_forward_solve)
  done

lemma get_cnode_wp [wp]:
  "\<lbrace> \<lambda>s. case (cdl_objects s a) of Some (CNode x) \<Rightarrow> P x s | _ \<Rightarrow> False \<rbrace>
     get_cnode a
   \<lbrace> P \<rbrace>"
  apply (clarsimp simp: get_cnode_def)
  apply (sp sp: gets_the_sp return_sp)
  apply (clarsimp simp: opt_object_def split: cdl_object.splits)
  apply (sp)
  apply (clarsimp simp: opt_object_def split: cdl_object.splits)
  done

lemma get_cnode_sp:
  "\<lbrace>\<lambda>s. P s  \<rbrace>
     get_cnode a
   \<lbrace>\<lambda>rv s. P s \<and>  (\<exists>x. cdl_objects s a = Some (CNode x) \<and> rv = x)   \<rbrace>"
  apply (clarsimp simp: get_cnode_def)
  apply (sp sp: gets_the_sp return_sp)
  apply (clarsimp simp: opt_object_def split: cdl_object.splits)
  apply (sp)
  apply (clarsimp simp: opt_object_def split: cdl_object.splits)
  done

lemma resolve_address_bits_wp:
 "\<lbrace> \<lambda>s. P s \<rbrace>
  resolve_address_bits cnode_cap cap_ptr remaining_size
  \<lbrace> \<lambda>_. P \<rbrace>, \<lbrace> \<lambda>_. P \<rbrace>"
  apply (clarsimp simp: gets_the_resolve_cap[symmetric])
  apply (wp)
  apply simp
done

lemma resolve_cap_wp [wp]:
  "\<lbrace> P \<rbrace>
    gets_the (resolve_cap cnode_cap cap_ptr remaining_size)
  \<lbrace> \<lambda>_. P \<rbrace>"
  by (wp gets_the_inv)



lemma whenE_sp[sp]: "\<lbrace>P\<rbrace> f \<lbrace>Q\<rbrace>, \<lbrace>E\<rbrace>  \<Longrightarrow> 
      \<lbrace>\<lambda>s. P s \<rbrace> whenE cond f \<lbrace>\<lambda>rv s. if cond then Q rv s else P s\<rbrace>, \<lbrace>E\<rbrace>"
  apply (clarsimp simp: whenE_def returnOk_def)
  apply (clarsimp simp: validE_def, sp, clarsimp split: prod.splits)
done

lemma whenE_sp_throw[sp]: "
      \<lbrace>\<lambda>s. P s \<rbrace> whenE cond throw \<lbrace>\<lambda>rv s. if cond then P s \<and> rv = Inl undefined else P s\<rbrace>"
  apply (clarsimp simp: whenE_def returnOk_def throwError_def)
  apply (sp, clarsimp)
done

lemma lookup_slot_for_cnode_op_inv [wp]:
  "\<lbrace>P\<rbrace>
    lookup_slot_for_cnode_op cnode_cap cap_ptr remaining_size
  \<lbrace>\<lambda>_. P \<rbrace>"
  apply (clarsimp simp: lookup_slot_for_cnode_op_def split_def )
  apply (sp sp: seqE[simplified validE_def, where E="\<lambda>_. P"])
  apply (sp)
  apply (clarsimp split: if_splits sum.splits)
  apply (assumption)
    apply (sp sp: seqE[simplified validE_def, where E="\<lambda>_. P"])
  apply (clarsimp simp: fault_to_except_def)
  apply (clarsimp simp: gets_the_resolve_cap[symmetric])
  apply (clarsimp simp: handleE'_def)
  apply (sp sp: gets_the_sp)
  apply (clarsimp split: sum.splits)
  apply (intro allI conjI impI)
  apply (sp sp: throwError_wp[simplified validE_def])
  apply (clarsimp)
  apply (intro conjI allI impI)
  apply (simp add: isLeft_case_sum isLeft_def)
  apply (clarsimp)
  apply (assumption)
  apply (sp)
apply (intro conjI allI impI)
  apply (simp add: isLeft_case_sum isLeft_def)
  apply (clarsimp)
apply (assumption)
 apply (clarsimp split: if_splits)
apply (intro conjI allI impI)
apply (clarsimp simp: returnOk_def, sp)
apply (clarsimp, assumption)
  apply (sp sp: throwError_wp[simplified validE_def])
apply (simp)
done


lemma lookup_slot_for_cnode_op_wpE:
  "\<lbrace>P\<rbrace>
    lookup_slot_for_cnode_op cnode_cap cap_ptr remaining_size
  \<lbrace>\<lambda>_. P \<rbrace>,\<lbrace>\<lambda>_. P \<rbrace>"
  apply (clarsimp simp: validE_def)
  apply (wp)
done

end
