(*
 * Copyright 2014, NICTA
 *
 * This software may be distributed and modified according to the terms of
 * the GNU General Public License version 2. Note that NO WARRANTY is provided.
 * See "LICENSE_GPLv2.txt" for details.
 *
 * @TAG(NICTA_GPL)
 *)

theory Proof_SI
imports
  CreateObjects_SI
  CreateIRQCaps_SI
  DuplicateCaps_SI
  InitVSpace_SI
  InitTCB_SI
  InitCSpace_SI
  InitIRQ_SI
  StartThreads_SI
begin

lemma parse_bootinfo_sep:
  "\<lbrace>\<guillemotleft>((\<And>* (cptr, cap) \<in> set (zip [ustart .e. uend - 1] untyped_caps). (si_cnode_id, unat cptr) \<mapsto>c cap) \<and>*
      (\<And>* cptr \<in> set [fstart .e. fend - 1]. (si_cnode_id, unat cptr) \<mapsto>c NullCap)  \<and>*
      (\<And>* obj_id\<in>(\<Union>cap\<in>set untyped_caps. cap_free_ids cap). obj_id \<mapsto>o Untyped) \<and>* R)
     and K (bi_untypes bootinfo = (ustart, uend) \<and>
            bi_free_slots bootinfo = (fstart, fend) \<and>
            unat ustart < 2 ^ si_cnode_size \<and>
            unat (uend - 1) < 2 ^ si_cnode_size \<and>
            unat fstart < 2 ^ si_cnode_size \<and>
            unat (fend - 1) < 2 ^ si_cnode_size \<and>
            uend \<noteq> 0 \<and>
            fend \<noteq> 0 \<and>
            list_all is_full_untyped_cap untyped_caps \<and>
            length untyped_caps = unat uend - unat ustart) \<guillemotright>\<rbrace>
    parse_bootinfo bootinfo
   \<lbrace>\<lambda>rv.
    \<guillemotleft>((\<And>* (cptr, cap) \<in> set (zip (fst rv) untyped_caps). (si_cnode_id, unat cptr) \<mapsto>c cap) \<and>*
      (\<And>* cptr \<in> set (snd rv). (si_cnode_id, unat cptr) \<mapsto>c NullCap)  \<and>*
      (\<And>* obj_id\<in>(\<Union>cap\<in>set untyped_caps. cap_free_ids cap). obj_id \<mapsto>o Untyped) \<and>* R) and
     K (rv = ([fst (bi_untypes bootinfo) .e. snd (bi_untypes bootinfo) - 1],
              [fst (bi_free_slots bootinfo) .e. snd (bi_free_slots bootinfo) - 1]))\<guillemotright> \<rbrace>"
  apply (clarsimp simp: parse_bootinfo_def)
  apply (cases bootinfo, clarsimp)
  apply wp
  apply (clarsimp simp: zip_map1 comp_def split_beta')
  done

lemma parse_spec_inv:
  "\<lbrace>\<lambda>s. \<guillemotleft>R\<guillemotright> s\<rbrace>
     parse_spec spec obj_ids
   \<lbrace>\<lambda>rv s. \<guillemotleft>R\<guillemotright> s\<rbrace>"
  apply (clarsimp simp: parse_spec_def sep_state_projection2_def)
  apply (wp)
  apply clarsimp
  done

lemma parse_spec_sep:
  "\<lbrace>\<lambda>s. True\<rbrace>
     parse_spec spec obj_ids
   \<lbrace>\<lambda>_ s. set obj_ids = dom (cdl_objects spec) \<and> distinct obj_ids \<rbrace>"
  apply (clarsimp simp: parse_spec_def)
  apply (wp)
  apply clarsimp
  done

(* This isn't actually all the combinations, but enough of them for what I needed. *)
lemma object_types_distinct:
 "tcb_at x s     \<Longrightarrow> \<not> cnode_at x s"
 "table_at x s   \<Longrightarrow> \<not> cnode_at x s"
 "table_at x s   \<Longrightarrow> \<not> tcb_at x s"
 "capless_at x s \<Longrightarrow> \<not> cnode_at x s"
 "capless_at x s \<Longrightarrow> \<not> tcb_at x s"
 "capless_at x s \<Longrightarrow> \<not> table_at x s"
 "capless_at x s \<Longrightarrow> \<not> pt_at x s"
 "capless_at x s \<Longrightarrow> \<not> pd_at x s"
 "capless_at x s \<Longrightarrow> \<not> asidpool_at x s"
  by (clarsimp simp: object_at_def is_tcb_def is_cnode_def is_pd_def is_pt_def
                     is_ep_def is_ntfn_def is_asidpool_def is_frame_def
                     is_untyped_def | rule conjI |
      clarsimp split: cdl_object.splits)+

lemma real_objects_some_type:
  "well_formed spec \<Longrightarrow>
   {obj_id. real_object_at obj_id spec \<and>
       \<not> cnode_at obj_id spec \<and>
       \<not> tcb_at obj_id spec \<and>
       \<not> pt_at obj_id spec \<and>
       \<not> pd_at obj_id spec \<and>
       \<not> untyped_at obj_id spec \<and>
       \<not> ep_at obj_id spec \<and>
       \<not> ntfn_at obj_id spec \<and>
       \<not> frame_at obj_id spec} = {}"
  apply (clarsimp simp: object_at_def is_tcb_def is_cnode_def is_pd_def is_pt_def
                        is_ep_def is_ntfn_def is_asidpool_def is_frame_def is_untyped_def)
  apply (clarsimp split: cdl_object.splits)
  apply (drule_tac obj_id=x in well_formed_asidpool_at)
  apply (clarsimp simp: real_object_at_def object_at_def is_asidpool_def irq_nodes_def is_irq_node_def
                 split: cdl_object.splits)
  by metis

lemma object_at_irq_node_irq_node_at:
  "\<lbrakk>well_formed spec; object_at P obj_id spec; obj_id \<in> irq_nodes spec\<rbrakk> \<Longrightarrow> irq_node_at obj_id spec"
  apply (clarsimp simp: object_at_def)
  apply (frule (2) well_formed_irq_nodes_object_type)
  apply (simp add: object_type_is_object)
  done

lemma capdl_objects_by_parts:
  "well_formed spec \<Longrightarrow>
   (sep_map_set_conj P {obj_id. real_object_at obj_id spec}) =
   (sep_map_set_conj P {obj_id. cnode_at obj_id spec} \<and>*
    sep_map_set_conj P {obj_id. tcb_at obj_id spec} \<and>*
    sep_map_set_conj P {obj_id. table_at obj_id spec} \<and>*
    sep_map_set_conj P {obj_id. capless_at obj_id spec})"
  apply (rule sym)
  apply (subst (5) sep_map_set_conj_restrict [where t = "(\<lambda>obj. cnode_at obj spec)"], simp)
  apply (subst (6) sep_map_set_conj_restrict [where t = "(\<lambda>obj. tcb_at obj spec)"], simp)
  apply (subst (7) sep_map_set_conj_restrict [where t = "(\<lambda>obj. table_at obj spec)"], simp)
  apply (subst (8) sep_map_set_conj_restrict [where t = "(\<lambda>obj. capless_at obj spec)"], simp)
  apply (clarsimp simp: object_types_distinct real_object_not_irq_node real_objects_some_type
                  cong: rev_conj_cong)
  done

lemma objects_empty_by_parts:
  "well_formed spec \<Longrightarrow>
   (objects_empty spec t {obj_id. real_object_at obj_id spec}) =
   (objects_empty spec t {obj_id. cnode_at obj_id spec} \<and>*
    objects_empty spec t {obj_id. tcb_at obj_id spec} \<and>*
    objects_empty spec t {obj_id. table_at obj_id spec} \<and>*
    objects_empty spec t {obj_id. capless_at obj_id spec})"
  by (clarsimp simp: objects_empty_def capdl_objects_by_parts)

lemma objects_initialised_by_parts:
  "well_formed spec \<Longrightarrow>
   (objects_initialised spec t {obj_id. real_object_at obj_id spec}) =
   (objects_initialised spec t {obj_id. cnode_at obj_id spec} \<and>*
    objects_initialised spec t {obj_id. tcb_at obj_id spec} \<and>*
    objects_initialised spec t {obj_id. table_at obj_id spec} \<and>*
    objects_initialised spec t {obj_id. capless_at obj_id spec})"
  by (clarsimp simp: objects_initialised_def capdl_objects_by_parts)

lemma object_empty_object_initialised_capless:
  "capless_at obj_id spec \<Longrightarrow>
   object_empty spec t obj_id = object_initialised spec t obj_id"
  apply (rule ext)
  apply (clarsimp simp: object_empty_def object_initialised_def)
  apply (clarsimp simp: object_initialised_general_def object_default_state_def2)
  apply (fastforce simp: object_at_def update_slots_def
                         object_default_state_def2 spec2s_def
                         is_ep_def is_ntfn_def is_asidpool_def
                         is_frame_def is_untyped_def cdl_frame.splits
                  split: cdl_object.splits)
  done

lemma objects_empty_objects_initialised_capless:
  "objects_empty spec t {obj_id. capless_at obj_id spec} =
   objects_initialised spec t {obj_id. capless_at obj_id spec}"
  apply (clarsimp simp: objects_empty_def objects_initialised_def)
  apply (rule sep.prod.cong, simp)
  apply (clarsimp simp: object_empty_object_initialised_capless)
  done

lemma valid_case_prod':
  "(\<And>x y. \<lbrace>P x y\<rbrace> f x y \<lbrace>Q\<rbrace>) \<Longrightarrow> \<lbrace>P (fst v) (snd v)\<rbrace> case v of (x, y) \<Rightarrow> f x y \<lbrace>Q\<rbrace>"
  by (clarsimp split: prod.splits)

lemma le_list_all:
  "\<lbrakk>unat start < 2 ^ si_cnode_size; unat (end - 1) < 2 ^ si_cnode_size\<rbrakk>
  \<Longrightarrow> list_all (\<lambda>n. (n::32 word) < 2 ^ si_cnode_size) [start .e. end - 1]"
  apply (clarsimp simp: list_all_iff)
  apply (subst word_arith_power_alt)
  apply simp
  by (metis (no_types) dual_order.strict_trans2 unat_less_2_si_cnode_size word_of_int_numeral word_of_int_power_hom)

lemma sep_conj_pred_conj:
  "(P \<and>* (P' and K Q)) s = ((P \<and>* P') and K Q) s"
  by (case_tac "Q = False", simp_all)

lemma list_all_drop:
  "list_all P xs \<Longrightarrow> list_all P (drop n xs)"
  by (fastforce simp: list_all_iff dest: in_set_dropD)

lemma dom_map_of_zip':
  "length xs \<le> length ys \<Longrightarrow> dom (map_of (zip xs ys)) = set xs"
  apply (subst zip_take_length [symmetric])
  apply (subst dom_map_of_zip, simp+)
  done


(* Dirty hack that is sadly needed to make the below proof work. *)
declare [[unify_search_bound = 1000]]

lemma small_one:
  "\<lbrakk>well_formed spec;
   set obj_ids = dom (cdl_objects spec); distinct obj_ids;
   real_ids = [obj_id \<leftarrow> obj_ids. real_object_at obj_id spec];
   length obj_ids + length [obj\<leftarrow>obj_ids. cnode_or_tcb_at obj spec] \<le> unat fend - unat fstart;
   length untyped_caps = unat uend - unat ustart;
   distinct_sets (map cap_free_ids untyped_caps);
   list_all is_full_untyped_cap untyped_caps;
   list_all well_formed_untyped_cap untyped_caps;
   list_all (\<lambda>c. \<not> is_device_cap c) untyped_caps;
   bi_untypes bootinfo = (ustart, uend);
   bi_free_slots bootinfo = (fstart, fend);
   unat ustart < 2 ^ si_cnode_size;
   unat (uend - 1) < 2 ^ si_cnode_size;
   unat fstart < 2 ^ si_cnode_size;
   unat (fend - 1) < 2 ^ si_cnode_size;
   uend \<noteq> 0; fend \<noteq> 0;
   [ustart .e. uend - 1] = untyped_cptrs;
   [fstart .e. fend - 1] = free_cptrs;
   (map_of (zip [obj\<leftarrow>obj_ids . cnode_or_tcb_at obj spec] (drop (length obj_ids) [fstart .e. fend - 1]))) = dup_caps
   \<rbrakk> \<Longrightarrow>
   \<lbrace>\<guillemotleft>(\<And>* (cptr, cap) \<in> set (zip untyped_cptrs untyped_caps). (si_cnode_id, unat cptr) \<mapsto>c cap) \<and>*
     (\<And>* cptr \<in> set free_cptrs. (si_cnode_id, unat cptr) \<mapsto>c NullCap)  \<and>*
     (\<And>* obj_id\<in>(\<Union>cap\<in>set untyped_caps. cap_free_ids cap). obj_id \<mapsto>o Untyped) \<and>*
    si_objects \<and>* si_irq_nodes spec \<and>* R\<guillemotright>\<rbrace>
   init_system spec bootinfo obj_ids
  \<lbrace>\<lambda>_ s. \<exists>t.
    \<guillemotleft>objects_initialised spec t {obj_id. real_object_at obj_id spec} \<and>*
     irqs_initialised spec t (used_irqs spec) \<and>*
    (\<And>* cptr\<in>set (take (card (dom (cdl_objects spec))) free_cptrs). (si_cnode_id, unat cptr) \<mapsto>c NullCap) \<and>*
     si_caps_at t dup_caps spec False {obj_id. cnode_or_tcb_at obj_id spec} \<and>*
     si_objects \<and>*
     si_objects_extra_caps (dom (cdl_objects spec))
                            (free_cptrs :: 32 word list)
                            (untyped_cptrs :: 32 word list) spec \<and>* R\<guillemotright> s \<and>
     inj_on t (dom (cdl_objects spec)) \<and> dom t = set obj_ids\<rbrace>"
  apply clarsimp
  apply (frule (1) le_list_all [where start = ustart])
  apply (frule (1) le_list_all [where start = fstart])
  apply (frule well_formed_objects_card)
  apply (insert distinct_card [symmetric, where xs ="[obj\<leftarrow>obj_ids . cnode_or_tcb_at obj spec]"], simp)
  apply (frule distinct_card [symmetric])
  apply (clarsimp simp: init_system_def, wp valid_case_prod')
           apply (rule hoare_ex_wp, rename_tac t, rule_tac t=t in start_threads_sep [sep_wandise], simp)
          apply (rule hoare_ex_wp, rename_tac t, rule_tac t=t and
                                                 free_cptrs="[fstart .e. fend - 1]" in init_cspace_sep [sep_wandise])
         apply (rule hoare_ex_wp, rename_tac t, rule_tac t=t in init_tcbs_sep [sep_wandise])
        apply (rule hoare_ex_wp, rename_tac t, rule_tac t=t in init_vspace_sep [sep_wandise])
       apply (rule hoare_ex_wp, rename_tac t, rule_tac t=t in init_pd_asids_sep [sep_wandise])
      apply (rule hoare_ex_wp, rename_tac t, rule_tac t=t and dev=False in init_irqs_sep [sep_wandise])
     apply (rule hoare_ex_wp, rename_tac t, rule_tac t=t and dev=False and
                                            untyped_cptrs = "[ustart .e. uend - 1]" and
                                            free_cptrs_orig = "[fstart .e. fend - 1]" in duplicate_caps_sep [sep_wandise])
     apply (rule create_irq_caps_sep [where dev = False,sep_wandise,
            where free_cptrs_orig = "[fstart .e. fend - 1]"
              and untyped_cptrs = "[ustart .e. uend - 1]"
              and orig_caps = "map_of (zip [obj\<leftarrow>obj_ids. real_object_at obj spec] [fstart .e. fend - 1])"
              and spec = spec])
    apply (wp sep_wp: create_objects_sep [where untyped_caps = untyped_caps and dev = False])
    apply (wp sep_wp: parse_bootinfo_sep [where fstart = fstart
                                            and fend = fend
                                            and ustart = ustart
                                            and uend = uend
                                            and untyped_caps = untyped_caps])
  apply (subst objects_initialised_by_parts, assumption)
  apply (subst objects_empty_by_parts, assumption)+
  apply (subst objects_empty_objects_initialised_capless)+
  apply clarsimp
  apply (sep_cancel+ | intro conjI allI impI | erule sep_curry[rotated, where P=R])+

  apply simp
  apply (intro conjI allI impI | sep_cancel+)+
   apply (intro conjI pred_andI)
      apply sep_cancel+
      apply (intro conjI pred_andI allI impI)
      apply (erule sep_curry[rotated, where P=R])
      apply (intro conjI pred_andI allI impI)
       apply sep_solve
      apply (erule (1) le_list_all)
     apply (rule list_all_drop, erule (1) le_list_all)
    apply simp
   apply (subst dom_map_of_zip')
    apply (insert length_filter_le [where xs = obj_ids and P="\<lambda>obj. real_object_at obj spec"], simp)
   apply simp
  apply (erule (1) le_list_all)
  done

(* FIXME, make the acquiring of the object_ids part of sys_init, not a parameter. *)



lemma set_inter_rewrite:
  " ({x. P x} \<inter> S) =
     {x \<in> S. P x}"
  by fast


(**************************************************
 * The top level lemma for system initialisation. *
 **************************************************)

lemma sys_init:
  "\<lbrakk>well_formed spec; set obj_ids = dom (cdl_objects spec); distinct obj_ids\<rbrakk> \<Longrightarrow>
   \<lbrace>\<guillemotleft>valid_boot_info bootinfo spec \<and>* R\<guillemotright>\<rbrace>
   init_system spec bootinfo obj_ids
  \<lbrace>\<lambda>_ s. \<exists>t.
    \<guillemotleft>objects_initialised spec t {obj_id. real_object_at obj_id spec} \<and>*
     irqs_initialised spec t (used_irqs spec) \<and>*
     si_final_objects spec t \<and>* R\<guillemotright> s \<and>
     inj_on t (set obj_ids) \<and> dom t = set obj_ids\<rbrace>"
  apply (frule distinct_card)
  apply (insert distinct_card [where xs = "[obj\<leftarrow>obj_ids . cnode_or_tcb_at obj spec]"], simp)
  apply (clarsimp simp: valid_boot_info_def si_final_objects_def
                        sep_conj_exists sep_conj_assoc)
  apply (subst ex_conj_increase)+
  apply (rule hoare_ex_pre)+
  apply (rule hoare_grab_asm)+
  apply (rule hoare_strengthen_post)
  apply (wp small_one [where obj_ids=obj_ids and R=R],
        (assumption|simp add: unat_less_2_si_cnode_size')+)

  apply clarsimp
  apply (rule_tac x=t in exI)
  apply (clarsimp)
  apply (clarsimp simp: si_objects_extra_caps_def si_caps_at_def
                        sep_conj_exists sep_conj_assoc)
  apply (rule_tac x="(map_of (zip [obj\<leftarrow>obj_ids . cnode_or_tcb_at obj spec] (drop (length obj_ids) [fstart .e. fend - 1])))" in exI)
  apply (rule_tac x="[x .e. xa - 1]" in exI)
  apply (rule_tac x="[fstart .e. fend - 1]" in exI)
  apply (rule_tac x=untyped_capsa in exI)
  apply (rule_tac x=all_available_ids in exI)
  apply (clarsimp simp: sep_conj_ac)
  done

definition injective :: "('a \<Rightarrow> 'b option) \<Rightarrow> bool"
where "injective f \<equiv> inj_on f (dom f)"

lemma sys_init_paper:
  "\<lbrakk>well_formed spec; set obj_ids = dom (cdl_objects spec); distinct obj_ids\<rbrakk> \<Longrightarrow>
   \<lbrace>\<guillemotleft>valid_boot_info bootinfo spec \<and>* R\<guillemotright>\<rbrace>
   init_system spec bootinfo obj_ids
  \<lbrace>\<lambda>_ s. \<exists>\<phi>.
    \<guillemotleft>objects_initialised spec \<phi> {obj_id. real_object_at obj_id spec} \<and>*
     irqs_initialised spec \<phi> (used_irqs spec) \<and>*
     si_final_objects spec \<phi> \<and>* R\<guillemotright> s \<and>
     injective \<phi> \<and> dom \<phi> = set obj_ids\<rbrace>"
  apply (rule hoare_strengthen_post)
  apply (fact sys_init)
  apply (fastforce simp: injective_def)
  done

end
