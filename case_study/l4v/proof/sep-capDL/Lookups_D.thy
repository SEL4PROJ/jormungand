(*
 * Copyright 2014, NICTA
 *
 * This software may be distributed and modified according to the terms of
 * the GNU General Public License version 2. Note that NO WARRANTY is provided.
 * See "LICENSE_GPLv2.txt" for details.
 *
 * @TAG(NICTA_GPL)
 *)

theory Lookups_D
imports
  "../../spec/capDL/Syscall_D"
  "../../lib/Monad_WP/OptionMonadND"
begin

type_synonym 'a lookup = "cdl_state \<Rightarrow> 'a option"

definition
  opt_cnode :: "cdl_object_id \<Rightarrow> cdl_cnode lookup"
where
  "opt_cnode p \<equiv> DO
      t \<leftarrow> opt_object p;
      case t of
        CNode cnode \<Rightarrow> oreturn cnode
      | _ \<Rightarrow> ofail
   OD"

function resolve_cap ::
  "cdl_cap \<Rightarrow> cdl_cptr \<Rightarrow> nat \<Rightarrow> (cdl_fault_error + cdl_cap_ref \<times> nat) lookup"
where
  "resolve_cap cnode_cap cap_ptr remaining_size =
  (if is_cnode_cap cnode_cap
  then DO
    (* Fetch the next level CNode. *)
    cnode \<leftarrow> opt_cnode $ cap_object cnode_cap;
    radix_size \<leftarrow> oreturn $ cdl_cnode_size_bits cnode;
    guard_size \<leftarrow> oreturn $ cap_guard_size cnode_cap;
    cap_guard  \<leftarrow> oreturn $ cap_guard cnode_cap;
    level_size \<leftarrow> oreturn (radix_size + guard_size);
    oassert (level_size \<noteq> 0);

    (* Ensure the guard matches up. *)
    guard \<leftarrow> oreturn $ (cap_ptr >> (remaining_size-guard_size)) && (mask guard_size);
    if \<not>(guard_size \<le> remaining_size \<and> guard = cap_guard) \<or>
       level_size > remaining_size
    then othrow FaultError
    else DO
      (* Find the next slot. *)
      offset \<leftarrow> oreturn $ (cap_ptr >> (remaining_size-level_size)) && (mask radix_size);
      slot \<leftarrow> oreturn (cap_object cnode_cap, unat offset);
      size_left \<leftarrow> oreturn (remaining_size - level_size);
      if size_left = 0 then
        oreturnOk (slot, 0)
      else DO
        next_cap \<leftarrow> opt_cap slot;
        if is_cnode_cap next_cap then
          resolve_cap next_cap cap_ptr size_left
        else
          oreturnOk (slot, size_left)
      OD
    OD
  OD
  else othrow FaultError)"
  by auto

termination
  by (relation "measure (\<lambda>(a,b,c). c)") auto

declare resolve_cap.simps [simp del]

declare resolve_address_bits.simps [simp del]

lemma throwError_FaultError [simp]:
  "throwError FaultError = throw"
  apply (cases "undefined::cdl_fault_error")
  apply simp
  done

lemma gets_the_get_cnode:
  "gets_the (opt_cnode r) = get_cnode r"
  apply (simp add: get_cnode_def opt_cnode_def)
  apply (rule bind_cong, rule refl)
  apply (clarsimp split: cdl_object.splits)
  done

lemma gets_the_resolve_cap:
  "gets_the (resolve_cap cnode_cap cap_ptr remaining_size) =
   resolve_address_bits cnode_cap cap_ptr remaining_size"
  apply (induct cnode_cap cap_ptr remaining_size rule: resolve_cap.induct [simplified])
  apply (subst resolve_cap.simps)
  apply (subst resolve_address_bits.simps)
  apply (clarsimp simp: unlessE_def liftE_bindE assertE_liftE gets_the_get_cnode)
  apply (rule bind_cong, rule refl)
  apply (rule bind_apply_cong, rule refl)
  apply (clarsimp simp: liftE_bindE)
  apply (rule bind_apply_cong, rule refl)
  apply (clarsimp simp: in_monad gets_the_get_cnode [symmetric])
  done

definition resolve_address_bits' ::
  "cdl_cap \<Rightarrow> cdl_cptr \<Rightarrow> nat \<Rightarrow> (cdl_cap_ref \<times> nat) lookup"
where
  "resolve_address_bits' cap cptr n \<equiv> odrop $  resolve_cap cap cptr n"



definition
  lookup_slot' :: "cdl_object_id \<Rightarrow> cdl_cptr \<Rightarrow> cdl_cap_ref lookup"
where
  "lookup_slot' thread cptr \<equiv>
    DO
      cspace_root \<leftarrow> opt_cap (thread, tcb_cspace_slot);
      (slot, _) \<leftarrow> resolve_address_bits' cspace_root cptr word_bits;
      oreturn slot
    OD"

definition
  lookup_cap' :: "cdl_object_id \<Rightarrow> cdl_cptr \<Rightarrow> cdl_cap lookup"
where
  "lookup_cap' thread cptr \<equiv>
    DO
      slot \<leftarrow> lookup_slot' thread cptr;
      opt_cap slot
    OD"

definition
  lookup_cap_and_slot' :: "cdl_object_id \<Rightarrow> cdl_cptr \<Rightarrow> (cdl_cap \<times> cdl_cap_ref) lookup"
where
  "lookup_cap_and_slot' thread cptr \<equiv>
    DO
      slot \<leftarrow> lookup_slot' thread cptr;
      cap \<leftarrow> opt_cap slot;
      oreturn (cap, slot)
    OD"

definition
  lookup_object :: "cdl_object_id \<Rightarrow> cdl_cptr \<Rightarrow> cdl_object_id lookup"
where
  "lookup_object thread cptr \<equiv>
    DO
      cap \<leftarrow> lookup_cap' thread cptr;
      oreturn $ cap_object cap
    OD"

definition
  lookup_extra_caps' :: "cdl_object_id \<Rightarrow> cdl_cptr list \<Rightarrow> (cdl_cap \<times> cdl_cap_ref) list lookup"
where
  "lookup_extra_caps' thread cptrs \<equiv>
     omap (\<lambda>cptr. lookup_cap_and_slot' thread cptr) cptrs"

end
