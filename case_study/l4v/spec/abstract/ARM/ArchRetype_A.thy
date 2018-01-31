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
Retyping and untyped invocation
*)

chapter "Retyping and Untyped Invocations"

theory ArchRetype_A
imports
  ArchVSpaceAcc_A
  ArchInvocation_A
begin

context Arch begin global_naming ARM_A

text {* This is a placeholder function. We may wish to extend the specification
  with explicitly tagging kernel data regions in memory. *}
definition
  reserve_region :: "obj_ref \<Rightarrow> nat \<Rightarrow> bool \<Rightarrow> (unit,'z::state_ext) s_monad" where
  "reserve_region ptr byteLength is_kernel \<equiv> return ()"

text {* Initialise architecture-specific objects. *}

definition
  init_arch_objects :: "apiobject_type \<Rightarrow> obj_ref \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> obj_ref list \<Rightarrow> (unit,'z::state_ext) s_monad"
where
  "init_arch_objects new_type ptr num_objects obj_sz refs
    \<equiv> if new_type = ArchObject PageDirectoryObj then (do
      mapM_x copy_global_mappings refs;
      do_machine_op $ mapM_x (\<lambda>x. cleanCacheRange_PoU x (x + ((1::word32) << pd_bits) - 1)
                                                      (addrFromPPtr x)) refs
    od) else return ()"

definition
  empty_context :: user_context where
  "empty_context \<equiv> \<lambda>_. 0"

definition init_arch_tcb :: arch_tcb where
  "init_arch_tcb \<equiv> \<lparr> tcb_context = empty_context \<rparr>"


end

end
