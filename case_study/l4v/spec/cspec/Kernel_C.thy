(*
 * Copyright 2014, General Dynamics C4 Systems
 *
 * This software may be distributed and modified according to the terms of
 * the GNU General Public License version 2. Note that NO WARRANTY is provided.
 * See "LICENSE_GPLv2.txt" for details.
 *
 * @TAG(GD_GPL)
 *)

theory Kernel_C
imports
  "../machine/$L4V_ARCH/MachineTypes"
  "../../lib/CTranslationNICTA"
  "../../tools/asmrefine/CommonOps"
begin

declare Char_eq_Char_iff [simp del]

context begin interpretation Arch .

requalify_types
  machine_state

end

declare [[populate_globals=true]]

context begin interpretation Arch . (*FIXME: arch_split*)

type_synonym cghost_state = "(machine_word \<rightharpoonup> vmpage_size) * (machine_word \<rightharpoonup> nat)
    * ghost_assertions"

definition
  gs_clear_region :: "word32 \<Rightarrow> nat \<Rightarrow> cghost_state \<Rightarrow> cghost_state" where
  "gs_clear_region ptr bits gs \<equiv>
   (%x. if x \<in> {ptr..+2 ^ bits} then None else fst gs x,
    %x. if x \<in> {ptr..+2 ^ bits} then None else fst (snd gs) x, snd (snd gs))"

definition
  gs_new_frames:: "vmpage_size \<Rightarrow> word32 \<Rightarrow> nat \<Rightarrow> cghost_state \<Rightarrow> cghost_state"
  where
  "gs_new_frames sz ptr bits \<equiv> \<lambda>gs.
   if bits < pageBitsForSize sz then gs
   else (\<lambda>x. if \<exists>n\<le>mask (bits - pageBitsForSize sz).
                  x = ptr + n * 2 ^ pageBitsForSize sz then Some sz
             else fst gs x, snd gs)"

definition
  gs_new_cnodes:: "nat \<Rightarrow> word32 \<Rightarrow> nat \<Rightarrow> cghost_state \<Rightarrow> cghost_state"
  where
  "gs_new_cnodes sz ptr bits \<equiv> \<lambda>gs.
   if bits < sz + 4 then gs
   else (fst gs, \<lambda>x. if \<exists>n\<le>mask (bits - sz - 4). x = ptr + n * 2 ^ (sz + 4)
                     then Some sz
                     else fst (snd gs) x, snd (snd gs))"

abbreviation
  gs_get_assn :: "int \<Rightarrow> cghost_state \<Rightarrow> word32"
  where
  "gs_get_assn k \<equiv> ghost_assertion_data_get k (snd o snd)"

abbreviation
  gs_set_assn :: "int \<Rightarrow> word32 \<Rightarrow> cghost_state \<Rightarrow> cghost_state"
  where
  "gs_set_assn k v \<equiv> ghost_assertion_data_set k v (apsnd o apsnd)"

declare [[record_codegen = false]]
declare [[allow_underscore_idents = true]]

end

(* workaround for the fact that the C parser wants to know the vmpage sizes*)

(* create appropriately qualified aliases *)
context begin interpretation Arch . global_naming vmpage_size

requalify_consts ARMSmallPage ARMLargePage ARMSection ARMSuperSection

end

install_C_file "c/kernel_all.c_pp"
  [machinety=machine_state, ghostty=cghost_state]

(* hide them again *)

hide_const 
 vmpage_size.ARMSmallPage 
 vmpage_size.ARMLargePage 
 vmpage_size.ARMSection 
 vmpage_size.ARMSuperSection

(* re-allow fully qualified accesses (for consistency). Slightly clunky *)

context Arch begin 

global_naming "ARM.vmpage_size"
requalify_consts ARMSmallPage ARMLargePage ARMSection ARMSuperSection

global_naming ARM
requalify_consts ARMSmallPage ARMLargePage ARMSection ARMSuperSection
end


end
