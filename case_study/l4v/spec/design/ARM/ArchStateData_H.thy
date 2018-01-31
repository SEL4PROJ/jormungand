(* THIS FILE WAS AUTOMATICALLY GENERATED. DO NOT EDIT. *)
(* instead, see the skeleton file ArchStateData_H.thy *)
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
	Kernel state and kernel monads, imports everything that SEL4.Model needs.
*)

chapter "Architecture Specific Kernel State and Monads"

theory ArchStateData_H
imports
  Arch_Structs_B
  ArchTypes_H
  ArchStructures_H
begin
context Arch begin global_naming ARM_H

datatype kernel_state =
    ARMKernelState "asid \<Rightarrow> ((machine_word) option)" "hardware_asid \<Rightarrow> (asid option)" hardware_asid "asid \<Rightarrow> ((hardware_asid * machine_word) option)" machine_word "machine_word list" "machine_word \<Rightarrow> arm_vspace_region_use"

primrec
  armKSKernelVSpace :: "kernel_state \<Rightarrow> machine_word \<Rightarrow> arm_vspace_region_use"
where
  "armKSKernelVSpace (ARMKernelState v0 v1 v2 v3 v4 v5 v6) = v6"

primrec
  armKSASIDTable :: "kernel_state \<Rightarrow> asid \<Rightarrow> ((machine_word) option)"
where
  "armKSASIDTable (ARMKernelState v0 v1 v2 v3 v4 v5 v6) = v0"

primrec
  armKSGlobalPD :: "kernel_state \<Rightarrow> machine_word"
where
  "armKSGlobalPD (ARMKernelState v0 v1 v2 v3 v4 v5 v6) = v4"

primrec
  armKSHWASIDTable :: "kernel_state \<Rightarrow> hardware_asid \<Rightarrow> (asid option)"
where
  "armKSHWASIDTable (ARMKernelState v0 v1 v2 v3 v4 v5 v6) = v1"

primrec
  armKSGlobalPTs :: "kernel_state \<Rightarrow> machine_word list"
where
  "armKSGlobalPTs (ARMKernelState v0 v1 v2 v3 v4 v5 v6) = v5"

primrec
  armKSNextASID :: "kernel_state \<Rightarrow> hardware_asid"
where
  "armKSNextASID (ARMKernelState v0 v1 v2 v3 v4 v5 v6) = v2"

primrec
  armKSASIDMap :: "kernel_state \<Rightarrow> asid \<Rightarrow> ((hardware_asid * machine_word) option)"
where
  "armKSASIDMap (ARMKernelState v0 v1 v2 v3 v4 v5 v6) = v3"

primrec
  armKSKernelVSpace_update :: "((machine_word \<Rightarrow> arm_vspace_region_use) \<Rightarrow> (machine_word \<Rightarrow> arm_vspace_region_use)) \<Rightarrow> kernel_state \<Rightarrow> kernel_state"
where
  "armKSKernelVSpace_update f (ARMKernelState v0 v1 v2 v3 v4 v5 v6) = ARMKernelState v0 v1 v2 v3 v4 v5 (f v6)"

primrec
  armKSASIDTable_update :: "((asid \<Rightarrow> ((machine_word) option)) \<Rightarrow> (asid \<Rightarrow> ((machine_word) option))) \<Rightarrow> kernel_state \<Rightarrow> kernel_state"
where
  "armKSASIDTable_update f (ARMKernelState v0 v1 v2 v3 v4 v5 v6) = ARMKernelState (f v0) v1 v2 v3 v4 v5 v6"

primrec
  armKSGlobalPD_update :: "(machine_word \<Rightarrow> machine_word) \<Rightarrow> kernel_state \<Rightarrow> kernel_state"
where
  "armKSGlobalPD_update f (ARMKernelState v0 v1 v2 v3 v4 v5 v6) = ARMKernelState v0 v1 v2 v3 (f v4) v5 v6"

primrec
  armKSHWASIDTable_update :: "((hardware_asid \<Rightarrow> (asid option)) \<Rightarrow> (hardware_asid \<Rightarrow> (asid option))) \<Rightarrow> kernel_state \<Rightarrow> kernel_state"
where
  "armKSHWASIDTable_update f (ARMKernelState v0 v1 v2 v3 v4 v5 v6) = ARMKernelState v0 (f v1) v2 v3 v4 v5 v6"

primrec
  armKSGlobalPTs_update :: "((machine_word list) \<Rightarrow> (machine_word list)) \<Rightarrow> kernel_state \<Rightarrow> kernel_state"
where
  "armKSGlobalPTs_update f (ARMKernelState v0 v1 v2 v3 v4 v5 v6) = ARMKernelState v0 v1 v2 v3 v4 (f v5) v6"

primrec
  armKSNextASID_update :: "(hardware_asid \<Rightarrow> hardware_asid) \<Rightarrow> kernel_state \<Rightarrow> kernel_state"
where
  "armKSNextASID_update f (ARMKernelState v0 v1 v2 v3 v4 v5 v6) = ARMKernelState v0 v1 (f v2) v3 v4 v5 v6"

primrec
  armKSASIDMap_update :: "((asid \<Rightarrow> ((hardware_asid * machine_word) option)) \<Rightarrow> (asid \<Rightarrow> ((hardware_asid * machine_word) option))) \<Rightarrow> kernel_state \<Rightarrow> kernel_state"
where
  "armKSASIDMap_update f (ARMKernelState v0 v1 v2 v3 v4 v5 v6) = ARMKernelState v0 v1 v2 (f v3) v4 v5 v6"

abbreviation (input)
  ARMKernelState_trans :: "(asid \<Rightarrow> ((machine_word) option)) \<Rightarrow> (hardware_asid \<Rightarrow> (asid option)) \<Rightarrow> (hardware_asid) \<Rightarrow> (asid \<Rightarrow> ((hardware_asid * machine_word) option)) \<Rightarrow> (machine_word) \<Rightarrow> (machine_word list) \<Rightarrow> (machine_word \<Rightarrow> arm_vspace_region_use) \<Rightarrow> kernel_state" ("ARMKernelState'_ \<lparr> armKSASIDTable= _, armKSHWASIDTable= _, armKSNextASID= _, armKSASIDMap= _, armKSGlobalPD= _, armKSGlobalPTs= _, armKSKernelVSpace= _ \<rparr>")
where
  "ARMKernelState_ \<lparr> armKSASIDTable= v0, armKSHWASIDTable= v1, armKSNextASID= v2, armKSASIDMap= v3, armKSGlobalPD= v4, armKSGlobalPTs= v5, armKSKernelVSpace= v6 \<rparr> == ARMKernelState v0 v1 v2 v3 v4 v5 v6"

lemma armKSKernelVSpace_armKSKernelVSpace_update [simp]:
  "armKSKernelVSpace (armKSKernelVSpace_update f v) = f (armKSKernelVSpace v)"
  by (cases v) simp

lemma armKSKernelVSpace_armKSASIDTable_update [simp]:
  "armKSKernelVSpace (armKSASIDTable_update f v) = armKSKernelVSpace v"
  by (cases v) simp

lemma armKSKernelVSpace_armKSGlobalPD_update [simp]:
  "armKSKernelVSpace (armKSGlobalPD_update f v) = armKSKernelVSpace v"
  by (cases v) simp

lemma armKSKernelVSpace_armKSHWASIDTable_update [simp]:
  "armKSKernelVSpace (armKSHWASIDTable_update f v) = armKSKernelVSpace v"
  by (cases v) simp

lemma armKSKernelVSpace_armKSGlobalPTs_update [simp]:
  "armKSKernelVSpace (armKSGlobalPTs_update f v) = armKSKernelVSpace v"
  by (cases v) simp

lemma armKSKernelVSpace_armKSNextASID_update [simp]:
  "armKSKernelVSpace (armKSNextASID_update f v) = armKSKernelVSpace v"
  by (cases v) simp

lemma armKSKernelVSpace_armKSASIDMap_update [simp]:
  "armKSKernelVSpace (armKSASIDMap_update f v) = armKSKernelVSpace v"
  by (cases v) simp

lemma armKSASIDTable_armKSKernelVSpace_update [simp]:
  "armKSASIDTable (armKSKernelVSpace_update f v) = armKSASIDTable v"
  by (cases v) simp

lemma armKSASIDTable_armKSASIDTable_update [simp]:
  "armKSASIDTable (armKSASIDTable_update f v) = f (armKSASIDTable v)"
  by (cases v) simp

lemma armKSASIDTable_armKSGlobalPD_update [simp]:
  "armKSASIDTable (armKSGlobalPD_update f v) = armKSASIDTable v"
  by (cases v) simp

lemma armKSASIDTable_armKSHWASIDTable_update [simp]:
  "armKSASIDTable (armKSHWASIDTable_update f v) = armKSASIDTable v"
  by (cases v) simp

lemma armKSASIDTable_armKSGlobalPTs_update [simp]:
  "armKSASIDTable (armKSGlobalPTs_update f v) = armKSASIDTable v"
  by (cases v) simp

lemma armKSASIDTable_armKSNextASID_update [simp]:
  "armKSASIDTable (armKSNextASID_update f v) = armKSASIDTable v"
  by (cases v) simp

lemma armKSASIDTable_armKSASIDMap_update [simp]:
  "armKSASIDTable (armKSASIDMap_update f v) = armKSASIDTable v"
  by (cases v) simp

lemma armKSGlobalPD_armKSKernelVSpace_update [simp]:
  "armKSGlobalPD (armKSKernelVSpace_update f v) = armKSGlobalPD v"
  by (cases v) simp

lemma armKSGlobalPD_armKSASIDTable_update [simp]:
  "armKSGlobalPD (armKSASIDTable_update f v) = armKSGlobalPD v"
  by (cases v) simp

lemma armKSGlobalPD_armKSGlobalPD_update [simp]:
  "armKSGlobalPD (armKSGlobalPD_update f v) = f (armKSGlobalPD v)"
  by (cases v) simp

lemma armKSGlobalPD_armKSHWASIDTable_update [simp]:
  "armKSGlobalPD (armKSHWASIDTable_update f v) = armKSGlobalPD v"
  by (cases v) simp

lemma armKSGlobalPD_armKSGlobalPTs_update [simp]:
  "armKSGlobalPD (armKSGlobalPTs_update f v) = armKSGlobalPD v"
  by (cases v) simp

lemma armKSGlobalPD_armKSNextASID_update [simp]:
  "armKSGlobalPD (armKSNextASID_update f v) = armKSGlobalPD v"
  by (cases v) simp

lemma armKSGlobalPD_armKSASIDMap_update [simp]:
  "armKSGlobalPD (armKSASIDMap_update f v) = armKSGlobalPD v"
  by (cases v) simp

lemma armKSHWASIDTable_armKSKernelVSpace_update [simp]:
  "armKSHWASIDTable (armKSKernelVSpace_update f v) = armKSHWASIDTable v"
  by (cases v) simp

lemma armKSHWASIDTable_armKSASIDTable_update [simp]:
  "armKSHWASIDTable (armKSASIDTable_update f v) = armKSHWASIDTable v"
  by (cases v) simp

lemma armKSHWASIDTable_armKSGlobalPD_update [simp]:
  "armKSHWASIDTable (armKSGlobalPD_update f v) = armKSHWASIDTable v"
  by (cases v) simp

lemma armKSHWASIDTable_armKSHWASIDTable_update [simp]:
  "armKSHWASIDTable (armKSHWASIDTable_update f v) = f (armKSHWASIDTable v)"
  by (cases v) simp

lemma armKSHWASIDTable_armKSGlobalPTs_update [simp]:
  "armKSHWASIDTable (armKSGlobalPTs_update f v) = armKSHWASIDTable v"
  by (cases v) simp

lemma armKSHWASIDTable_armKSNextASID_update [simp]:
  "armKSHWASIDTable (armKSNextASID_update f v) = armKSHWASIDTable v"
  by (cases v) simp

lemma armKSHWASIDTable_armKSASIDMap_update [simp]:
  "armKSHWASIDTable (armKSASIDMap_update f v) = armKSHWASIDTable v"
  by (cases v) simp

lemma armKSGlobalPTs_armKSKernelVSpace_update [simp]:
  "armKSGlobalPTs (armKSKernelVSpace_update f v) = armKSGlobalPTs v"
  by (cases v) simp

lemma armKSGlobalPTs_armKSASIDTable_update [simp]:
  "armKSGlobalPTs (armKSASIDTable_update f v) = armKSGlobalPTs v"
  by (cases v) simp

lemma armKSGlobalPTs_armKSGlobalPD_update [simp]:
  "armKSGlobalPTs (armKSGlobalPD_update f v) = armKSGlobalPTs v"
  by (cases v) simp

lemma armKSGlobalPTs_armKSHWASIDTable_update [simp]:
  "armKSGlobalPTs (armKSHWASIDTable_update f v) = armKSGlobalPTs v"
  by (cases v) simp

lemma armKSGlobalPTs_armKSGlobalPTs_update [simp]:
  "armKSGlobalPTs (armKSGlobalPTs_update f v) = f (armKSGlobalPTs v)"
  by (cases v) simp

lemma armKSGlobalPTs_armKSNextASID_update [simp]:
  "armKSGlobalPTs (armKSNextASID_update f v) = armKSGlobalPTs v"
  by (cases v) simp

lemma armKSGlobalPTs_armKSASIDMap_update [simp]:
  "armKSGlobalPTs (armKSASIDMap_update f v) = armKSGlobalPTs v"
  by (cases v) simp

lemma armKSNextASID_armKSKernelVSpace_update [simp]:
  "armKSNextASID (armKSKernelVSpace_update f v) = armKSNextASID v"
  by (cases v) simp

lemma armKSNextASID_armKSASIDTable_update [simp]:
  "armKSNextASID (armKSASIDTable_update f v) = armKSNextASID v"
  by (cases v) simp

lemma armKSNextASID_armKSGlobalPD_update [simp]:
  "armKSNextASID (armKSGlobalPD_update f v) = armKSNextASID v"
  by (cases v) simp

lemma armKSNextASID_armKSHWASIDTable_update [simp]:
  "armKSNextASID (armKSHWASIDTable_update f v) = armKSNextASID v"
  by (cases v) simp

lemma armKSNextASID_armKSGlobalPTs_update [simp]:
  "armKSNextASID (armKSGlobalPTs_update f v) = armKSNextASID v"
  by (cases v) simp

lemma armKSNextASID_armKSNextASID_update [simp]:
  "armKSNextASID (armKSNextASID_update f v) = f (armKSNextASID v)"
  by (cases v) simp

lemma armKSNextASID_armKSASIDMap_update [simp]:
  "armKSNextASID (armKSASIDMap_update f v) = armKSNextASID v"
  by (cases v) simp

lemma armKSASIDMap_armKSKernelVSpace_update [simp]:
  "armKSASIDMap (armKSKernelVSpace_update f v) = armKSASIDMap v"
  by (cases v) simp

lemma armKSASIDMap_armKSASIDTable_update [simp]:
  "armKSASIDMap (armKSASIDTable_update f v) = armKSASIDMap v"
  by (cases v) simp

lemma armKSASIDMap_armKSGlobalPD_update [simp]:
  "armKSASIDMap (armKSGlobalPD_update f v) = armKSASIDMap v"
  by (cases v) simp

lemma armKSASIDMap_armKSHWASIDTable_update [simp]:
  "armKSASIDMap (armKSHWASIDTable_update f v) = armKSASIDMap v"
  by (cases v) simp

lemma armKSASIDMap_armKSGlobalPTs_update [simp]:
  "armKSASIDMap (armKSGlobalPTs_update f v) = armKSASIDMap v"
  by (cases v) simp

lemma armKSASIDMap_armKSNextASID_update [simp]:
  "armKSASIDMap (armKSNextASID_update f v) = armKSASIDMap v"
  by (cases v) simp

lemma armKSASIDMap_armKSASIDMap_update [simp]:
  "armKSASIDMap (armKSASIDMap_update f v) = f (armKSASIDMap v)"
  by (cases v) simp

definition
newKernelState :: "paddr \<Rightarrow> (kernel_state * paddr list)"
where
"newKernelState data_start \<equiv>
    let
        alignToBits = (\<lambda>  addr b. (((addr - 1) `~shiftR~` b) + 1) `~shiftL~` b);
        globalsFrame = data_start `~alignToBits~` pageBits;
        globalsFrameTop = globalsFrame + bit pageBits;
        globalPTs = globalsFrameTop `~alignToBits~` pageBits;
        globalPTsTop = globalPTs + bit pageBits;
        globalPD = globalPTsTop `~alignToBits~` pdBits;
        globalPDTop = globalPD + bit pdBits;
        frames = globalsFrame #
            [globalPTs, globalPTs + bit pageBits  .e.  globalPTsTop - 1] @
            [globalPD, globalPD + bit pageBits  .e.  globalPDTop - 1];
        state = ARMKernelState_ \<lparr>
            armKSASIDTable= funPartialArray (const Nothing) (0, (1 `~shiftL~` asidHighBits) - 1),
            armKSHWASIDTable= funArray (const Nothing),
            armKSNextASID= minBound,
            armKSASIDMap= funPartialArray (const Nothing) asidRange,
            armKSGlobalPD= ptrFromPAddr globalPD,
            armKSGlobalPTs= map ptrFromPAddr
                [globalPTs, globalPTs + bit ptBits  .e.  globalPTsTop- 1],
            armKSKernelVSpace=
                (\<lambda> vref. if vref < mask 20 then ArmVSpaceKernelWindow
                                            else ArmVSpaceInvalidRegion) \<rparr>
    in
                                   (state, frames)"


end

end
