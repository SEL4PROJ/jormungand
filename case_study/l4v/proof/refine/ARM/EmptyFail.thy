(*
 * Copyright 2014, General Dynamics C4 Systems
 *
 * This software may be distributed and modified according to the terms of
 * the GNU General Public License version 2. Note that NO WARRANTY is provided.
 * See "LICENSE_GPLv2.txt" for details.
 *
 * @TAG(GD_GPL)
 *)

theory EmptyFail
imports Bits_R
begin

(* Collect empty_fail lemmas here. naming convention is emtpy_fail_NAME. 
   Unless there is a good reason, they should all be [intro!, wp, simp] *)

lemma empty_fail_projectKO [simp, intro!]:
  "empty_fail (projectKO v)"
  unfolding empty_fail_def projectKO_def
  by (simp add: return_def fail_def split: option.splits)

lemma empty_fail_alignCheck [intro!, wp, simp]:
  "empty_fail (alignCheck a b)"
  unfolding alignCheck_def
  by (simp add: alignError_def)

lemma empty_fail_magnitudeCheck [intro!, wp, simp]:
  "empty_fail (magnitudeCheck a b c)"
  unfolding magnitudeCheck_def
  by (simp split: option.splits)  

lemma empty_fail_loadObject_default [intro!, wp, simp]:
  shows "empty_fail (loadObject_default x b c d)"
  by (auto simp: loadObject_default_def
           split: option.splits)

lemma empty_fail_threadGet [intro!, wp, simp]:
  "empty_fail (threadGet f p)"
  by (simp add: threadGet_def getObject_def split_def)

lemma empty_fail_getCTE [intro!, wp, simp]:
  "empty_fail (getCTE slot)"
  apply (simp add: getCTE_def getObject_def split_def)
  apply (intro empty_fail_bind, simp_all)
  apply (simp add: loadObject_cte typeError_def alignCheck_def alignError_def
                   magnitudeCheck_def
            split: Structures_H.kernel_object.split) 
  apply (auto split: option.split)
  done

lemma empty_fail_updateObject_cte [intro!, wp, simp]:
  "empty_fail (updateObject (v :: cte) ko a b c)"
  by (simp add: updateObject_cte typeError_def unless_def split: kernel_object.splits )

lemma empty_fail_setCTE [intro!, wp, simp]:
  "empty_fail (setCTE p cte)"
  unfolding setCTE_def
  by (simp add: setObject_def split_def)

lemma empty_fail_updateMDB [intro!, wp, simp]:
  "empty_fail (updateMDB a b)"
  unfolding updateMDB_def Let_def by auto

lemma empty_fail_getSlotCap [intro!, wp, simp]:
  "empty_fail (getSlotCap a)"
  unfolding getSlotCap_def by simp

context begin interpretation Arch . (*FIXME: arch_split*)

lemma empty_fail_getObject:
  assumes x: "(\<And>b c d. empty_fail (loadObject x b c d::'a :: pspace_storable kernel))"
  shows "empty_fail (getObject x :: 'a :: pspace_storable kernel)"
  apply (simp add: getObject_def split_def)
  apply (safe intro!: empty_fail_bind empty_fail_gets empty_fail_assert_opt)
  apply (rule x)
  done

lemma empty_fail_getObject_tcb [intro!, wp, simp]:
  shows "empty_fail (getObject x :: tcb kernel)"
  by (auto intro: empty_fail_getObject)

lemma empty_fail_updateTrackedFreeIndex [intro!, wp, simp]:
  shows "empty_fail (updateTrackedFreeIndex p idx)"
  by (simp add: updateTrackedFreeIndex_def)

lemma empty_fail_updateNewFreeIndex [intro!, wp, simp]:
  shows "empty_fail (updateNewFreeIndex p)"
  apply (simp add: updateNewFreeIndex_def)
  apply (safe intro!: empty_fail_bind)
  apply (simp split: capability.split)
  done

lemma empty_fail_insertNewCap [intro!, wp, simp]:
  "empty_fail (insertNewCap p p' cap)"
  unfolding insertNewCap_def by simp
        
lemma empty_fail_getIRQSlot [intro!, wp, simp]:
  "empty_fail (getIRQSlot irq)"
  by (simp add: getIRQSlot_def getInterruptState_def locateSlot_conv)

lemma empty_fail_getObject_ntfn [intro!, wp, simp]:
  "empty_fail (getObject p :: Structures_H.notification kernel)"
  by (simp add: empty_fail_getObject)

lemma empty_fail_getNotification [intro!, wp, simp]:
  "empty_fail (getNotification ep)"
  by (simp add: getNotification_def)

lemma empty_fail_lookupIPCBuffer [intro!, wp, simp]:
  "empty_fail (lookupIPCBuffer a b)"
  by (clarsimp simp: lookupIPCBuffer_def ARM_H.lookupIPCBuffer_def
                     Let_def getThreadBufferSlot_def locateSlot_conv
              split: capability.splits arch_capability.splits | wp | wpc)+

lemma empty_fail_updateObject_default [intro!, wp, simp]:
  "empty_fail (updateObject_default v ko a b c)"
  by (simp add: updateObject_default_def typeError_def unless_def split: kernel_object.splits )

lemma empty_fail_threadSet [intro!, wp, simp]:
  "empty_fail (threadSet f p)"
  by (simp add: threadSet_def getObject_def setObject_def split_def)

lemma empty_fail_getThreadState[iff]:
  "empty_fail (getThreadState t)"
  by (simp add: getThreadState_def)

declare empty_fail_stateAssert [wp]
declare setRegister_empty_fail [intro!, simp]

end
end
