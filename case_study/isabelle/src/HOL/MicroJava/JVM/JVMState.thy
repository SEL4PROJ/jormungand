(*  Title:      HOL/MicroJava/JVM/JVMState.thy
    Author:     Cornelia Pusch, Gerwin Klein, Technische Universitaet Muenchen
*)

chapter \<open>Java Virtual Machine \label{cha:jvm}\<close>

section \<open>State of the JVM\<close>

theory JVMState
imports "../J/Conform"
begin

subsection \<open>Frame Stack\<close>
type_synonym opstack = "val list"
type_synonym locvars = "val list"
type_synonym p_count = nat

type_synonym
 frame = "opstack \<times>     
          locvars \<times>   
          cname \<times>     
          sig \<times>     
          p_count"

  \<comment> "operand stack" 
  \<comment> "local variables (including this pointer and method parameters)"
  \<comment> "name of class where current method is defined"
  \<comment> "method name + parameter types"
  \<comment> "program counter within frame"


subsection \<open>Exceptions\<close>
definition raise_system_xcpt :: "bool \<Rightarrow> xcpt \<Rightarrow> val option" where
  "raise_system_xcpt b x \<equiv> raise_if b x None"

subsection \<open>Runtime State\<close>
type_synonym
  jvm_state = "val option \<times> aheap \<times> frame list"  \<comment> "exception flag, heap, frames"


subsection \<open>Lemmas\<close>

lemma new_Addr_OutOfMemory:
  "snd (new_Addr hp) = Some xcp \<Longrightarrow> xcp = Addr (XcptRef OutOfMemory)"
proof - 
  obtain ref xp where "new_Addr hp = (ref, xp)" by (cases "new_Addr hp")
  moreover
  assume "snd (new_Addr hp) = Some xcp" 
  ultimately
  show ?thesis by (auto dest: new_AddrD)
qed
  
end
