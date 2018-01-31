(*
 * Copyright 2014, General Dynamics C4 Systems
 *
 * This software may be distributed and modified according to the terms of
 * the GNU General Public License version 2. Note that NO WARRANTY is provided.
 * See "LICENSE_GPLv2.txt" for details.
 *
 * @TAG(GD_GPL)
 *)

theory ArchInterruptDecls_H
imports "../RetypeDecls_H" "../CNode_H" 
begin

context Arch begin global_naming ARM_H

#INCLUDE_HASKELL SEL4/Object/Interrupt/ARM.lhs CONTEXT ARM_H decls_only ArchInv=

end

end
