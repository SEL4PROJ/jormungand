(*
 * Copyright 2014, General Dynamics C4 Systems
 *
 * This software may be distributed and modified according to the terms of
 * the GNU General Public License version 2. Note that NO WARRANTY is provided.
 * See "LICENSE_GPLv2.txt" for details.
 *
 * @TAG(GD_GPL)
 *)

chapter "Retyping Objects"

theory ArchVSpaceDecls_H
imports ArchRetypeDecls_H "../InvocationLabels_H"
begin
context Arch begin global_naming ARM_H

#INCLUDE_HASKELL_PREPARSE SEL4/Object/Structures.lhs CONTEXT ARM_H
#INCLUDE_HASKELL SEL4/Kernel/VSpace/ARM.lhs CONTEXT ARM_H decls_only ArchInv=

end
end
