%
% Copyright 2014, General Dynamics C4 Systems
%
% This software may be distributed and modified according to the terms of
% the GNU General Public License version 2. Note that NO WARRANTY is provided.
% See "LICENSE_GPLv2.txt" for details.
%
% @TAG(GD_GPL)
%

This module contains operations on machine-specific object types for the ARM.

> module SEL4.Object.ObjectType.ARM where

\begin{impdetails}

> import SEL4.Machine.RegisterSet
> import SEL4.Machine.Hardware.ARM
> import SEL4.Model
> import SEL4.API.Types
> import SEL4.API.Failures
> import SEL4.API.Invocation.ARM as ArchInv
> import SEL4.Object.Structures
> import SEL4.Kernel.VSpace.ARM

> import Data.Bits

\end{impdetails}

The ARM-specific types and structures are qualified with the "Arch.Types" and "Arch.Structures" prefixes, respectively. This is to avoid namespace conflicts with the platform-independent modules.

> import qualified SEL4.API.Types.ARM as Arch.Types

\subsection{Copying and Mutating Capabilities}

> deriveCap :: PPtr CTE -> ArchCapability -> KernelF SyscallError ArchCapability

It is not possible to copy a page table or page directory capability unless it has been mapped.

> deriveCap _ (c@PageTableCap { capPTMappedAddress = Just _ }) = return c
> deriveCap _ (PageTableCap { capPTMappedAddress = Nothing })
>     = throw IllegalOperation
> deriveCap _ (c@PageDirectoryCap { capPDMappedASID = Just _ }) = return c
> deriveCap _ (PageDirectoryCap { capPDMappedASID = Nothing })
>     = throw IllegalOperation

Page capabilities are copied without their mapping information, to allow them to be mapped in multiple locations.

> deriveCap _ (c@PageCap {}) = return $ c { capVPMappedAddress = Nothing }

ASID capabilities can be copied without modification.

> deriveCap _ c@ASIDControlCap = return c
> deriveCap _ (c@ASIDPoolCap {}) = return c

None of the ARM-specific capabilities have a user writeable data word.

> updateCapData :: Bool -> Word -> ArchCapability -> Capability
> updateCapData _ _ cap = ArchObjectCap cap

Page capabilities have read and write permission bits, which are used to restrict virtual memory accesses to their contents. Note that the ability to map objects into a page table or page directory is granted by possession of a capability to it; there is no specific permission bit restricting this ability.

> maskCapRights :: CapRights -> ArchCapability -> Capability
> maskCapRights r c@(PageCap {}) = ArchObjectCap $ c {
>     capVPRights = maskVMRights (capVPRights c) r }
> maskCapRights _ c = ArchObjectCap c

\subsection{Deleting Capabilities}

> finaliseCap :: ArchCapability -> Bool -> Kernel Capability

Deletion of a final capability to an ASID pool requires that the pool is removed from the global ASID table.

> finaliseCap (ASIDPoolCap { capASIDBase = b, capASIDPool = ptr }) True = do
>     deleteASIDPool b ptr
>     return NullCap

Deletion of a final capability to a page directory with an assigned ASID requires the ASID assignment to be removed, and the ASID flushed from the caches.

> finaliseCap (PageDirectoryCap {
>         capPDMappedASID = Just a,
>         capPDBasePtr = ptr }) True = do
>     deleteASID a ptr
>     return NullCap

Deletion of a final capability to a page table that has been mapped requires that the mapping be removed from the page directory, and the corresponding addresses flushed from the caches.

> finaliseCap (PageTableCap {
>         capPTMappedAddress = Just (a, v),
>         capPTBasePtr = ptr }) True = do
>     unmapPageTable a v ptr
>     return NullCap

Deletion of any mapped frame capability requires the page table slot to be located and cleared, and the unmapped address to be flushed from the caches.

> finaliseCap (PageCap { capVPMappedAddress = Just (a, v),
>                        capVPSize = s, capVPBasePtr = ptr }) _
>     = do
>         unmapPage s a v ptr
>         return NullCap

All other capabilities need no finalisation action.

> finaliseCap _ _ = return NullCap


\subsection{Identifying Capabilities}

> sameRegionAs :: ArchCapability -> ArchCapability -> Bool
> sameRegionAs (a@PageCap {}) (b@PageCap {}) =
>     (botA <= botB) && (topA >= topB) && (botB <= topB)
>     where
>         botA = capVPBasePtr a
>         botB = capVPBasePtr b
>         topA = botA + bit (pageBitsForSize $ capVPSize a) - 1
>         topB = botB + bit (pageBitsForSize $ capVPSize b) - 1
> sameRegionAs (a@PageTableCap {}) (b@PageTableCap {}) =
>     capPTBasePtr a == capPTBasePtr b
> sameRegionAs (a@PageDirectoryCap {}) (b@PageDirectoryCap {}) =
>     capPDBasePtr a == capPDBasePtr b
> sameRegionAs ASIDControlCap ASIDControlCap = True
> sameRegionAs (a@ASIDPoolCap {}) (b@ASIDPoolCap {}) =
>     capASIDPool a == capASIDPool b
> sameRegionAs _ _ = False

> isPhysicalCap :: ArchCapability -> Bool
> isPhysicalCap ASIDControlCap = False
> isPhysicalCap _ = True

> sameObjectAs :: ArchCapability -> ArchCapability -> Bool
> sameObjectAs (a@PageCap { capVPBasePtr = ptrA }) (b@PageCap {}) =
>     (ptrA == capVPBasePtr b) && (capVPSize a == capVPSize b)
>         && (ptrA <= ptrA + bit (pageBitsForSize $ capVPSize a) - 1)
>         && (capVPIsDevice a == capVPIsDevice b)
> sameObjectAs a b = sameRegionAs a b

\subsection{Creating New Capabilities}

Create an architecture-specific object.

> placeNewDataObject :: PPtr () -> Int -> Bool -> Kernel ()
> placeNewDataObject regionBase sz isDevice = if isDevice
>     then placeNewObject regionBase UserDataDevice sz
>     else placeNewObject regionBase UserData sz

> createObject :: ObjectType -> PPtr () -> Int -> Bool -> Kernel ArchCapability
> createObject t regionBase _ isDevice =
>     let funupd = (\f x v y -> if y == x then v else f y) in
>     let pointerCast = PPtr . fromPPtr
>     in case t of
>         Arch.Types.APIObjectType _ ->
>             fail "Arch.createObject got an API type"
>         Arch.Types.SmallPageObject -> do
>             placeNewDataObject regionBase 0 isDevice
>             modify (\ks -> ks { gsUserPages =
>               funupd (gsUserPages ks)
>                      (fromPPtr regionBase) (Just ARMSmallPage)})
>             return $! PageCap isDevice (pointerCast regionBase)
>                   VMReadWrite ARMSmallPage Nothing
>         Arch.Types.LargePageObject -> do
>             placeNewDataObject regionBase 4 isDevice
>             modify (\ks -> ks { gsUserPages =
>               funupd (gsUserPages ks)
>                      (fromPPtr regionBase) (Just ARMLargePage)})
>             return $! PageCap isDevice (pointerCast regionBase)
>                   VMReadWrite ARMLargePage Nothing
>         Arch.Types.SectionObject -> do
>             placeNewDataObject regionBase 8 isDevice
>             modify (\ks -> ks { gsUserPages =
>               funupd (gsUserPages ks)
>                      (fromPPtr regionBase) (Just ARMSection)})
>             return $! PageCap isDevice (pointerCast regionBase)
>                   VMReadWrite ARMSection Nothing
>         Arch.Types.SuperSectionObject -> do
>             placeNewDataObject regionBase 12 isDevice
>             modify (\ks -> ks { gsUserPages =
>               funupd (gsUserPages ks)
>                      (fromPPtr regionBase) (Just ARMSuperSection)})
>             return $! PageCap isDevice (pointerCast regionBase)
>                   VMReadWrite ARMSuperSection Nothing
>         Arch.Types.PageTableObject -> do
>             let ptSize = ptBits - objBits (makeObject :: PTE)
>             placeNewObject regionBase (makeObject :: PTE) ptSize
>             return $! PageTableCap (pointerCast regionBase) Nothing
>         Arch.Types.PageDirectoryObject -> do
>             let pdSize = pdBits - objBits (makeObject :: PDE)
>             let regionSize = (1 `shiftL` pdBits)
>             placeNewObject regionBase (makeObject :: PDE) pdSize
>             copyGlobalMappings (pointerCast regionBase)
>             doMachineOp $
>                 cleanCacheRange_PoU (VPtr $ fromPPtr regionBase)
>                       (VPtr $ fromPPtr regionBase + regionSize - 1)
>                       (addrFromPPtr regionBase)
>             return $! PageDirectoryCap (pointerCast regionBase) Nothing

\subsection{Capability Invocation}

> decodeInvocation :: Word -> [Word] -> CPtr -> PPtr CTE ->
>         ArchCapability -> [(Capability, PPtr CTE)] ->
>         KernelF SyscallError ArchInv.Invocation
> decodeInvocation = decodeARMMMUInvocation

> performInvocation :: ArchInv.Invocation -> KernelP [Word]
> performInvocation = performARMMMUInvocation

\subsection{Helper Functions}

> capUntypedPtr :: ArchCapability -> PPtr ()
> capUntypedPtr (PageCap { capVPBasePtr = PPtr p }) = PPtr p
> capUntypedPtr (PageTableCap { capPTBasePtr = PPtr p }) = PPtr p
> capUntypedPtr (PageDirectoryCap { capPDBasePtr = PPtr p }) = PPtr p
> capUntypedPtr ASIDControlCap = error "ASID control has no pointer"
> capUntypedPtr (ASIDPoolCap { capASIDPool = PPtr p }) = PPtr p

> capUntypedSize :: ArchCapability -> Word
> capUntypedSize (PageCap {capVPSize = sz}) = 1 `shiftL` pageBitsForSize sz
> capUntypedSize (PageTableCap {}) = 1 `shiftL` 10
> capUntypedSize (PageDirectoryCap {}) = 1 `shiftL` 14
> capUntypedSize (ASIDControlCap {}) = 1 `shiftL` (asidHighBits + 2)
> capUntypedSize (ASIDPoolCap {}) = 1 `shiftL` (asidLowBits + 2)


No arch-specific thread deletion operations needed on ARM platform.

> prepareThreadDelete :: PPtr TCB -> Kernel ()
> prepareThreadDelete _ = return ()


