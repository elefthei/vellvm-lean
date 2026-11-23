import PortChecks.SourceType
import Vellvm.Semantics.Interfaces.Memory

open Vellvm Vellvm.Semantics.Interfaces.Memory
universe u v w z

private abbrev MemoryElimination := ∀ {S : Type u} {A : Type v} {P : Type} {X : Type w}
    (Q : memS S A P X → Sort z),
    (∀ x, Q (Mret x)) → (∀ msg : IRString, Q (Moom msg)) →
    (∀ msg : IRString, Q (Mub msg)) → (∀ msg : IRString, Q (Merr msg)) →
    (∀ k, (∀ s, Q (k s)) → Q (Mget k)) →
    (∀ s k, (∀ t : Unit, Q (k t)) → Q (Mput s k)) →
    (∀ c k, (∀ answer : memCType (P := P) c, Q (k answer)) → Q (Mchoose c k)) →
    ∀ m, Q m

#source_check "src/rocq/Semantics/Interfaces/Memory.v|Vellvm.Semantics.Interfaces.Memory|memS_rect"
  memS_rect : MemoryElimination.{u, v, w, z + 1}

#source_check "src/rocq/Semantics/Interfaces/Memory.v|Vellvm.Semantics.Interfaces.Memory|memS_rec"
  memS_rec : MemoryElimination.{u, v, w, 1}

#source_check "src/rocq/Semantics/Interfaces/Memory.v|Vellvm.Semantics.Interfaces.Memory|memS_ind"
  memS_ind : MemoryElimination.{u, v, w, 0}

#source_check "src/rocq/Semantics/Interfaces/Memory.v|Vellvm.Semantics.Interfaces.Memory|memS_sind"
  memS_sind : MemoryElimination.{u, v, w, 0}

#source_check "src/rocq/Semantics/Interfaces/Memory.v|Vellvm.Semantics.Interfaces.Memory|memS_mon"
  memS_mon : ∀ {S : Type u} {A : Type v} {P : Type}, Monad (memS S A P : Type w → Type (max u w))

open Vellvm.Semantics.Interfaces.Params Vellvm.Semantics.MemoryBytes
universe r

#source_check "src/rocq/Semantics/Interfaces/Memory.v|Vellvm.Semantics.Interfaces.Memory|mm_state"
  mm_state : ∀ [Pa : Params] [MemoryModelPrimitives.{u,v,w,z,r}], MemoryModelState.{u,v,w,z,r}

#source_check "src/rocq/Semantics/Interfaces/Memory.v|Vellvm.Semantics.Interfaces.Memory|read_byte"
  read_byte : ∀ [Pa : Params] [M : MemoryModelPrimitives.{u,v,w,z,r}],
    Pa.PTR.ptr → memM (MMS := M.mm_state) memory_byte

#source_check "src/rocq/Semantics/Interfaces/Memory.v|Vellvm.Semantics.Interfaces.Memory|write_byte"
  write_byte : ∀ [Pa : Params] [M : MemoryModelPrimitives.{u,v,w,z,r}],
    Pa.PTR.ptr → memory_byte → memM (MMS := M.mm_state) Unit

#source_check "src/rocq/Semantics/Interfaces/Memory.v|Vellvm.Semantics.Interfaces.Memory|allocate_bytes_with_pr"
  allocate_bytes_with_pr : ∀ [Pa : Params] [M : MemoryModelPrimitives.{u,v,w,z,r}],
    List memory_byte → Nat → Pa.PROV.provenance → memM (MMS := M.mm_state) Pa.PTR.ptr

#source_check "src/rocq/Semantics/Interfaces/Memory.v|Vellvm.Semantics.Interfaces.Memory|malloc_bytes_with_pr"
  malloc_bytes_with_pr : ∀ [Pa : Params] [M : MemoryModelPrimitives.{u,v,w,z,r}],
    List memory_byte → Nat → Pa.PROV.provenance → memM (MMS := M.mm_state) Pa.PTR.ptr

#source_check "src/rocq/Semantics/Interfaces/Memory.v|Vellvm.Semantics.Interfaces.Memory|free"
  free : ∀ [Pa : Params] [M : MemoryModelPrimitives.{u,v,w,z,r}],
    Pa.PTR.ptr → memM (MMS := M.mm_state) Unit

#source_check "src/rocq/Semantics/Interfaces/Memory.v|Vellvm.Semantics.Interfaces.Memory|mempush"
  mempush : ∀ [Pa : Params] [M : MemoryModelPrimitives.{u,v,w,z,r}], memM (MMS := M.mm_state) Unit

#source_check "src/rocq/Semantics/Interfaces/Memory.v|Vellvm.Semantics.Interfaces.Memory|mempop"
  mempop : ∀ [Pa : Params] [M : MemoryModelPrimitives.{u,v,w,z,r}], memM (MMS := M.mm_state) Unit
