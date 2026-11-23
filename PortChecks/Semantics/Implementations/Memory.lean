import PortChecks.SourceType
import Vellvm.Semantics.Implementations.Memory.Primitives

open Vellvm.Semantics.Interfaces.Params Vellvm.Semantics.Interfaces.Memory
open Vellvm.Semantics.Implementations.Memory

universe u

#source_check "src/rocq/Semantics/Implementations/Memory.v|Vellvm.Semantics.Implementations.Memory|Framestack_rect"
  Framestack_rect : ∀ [Pa : Params] (P : Framestack → Type u),
    (∀ f, P (Singleton f)) → (∀ s, P s → ∀ f, P (Snoc s f)) → ∀ s, P s
#source_check "src/rocq/Semantics/Implementations/Memory.v|Vellvm.Semantics.Implementations.Memory|Framestack_rec"
  Framestack_rec : ∀ [Pa : Params] (P : Framestack → Type),
    (∀ f, P (Singleton f)) → (∀ s, P s → ∀ f, P (Snoc s f)) → ∀ s, P s
#source_check "src/rocq/Semantics/Implementations/Memory.v|Vellvm.Semantics.Implementations.Memory|Framestack_ind"
  Framestack_ind : ∀ [Pa : Params] (P : Framestack → Prop),
    (∀ f, P (Singleton f)) → (∀ s, P s → ∀ f, P (Snoc s f)) → ∀ s, P s
#source_check "src/rocq/Semantics/Implementations/Memory.v|Vellvm.Semantics.Implementations.Memory|Framestack_sind"
  Framestack_sind : ∀ [Pa : Params] (P : Framestack → Prop),
    (∀ f, P (Singleton f)) → (∀ s, P s → ∀ f, P (Snoc s f)) → ∀ s, P s
#source_check "src/rocq/Semantics/Implementations/Memory.v|Vellvm.Semantics.Implementations.Memory|MemoryModelStateV"
  MemoryModelStateV : ∀ [Pa : Params], @MemoryModelState.{0,0,0,0,0} Pa
#source_check "src/rocq/Semantics/Implementations/Memory.v|Vellvm.Semantics.Implementations.Memory|MemoryModelPrimitivesV"
  MemoryModelPrimitivesV : ∀ [Pa : Params], @MemoryModelPrimitives.{0,0,0,0,0} Pa
