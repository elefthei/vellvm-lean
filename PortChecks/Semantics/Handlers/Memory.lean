import PortChecks.SourceType
import Vellvm.Semantics.Handlers.Memory

open Vellvm.Utils.IntMaps Vellvm.Semantics.Handlers.Memory
universe u

#source_check "src/rocq/Semantics/Handlers/Memory.v|Vellvm.Semantics.Handlers.Memory|next_key_with_alignment"
  next_key_with_alignment : ∀ {A : Type u}, IntMap A → Nat → Int
