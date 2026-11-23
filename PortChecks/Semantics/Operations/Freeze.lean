import PortChecks.SourceType
import Vellvm.Semantics.Operations.Freeze

open Vellvm
open ITree (Effect Subeffect)
open Vellvm.Semantics.Interfaces.Params Vellvm.Semantics.DynamicValues Vellvm.Semantics.LLVMEvents
open Vellvm.Semantics.Operations.Freeze Vellvm.Syntax.DynamicTypes

#source_check "src/rocq/Semantics/Operations/Freeze.v|Vellvm.Semantics.Operations.Freeze|freeze_bits"
  freeze_bits : ∀ [Pa : Params], Int → Nat → List memory_bit → List memory_bit
#source_check "src/rocq/Semantics/Operations/Freeze.v|Vellvm.Semantics.Operations.Freeze|freeze_mixed_bits"
  freeze_mixed_bits : ∀ [Pa : Params] (sz : Positive), Int → List memory_bit → dvalue_bv sz
#source_check "src/rocq/Semantics/Operations/Freeze.v|Vellvm.Semantics.Operations.Freeze|freeze_base"
  freeze_base : ∀ [Pa : Params] {E B : Effect} [DrawE -< E] [FailureE -< E] [OOME -< E] [UBE -< E],
    dtyp → dvalue_base → CTree.CTree E B dvalue
#source_check "src/rocq/Semantics/Operations/Freeze.v|Vellvm.Semantics.Operations.Freeze|freeze"
  freeze : ∀ [Pa : Params] {E B : Effect} [DrawE -< E] [FailureE -< E] [OOME -< E] [UBE -< E],
    dtyp → dvalue → CTree.CTree E B dvalue

-- Either choice for the poisoned bit leaves the pointer, including its provenance, untouched.
example [Pa : Params] (p : Pa.PTR.ptr) (idx : Nat) (sz : Positive) (z : Int) :
    freeze_mixed_bits sz z [.Bit_ptr p idx, .Bit_psn] =
      .BYTE_Mixed [.Bit_ptr p idx, Z_to_memory_bit (if z.testBit 1 then 1 else 0)] := rfl

variable [Pa : Params] {E B : Effect} [DrawE -< E] [FailureE -< E] [OOME -< E] [UBE -< E]

example (dt : dtyp) (sz : Positive) (p : Pa.PTR.ptr) (idx : Nat) :
    let mixed := DVALUE_B sz (BYTE_Mixed [Bit_ptr p idx, Z_to_memory_bit 0])
    freeze_base dt mixed = (pure (DVALUE_Base mixed) : CTree.CTree E B dvalue) := rfl

-- Even when two leaves have the same type and value, each poison gets its own draw.
example (dt : dtyp) :
    freeze (DTYPE_Struct true [DTYPE_Array true 2 dt])
      (DVALUE_Struct false [DVALUE_Array false [DVALUE_Base DVALUE_Poison, DVALUE_Base DVALUE_Poison]]) =
      (do
        let a ← draw dt
        let b ← draw dt
        pure (DVALUE_Struct true [DVALUE_Array true [a, b]]) : CTree.CTree E B dvalue) := by
  simp [freeze, Worker.freeze, Worker.freezeFields, Worker.freezeElts, Worker.freeze_base,
    draw, bind_assoc]
