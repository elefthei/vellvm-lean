module

public import Vellvm.Utils.IntMaps

@[expose] public section
namespace Vellvm.Semantics.Handlers.Memory
open Vellvm.Utils.IntMaps

def pad_amount (align offset : Nat) := (align - offset % align) % align
def pad_to (align size : Nat) := size + pad_amount align size

def next_key_with_alignment (m : IntMap A) (align : Nat) : Int :=
  match IM_greatest_key m with
  | some k => pad_to align (1 + k.toNat)
  | none => pad_to align 1

end Vellvm.Semantics.Handlers.Memory
