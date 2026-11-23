module

public import Vellvm.Semantics.DynamicValues.Basic

@[expose] public section
namespace Vellvm.Semantics.MemoryBytes
open Interfaces.Params Interfaces.Sizeof DynamicValues Utils.ListUtil

abbrev memory_byte [Pa : Params] := dvalue_bv (Pa := Pa) ⟨8, by decide⟩

variable [Pa : Params]

def poison_memory_byte : memory_byte := BYTE_Mixed (List.replicate 8 Bit_psn)

def accumulate_memory_bytes (mb : memory_byte) (num_bytes : Nat) : List memory_byte → List memory_byte :=
  N.rev_loop_acc (fun _ ↦ mb) num_bytes 0

def accumulate_poison_bytes (n : Nat) : List memory_byte → List memory_byte :=
  accumulate_memory_bytes poison_memory_byte n

def accumulate_padding_bytes (offset n : Nat) (acc : List memory_byte) : Nat × List memory_byte :=
  (offset + n, accumulate_poison_bytes n acc)

def accumulate_padding (offset : Nat) (ta : Option Nat) (acc : List memory_byte) : Nat × List memory_byte :=
  match ta with
  | none => (offset, acc)
  | some a => accumulate_padding_bytes offset (pad_amount a offset) acc

end Vellvm.Semantics.MemoryBytes
