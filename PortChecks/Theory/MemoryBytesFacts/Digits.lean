import PortChecks.SourceType
import Vellvm.Theory.MemoryBytesFacts.Digits

open Vellvm Vellvm.Numeric.Integers Vellvm.Semantics.MemoryBytes Vellvm.Utils.ListUtil
open Vellvm.Theory.MemoryBytesFacts

#source_check "src/rocq/Theory/MemoryBytesFacts.v|Vellvm.Theory.MemoryBytesFacts|extract_bit_N"
  extract_bit_N : Nat → Nat → Nat
#source_check "src/rocq/Theory/MemoryBytesFacts.v|Vellvm.Theory.MemoryBytesFacts|concat_bytes_Z_extract"
  concat_bytes_Z_extract : ∀ (k : Nat) (v : Int) (j : Nat),
    concat_bytes_Z ((Nseq j k).map (fun i ↦ v / 2^(8*i) % 256)) = v / 2^(8*j) % 2^(8*k)
#source_check "src/rocq/Theory/MemoryBytesFacts.v|Vellvm.Theory.MemoryBytesFacts|extract_byte_vint_spec"
  extract_byte_vint_spec : ∀ {sz} (x : bit_int sz) (idx : Nat),
    8 * ((idx : Int) + 1) ≤ (sz.val : Int) → extract_byte_vint x idx = unsigned x / 2^(8*idx) % 256
#source_check "src/rocq/Theory/MemoryBytesFacts.v|Vellvm.Theory.MemoryBytesFacts|extract_byte_vint_spec_lt"
  extract_byte_vint_spec_lt : ∀ {sz} (x : bit_int sz) (idx : Nat),
    8 * (idx : Int) < (sz.val : Int) → extract_byte_vint x idx = unsigned x / 2^(8*idx) % 256
#source_check "src/rocq/Theory/MemoryBytesFacts.v|Vellvm.Theory.MemoryBytesFacts|extract_bit_N_spec"
  extract_bit_N_spec : ∀ {v : Int} (i : Nat), 0 ≤ v →
    (extract_bit_N v.toNat i : Int) = v / 2^i % 2
#source_check "src/rocq/Theory/MemoryBytesFacts.v|Vellvm.Theory.MemoryBytesFacts|concat_bits_Z_extract"
  concat_bits_Z_extract : ∀ (n : Nat) (v : Int) (j : Nat),
    concat_bits_Z ((Nseq j n).map (fun i ↦ v / 2^i % 2)) = v / 2^j % 2^n
#source_check "src/rocq/Theory/MemoryBytesFacts.v|Vellvm.Theory.MemoryBytesFacts|extract_byte_Z_spec"
  extract_byte_Z_spec : ∀ (v : Int) (idx : Nat), extract_byte_Z v idx = v / 2^(8*idx) % 256
#source_check "src/rocq/Theory/MemoryBytesFacts.v|Vellvm.Theory.MemoryBytesFacts|concat_bytes_vint_Z"
  concat_bytes_vint_Z : ∀ w (zs : List Int), 8 < @modulus w →
    concat_bytes_vint (zs.map (@Vellvm.Numeric.Integers.repr w)) =
      Vellvm.Numeric.Integers.repr (concat_bytes_Z zs)
