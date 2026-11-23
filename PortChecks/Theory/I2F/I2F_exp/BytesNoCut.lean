import PortChecks.SourceType
import Vellvm.Theory.I2F.I2F_exp.BytesNoCut

open Vellvm Vellvm.Semantics Vellvm.Semantics.Interfaces.Params Vellvm.Semantics.EOU
open Vellvm.Semantics.MemoryBytes Vellvm.Semantics.DynamicValues Vellvm.Utils.ListUtil
open Vellvm.Theory.I2F.Refinement Vellvm.Syntax.DynamicTypes Vellvm.Numeric.Integers
universe u
open Vellvm.Theory.I2F.I2F_exp

#source_check "src/rocq/Theory/I2F/I2F_exp.v|Vellvm.Theory.I2F.I2F_exp|no_cut"
  no_cut : {A : Type u} → EOU A → Prop

#source_check "src/rocq/Theory/I2F/I2F_exp.v|Vellvm.Theory.I2F.I2F_exp|no_cut_ret"
  no_cut_ret : ∀ {A : Type u} (a : A), no_cut (raise_ret a)

#source_check "src/rocq/Theory/I2F/I2F_exp.v|Vellvm.Theory.I2F.I2F_exp|no_cut_bind_EOUP"
  no_cut_bind_EOUP : ∀ {A B : Type u} (c : EOUP A) (k : A → EOUP B),
    no_cut c → (∀ a, no_cut (k a)) → no_cut (c >>= k : EOUP B)

#source_check "src/rocq/Theory/I2F/I2F_exp.v|Vellvm.Theory.I2F.I2F_exp|no_cut_map_monad_EOUP"
  no_cut_map_monad_EOUP : ∀ {A B : Type u} (f : A → EOUP B),
    (∀ a, no_cut (f a)) → ∀ xs, no_cut (map_monad (m := EOUP) f xs)

#source_check "src/rocq/Theory/I2F/I2F_exp.v|Vellvm.Theory.I2F.I2F_exp|no_cut_memory_bit_to_bit"
  no_cut_memory_bit_to_bit : ∀ [Pa : Params] b, no_cut (@memory_bit_to_bit Pa b)

#source_check "src/rocq/Theory/I2F/I2F_exp.v|Vellvm.Theory.I2F.I2F_exp|no_cut_memory_bits_to_Z"
  no_cut_memory_bits_to_Z : ∀ [Pa : Params] bits, no_cut (@memory_bits_to_Z Pa bits)

#source_check "src/rocq/Theory/I2F/I2F_exp.v|Vellvm.Theory.I2F.I2F_exp|no_cut_memory_byte_to_Z"
  no_cut_memory_byte_to_Z : ∀ [Pa : Params] b, no_cut (@memory_byte_to_Z Pa b)

#source_check "src/rocq/Theory/I2F/I2F_exp.v|Vellvm.Theory.I2F.I2F_exp|no_cut_concat_bytes_Z_mixed"
  no_cut_concat_bytes_Z_mixed : ∀ [Pa : Params] extra bs, no_cut (@concat_bytes_Z_mixed Pa extra bs)

#source_check "src/rocq/Theory/I2F/I2F_exp.v|Vellvm.Theory.I2F.I2F_exp|no_cut_memory_bytes_to_int"
  no_cut_memory_bytes_to_int : ∀ [Pa : Params] sz bs, no_cut (@memory_bytes_to_int Pa sz bs)

#source_check "src/rocq/Theory/I2F/I2F_exp.v|Vellvm.Theory.I2F.I2F_exp|no_cut_valid_pointer_bits"
  no_cut_valid_pointer_bits : ∀ [Pa : Params] p base bits off, no_cut (@valid_pointer_bits Pa p base off bits)

#source_check "src/rocq/Theory/I2F/I2F_exp.v|Vellvm.Theory.I2F.I2F_exp|no_cut_valid_pointer_byte"
  no_cut_valid_pointer_byte : ∀ [Pa : Params] p idx b, no_cut (@valid_pointer_byte Pa p idx b)

#source_check "src/rocq/Theory/I2F/I2F_exp.v|Vellvm.Theory.I2F.I2F_exp|no_cut_valid_pointer_bytes"
  no_cut_valid_pointer_bytes : ∀ [Pa : Params] p bs idx, no_cut (@valid_pointer_bytes Pa p idx bs)
