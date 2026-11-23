import Vellvm.Semantics.MemoryBytes
import Vellvm.Theory.I2F.I2F_exp.MemoryByte

namespace Vellvm.Theory.I2F.I2F_exp
open Vellvm Vellvm.Semantics Vellvm.Semantics.Interfaces.Params Vellvm.Semantics.EOU
open Vellvm.Semantics.MemoryBytes Vellvm.Semantics.DynamicValues Vellvm.Utils.ListUtil
open Vellvm.Theory.I2F.Refinement Vellvm.Syntax.DynamicTypes Vellvm.Numeric.Integers
universe u
open Vellvm.Semantics.Interfaces.Sizeof

def accumulate_struct_bytes [Pa : Params] (ta pad : Option Nat) :=
  @writeStruct Pa acc_dvalue_to_memory_bytes_h ta pad

def accumulate_array_bytes [Pa : Params] (ta : Option Nat) (v : Bool) (t : dtyp) :=
  @writeArray Pa acc_dvalue_to_memory_bytes_h ta t
    (if v then 0 else @alloc_size_dtyp Pa.SIZE t - @store_size_dtyp Pa.SIZE t)

theorem ser_Base_eq : ∀ [Pa : Params] t x o ta acc, @acc_dvalue_to_memory_bytes_h Pa (.DTYPE_Base t) (.DVALUE_Base x) o ta acc =
    let (i, bs) := acc_memory_bytes_of_dvalue_base t x o acc
    pure (accumulate_padding i ta bs) := by intros; rw [acc_dvalue_to_memory_bytes_h]

theorem ser_Struct_eq : ∀ [Pa : Params] p ts b xs o ta acc, @acc_dvalue_to_memory_bytes_h Pa (.DTYPE_Struct p ts) (.DVALUE_Struct b xs) o ta acc =
    accumulate_struct_bytes ta (if p then none else some (@max_preferred_dtyp_alignment Pa.SIZE ts)) xs ts o acc := by intros; rw [acc_dvalue_to_memory_bytes_h]; rfl

theorem ser_Array_eq : ∀ [Pa : Params] p n t b xs o ta acc, @acc_dvalue_to_memory_bytes_h Pa (.DTYPE_Array p n t) (.DVALUE_Array b xs) o ta acc =
    match packed_vector_type (.DTYPE_Array p n t) with
    | some (_, m) => writePacked m (.DTYPE_Array p n t) xs o ta acc
    | none => accumulate_array_bytes ta p t xs o acc := by intros; rw [acc_dvalue_to_memory_bytes_h]; rfl

theorem ser_Struct_poison_eq : ∀ [Pa : Params] p ts o ta acc, @acc_dvalue_to_memory_bytes_h Pa (.DTYPE_Struct p ts) (.DVALUE_Base .DVALUE_Poison) o ta acc =
    let (i, bs) := accumulate_padding_bytes o (@store_size_dtyp Pa.SIZE (.DTYPE_Struct p ts)) acc
    pure (accumulate_padding i ta bs) := by intros; rw [acc_dvalue_to_memory_bytes_h] <;> rfl

theorem ser_Array_poison_eq : ∀ [Pa : Params] v n t o ta acc, @acc_dvalue_to_memory_bytes_h Pa (.DTYPE_Array v n t) (.DVALUE_Base .DVALUE_Poison) o ta acc =
    let (i, bs) := accumulate_padding_bytes o (@store_size_dtyp Pa.SIZE (.DTYPE_Array v n t)) acc
    pure (accumulate_padding i ta bs) := by intros; rw [acc_dvalue_to_memory_bytes_h] <;> rfl

theorem acc_struct_nil : ∀ [Pa : Params] ta pad o acc, @accumulate_struct_bytes Pa ta pad [] [] o acc =
    let (i, bs) := accumulate_padding o pad acc
    pure (accumulate_padding i ta bs) := by intros; rfl

theorem acc_struct_nil_cons : ∀ [Pa : Params] ta pad t ts o acc, @accumulate_struct_bytes Pa ta pad [] (t :: ts) o acc =
    raise_error "type-mismatch: structs / fields have different lengths".toUTF8 := by intros; rfl

theorem acc_struct_cons_nil : ∀ [Pa : Params] ta pad x xs o acc, @accumulate_struct_bytes Pa ta pad (x :: xs) [] o acc =
    raise_error "type-mismatch: structs / fields have different lengths".toUTF8 := by intros; rfl

theorem acc_struct_cons : ∀ [Pa : Params] ta pad x xs t ts o acc, @accumulate_struct_bytes Pa ta pad (x :: xs) (t :: ts) o acc = (do
    let (i, bs) := accumulate_padding o (pad.map fun _ ↦ (@dtyp_alignment Pa.SIZE t).preferred_alignment) acc
    let (j, cs) ← acc_dvalue_to_memory_bytes_h t x 0 none bs
    let (k, ds) := accumulate_padding_bytes (i+j) (@alloc_size_dtyp Pa.SIZE t - @store_size_dtyp Pa.SIZE t) cs
    accumulate_struct_bytes ta pad xs ts k ds)
  := by intros; rfl

theorem acc_array_nil : ∀ [Pa : Params] ta v t o acc, @accumulate_array_bytes Pa ta v t [] o acc = pure (accumulate_padding o ta acc) := by intros; rfl

theorem acc_array_cons : ∀ [Pa : Params] ta v t x xs o acc, @accumulate_array_bytes Pa ta v t (x :: xs) o acc = (do
    let (j, bs) ← acc_dvalue_to_memory_bytes_h t x 0 none acc
    let (k, cs) := accumulate_padding_bytes (o+j) (if v then 0 else @alloc_size_dtyp Pa.SIZE t - @store_size_dtyp Pa.SIZE t) bs
    accumulate_array_bytes ta v t xs k cs)
  := by intros; rfl

end Vellvm.Theory.I2F.I2F_exp
