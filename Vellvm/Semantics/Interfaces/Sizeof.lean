module

public import Vellvm.Syntax.DynamicTypes

@[expose] public section
namespace Vellvm.Semantics.Interfaces.Sizeof
open Vellvm.Syntax.LLVMAst Vellvm.Syntax.DynamicTypes

def pad_amount (alignment offset : Nat) := (alignment - offset % alignment) % alignment
def pad_to (alignment sz : Nat) := sz + pad_amount alignment sz

structure alignment where
  Build_alignment ::
  abi_alignment : Nat
  preferred_alignment : Nat
export alignment (Build_alignment abi_alignment preferred_alignment)

/-- The source uses preferred alignment, not ABI alignment, for layout. -/
def pad_to_align (a : alignment) := pad_to a.preferred_alignment
def pad_to_align_bitwise (a : alignment) := pad_to (a.preferred_alignment * 8)

theorem pad_to_0 (x : Nat) : pad_to 0 x = x := by simp [pad_to, pad_amount]

theorem pad_to_mod {a : Nat} (x : Nat) (h : a ≠ 0) : pad_to a x % a = 0 := by
  have bound := Nat.mod_lt x (Nat.pos_of_ne_zero h)
  simp only [pad_to, pad_amount, Nat.add_mod_mod]
  rw [← Nat.mod_add_mod, Nat.add_sub_of_le (Nat.le_of_lt bound), Nat.mod_self]

theorem pad_amount_aligned (a y : Nat) (h : y % a = 0) : pad_amount a y = 0 := by
  simp [pad_amount, h]

theorem pad_to_idem (a x : Nat) : pad_to a (pad_to a x) = pad_to a x := by
  by_cases h : a = 0
  · simp [h, pad_to_0]
  · exact Nat.add_eq_left.mpr (pad_amount_aligned _ _ (pad_to_mod x h))

class Sizeof : Type where
  Build_Sizeof ::
  bit_sizeof_dtyp : dtyp → Nat
  store_size_dtyp : dtyp → Nat
  dtyp_alignment : dtyp → alignment
export Sizeof (Build_Sizeof bit_sizeof_dtyp store_size_dtyp dtyp_alignment)

def alloc_size_dtyp [Sizeof] (t : dtyp) : Nat := pad_to_align (dtyp_alignment t) (store_size_dtyp t)

def max_preferred_dtyp_alignment [Sizeof] (dts : List dtyp) : Nat :=
  dts.foldl (fun a t ↦ max a (dtyp_alignment t).preferred_alignment) 1

def ptr_size [Sizeof] : Nat := store_size_dtyp DTYPE_Pointer

def struct_fields_extent [Sizeof] (packed : Bool) (dts : List dtyp) : Nat :=
  dts.foldl (fun acc t ↦ (if packed then acc else pad_to_align (dtyp_alignment t) acc) +
    alloc_size_dtyp t) 0

class SizeofTheory [S : Sizeof] : Prop where
  Build_SizeofTheory ::
  store_size_dtyp_void : store_size_dtyp DTYPE_Void = 0
  store_size_dtyp_pos : ∀ t, 0 ≤ store_size_dtyp t
  store_size_dtyp_Struct : ∀ ts, store_size_dtyp (DTYPE_Struct false ts) =
    pad_to (max_preferred_dtyp_alignment ts) (struct_fields_extent false ts)
  store_size_dtyp_Packed_struct : ∀ ts,
    store_size_dtyp (DTYPE_Struct true ts) = struct_fields_extent true ts
  store_size_dtyp_array : ∀ n t, store_size_dtyp (DTYPE_Array false n t) = n * alloc_size_dtyp t
  store_size_dtyp_vector_int : ∀ n m,
    store_size_dtyp (DTYPE_Array true n (DTYPE_I m)) = (n * m.val + 7) / 8
  store_size_dtyp_vector_bytes : ∀ n m,
    store_size_dtyp (DTYPE_Array true n (DTYPE_B m)) = (n * m.val + 7) / 8
  store_size_dtyp_vector : ∀ n t, (∀ m, t ≠ DTYPE_Base (DTYPE_I m)) →
    (∀ m, t ≠ DTYPE_Base (DTYPE_B m)) → store_size_dtyp (DTYPE_Array true n t) = n * store_size_dtyp t
  store_size_dtyp_i8 : store_size_dtyp (DTYPE_I ⟨8, by decide⟩) = 1
  store_size_dtyp_int : ∀ sz, store_size_dtyp (DTYPE_I sz) = (sz.val + 7) / 8
  store_size_dtyp_bytes : ∀ sz, store_size_dtyp (DTYPE_B sz) = (sz.val + 7) / 8
  store_size_dtyp_float : store_size_dtyp (DTYPE_FP FP_float) = 4
  store_size_dtyp_double : store_size_dtyp (DTYPE_FP FP_double) = 8
  store_size_dtyp_ptr_pos : 0 < store_size_dtyp DTYPE_Pointer
  store_size_dtyp_iptr_pos : 0 < store_size_dtyp DTYPE_Iptr
  store_size_dtyp_Struct_alloc : ∀ ts,
    alloc_size_dtyp (DTYPE_Struct false ts) = store_size_dtyp (DTYPE_Struct false ts)
export SizeofTheory (Build_SizeofTheory store_size_dtyp_void store_size_dtyp_pos store_size_dtyp_Struct
  store_size_dtyp_Packed_struct store_size_dtyp_array store_size_dtyp_vector_int
  store_size_dtyp_vector_bytes store_size_dtyp_vector store_size_dtyp_i8 store_size_dtyp_int
  store_size_dtyp_bytes store_size_dtyp_float store_size_dtyp_double store_size_dtyp_ptr_pos
  store_size_dtyp_iptr_pos store_size_dtyp_Struct_alloc)

theorem store_le_alloc [Sizeof] (t : dtyp) : store_size_dtyp t ≤ alloc_size_dtyp t :=
  Nat.le_add_right _ _

section
variable [S : Sizeof] [@SizeofTheory S]
include S

theorem store_size_B_I (sz : Positive) : store_size_dtyp (DTYPE_B sz) = store_size_dtyp (DTYPE_I sz) := by
  rw [store_size_dtyp_bytes, store_size_dtyp_int]

theorem store_size_int_mult8 (sz : Positive) (h : sz.val % 8 = 0) :
    8 * store_size_dtyp (DTYPE_I sz) = sz.val := by rw [store_size_dtyp_int]; omega

theorem store_size_int_mixed (sz : Positive) (h : sz.val % 8 ≠ 0) :
    1 ≤ store_size_dtyp (DTYPE_I sz) ∧
    8 * (store_size_dtyp (DTYPE_I sz) - 1) + sz.val % 8 = sz.val := by
  rw [store_size_dtyp_int]; omega

theorem store_size_int_bits (sz : Positive) : sz.val ≤ 8 * store_size_dtyp (DTYPE_I sz) := by
  rw [store_size_dtyp_int]; omega

theorem store_size_B_bytes (sz : Positive) (h : sz.val % 8 = 0) :
    8 * store_size_dtyp (DTYPE_B sz) = sz.val := by
  rw [store_size_B_I]; exact store_size_int_mult8 sz h

end
end Vellvm.Semantics.Interfaces.Sizeof
