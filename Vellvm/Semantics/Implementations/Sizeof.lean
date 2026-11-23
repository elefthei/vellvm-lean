module

public import Vellvm.Semantics.Interfaces.Sizeof

@[expose] public section
namespace Vellvm.Semantics.Implementations.Sizeof
open Vellvm.Syntax.LLVMAst Vellvm.Syntax.DynamicTypes Vellvm.Semantics.Interfaces.Sizeof

def ptr_size : Nat := 8

def byte_sizeof_floating_point_variant : floating_point_variant → Nat
  | .FP_half | .FP_bfloat => 2
  | .FP_float => 4
  | .FP_double => 8
  | .FP_x86_fp80 => 10
  | .FP_fp128 | .FP_ppc_fp128 => 16

def bit_sizeof_floating_point_variant (fp : floating_point_variant) :=
  8 * byte_sizeof_floating_point_variant fp

def Bit_sizeof_dtyp_base : dtyp_base → Nat
  | .DTYPE_I sz | .DTYPE_B sz => sz.val
  | .DTYPE_FP fp => bit_sizeof_floating_point_variant fp
  | .DTYPE_Iptr | .DTYPE_Pointer | .DTYPE_Label | .DTYPE_Token | .DTYPE_X86_mmx => 64
  | .DTYPE_Void | .DTYPE_Metadata | .DTYPE_Opaque => 0

def Dtyp_base_alignment : dtyp_base → alignment
  | .DTYPE_I sz | .DTYPE_B sz =>
    if sz.val ≤ 8 then ⟨1, 1⟩ else if sz.val ≤ 16 then ⟨2, 2⟩
    else if sz.val ≤ 32 then ⟨4, 4⟩ else ⟨4, 8⟩
  | .DTYPE_FP .FP_half | .DTYPE_FP .FP_bfloat => ⟨2, 2⟩
  | .DTYPE_FP .FP_float => ⟨4, 4⟩
  | .DTYPE_FP .FP_x86_fp80 | .DTYPE_FP .FP_fp128 | .DTYPE_FP .FP_ppc_fp128 => ⟨16, 16⟩
  | .DTYPE_FP .FP_double | .DTYPE_Label | .DTYPE_Token | .DTYPE_X86_mmx
  | .DTYPE_Iptr | .DTYPE_Pointer => ⟨8, 8⟩
  | .DTYPE_Void | .DTYPE_Metadata | .DTYPE_Opaque => ⟨1, 1⟩

def max_alignment (a b : alignment) : alignment :=
  ⟨max a.abi_alignment b.abi_alignment, max a.preferred_alignment b.preferred_alignment⟩

def vector_alignment (n : Nat) (elt : dtyp_base) : alignment :=
  let bytes := (n * Bit_sizeof_dtyp_base elt + 7) / 8
  let a := bytes.nextPowerOfTwo
  ⟨a, a⟩

def Dtyp_alignment : dtyp → alignment
  | .DTYPE_Base t => Dtyp_base_alignment t
  | .DTYPE_Struct true _ => ⟨1, 1⟩
  | .DTYPE_Struct false fields => fields.foldl (fun a f ↦ max_alignment a (Dtyp_alignment f)) ⟨1, 1⟩
  | .DTYPE_Array true sz (.DTYPE_Base t) => vector_alignment sz t
  | .DTYPE_Array _ _ t => Dtyp_alignment t

def max_preferred_dtyp_alignment (ts : List dtyp) : Nat :=
  ts.foldl (fun a t ↦ max a (Dtyp_alignment t).preferred_alignment) 1

def round_up_to_eight (n : Nat) := if n = 0 then 0 else ((n - 1) / 8 + 1) * 8

def Bit_sizeof_dtyp : dtyp → Nat
  | .DTYPE_Base t => Bit_sizeof_dtyp_base t
  | .DTYPE_Struct false ts =>
    let sz := ts.foldl (fun a x ↦ pad_to_align_bitwise (Dtyp_alignment x) a + Bit_sizeof_dtyp x) 0
    pad_to (8 * max_preferred_dtyp_alignment ts) sz
  | .DTYPE_Struct true ts => ts.foldl (fun a x ↦ a + round_up_to_eight (Bit_sizeof_dtyp x)) 0
  | .DTYPE_Array false sz t => sz * round_up_to_eight (Bit_sizeof_dtyp t)
  | .DTYPE_Array true sz t => sz * Bit_sizeof_dtyp t

def Sizeof_dtyp_base : dtyp_base → Nat
  | .DTYPE_I sz | .DTYPE_B sz => round_up_to_eight sz.val / 8
  | .DTYPE_Iptr | .DTYPE_Pointer => ptr_size
  | .DTYPE_FP fp => byte_sizeof_floating_point_variant fp
  | .DTYPE_Label | .DTYPE_Token | .DTYPE_X86_mmx => 8
  | .DTYPE_Void | .DTYPE_Metadata | .DTYPE_Opaque => 0

def Store_size_dtyp : dtyp → Nat
  | .DTYPE_Base t => Sizeof_dtyp_base t
  | .DTYPE_Struct true ts =>
    ts.foldl (fun a x ↦ a + pad_to_align (Dtyp_alignment x) (Store_size_dtyp x)) 0
  | .DTYPE_Struct false ts =>
    let sz := ts.foldl (fun a x ↦
      let align := Dtyp_alignment x
      pad_to_align align a + pad_to_align align (Store_size_dtyp x)) 0
    pad_to (max_preferred_dtyp_alignment ts) sz
  | .DTYPE_Array false sz t => sz * pad_to_align (Dtyp_alignment t) (Store_size_dtyp t)
  | .DTYPE_Array true sz (.DTYPE_Base t) => (sz * Bit_sizeof_dtyp_base t + 7) / 8
  | .DTYPE_Array true sz t => sz * Store_size_dtyp t

instance SizeofV : Sizeof := ⟨Bit_sizeof_dtyp, Store_size_dtyp, Dtyp_alignment⟩

theorem Store_size_alloc_size (t : dtyp) : alloc_size_dtyp t =
    pad_to_align (Dtyp_alignment t) (Store_size_dtyp t) := rfl

theorem struct_fields_extent_V (packed : Bool) (l : List dtyp) : struct_fields_extent packed l =
    l.foldl (fun acc x ↦ (if packed then acc else pad_to_align (Dtyp_alignment x) acc) +
      pad_to_align (Dtyp_alignment x) (Store_size_dtyp x)) 0 := rfl

theorem preferred_Dtyp_alignment_Struct (dts : List dtyp) :
    (Dtyp_alignment (DTYPE_Struct false dts)).preferred_alignment = max_preferred_dtyp_alignment dts := by
  rw [Dtyp_alignment, max_preferred_dtyp_alignment]
  symm
  apply List.foldl_hom preferred_alignment (init := ⟨1, 1⟩)
  intros; rfl

theorem round_up_to_eight_div {n : Nat} (h : 0 < n) : round_up_to_eight n / 8 = (n + 7) / 8 := by
  simp [round_up_to_eight, Nat.ne_of_gt h]; omega

private theorem vector_bytes (n : Nat) (b : dtyp_base)
    (hi : ∀ m, b ≠ DTYPE_I m) (hb : ∀ m, b ≠ DTYPE_B m) :
    (n * Bit_sizeof_dtyp_base b + 7) / 8 = n * Sizeof_dtyp_base b := by
  have h : Bit_sizeof_dtyp_base b = 8 * Sizeof_dtyp_base b := by
    cases b <;> first | rfl | exact False.elim (hi _ rfl) | exact False.elim (hb _ rfl)
  rw [h, Nat.mul_left_comm n 8]
  omega

instance SizeofTheoryV : @SizeofTheory SizeofV where
  store_size_dtyp_void := by
    change Store_size_dtyp (DTYPE_Base DTYPE_Void) = 0
    rw [Store_size_dtyp]; rfl
  store_size_dtyp_pos := fun _ ↦ Nat.zero_le _
  store_size_dtyp_Struct := fun ts ↦ by
    change Store_size_dtyp (DTYPE_Struct false ts) = _
    rw [Store_size_dtyp]; rfl
  store_size_dtyp_Packed_struct := fun ts ↦ by
    change Store_size_dtyp (DTYPE_Struct true ts) = _
    rw [Store_size_dtyp]; rfl
  store_size_dtyp_array := fun n t ↦ by
    change Store_size_dtyp (DTYPE_Array false n t) = _
    rw [Store_size_dtyp]; rfl
  store_size_dtyp_vector_int := fun n m ↦ by
    change Store_size_dtyp (DTYPE_Array true n (DTYPE_Base (DTYPE_I m))) = _
    rw [Store_size_dtyp]; rfl
  store_size_dtyp_vector_bytes := fun n m ↦ by
    change Store_size_dtyp (DTYPE_Array true n (DTYPE_Base (DTYPE_B m))) = _
    rw [Store_size_dtyp]; rfl
  store_size_dtyp_vector := by
    intro n t hi hb
    change Store_size_dtyp (DTYPE_Array true n t) = n * Store_size_dtyp t
    cases t with
    | DTYPE_Base b =>
      rw [Store_size_dtyp, Store_size_dtyp]
      exact vector_bytes n b (fun m h ↦ hi m (congrArg DTYPE_Base h))
        (fun m h ↦ hb m (congrArg DTYPE_Base h))
    | DTYPE_Array _ _ _ | DTYPE_Struct _ _ => rw [Store_size_dtyp] <;> simp
  store_size_dtyp_i8 := by
    change Store_size_dtyp (DTYPE_Base (DTYPE_I ⟨8, by decide⟩)) = 1
    rw [Store_size_dtyp]; rfl
  store_size_dtyp_int := fun sz ↦ by
    change Store_size_dtyp (DTYPE_Base (DTYPE_I sz)) = _
    rw [Store_size_dtyp]; exact round_up_to_eight_div sz.property
  store_size_dtyp_bytes := fun sz ↦ by
    change Store_size_dtyp (DTYPE_Base (DTYPE_B sz)) = _
    rw [Store_size_dtyp]; exact round_up_to_eight_div sz.property
  store_size_dtyp_float := by
    change Store_size_dtyp (DTYPE_Base (DTYPE_FP FP_float)) = 4
    rw [Store_size_dtyp]; rfl
  store_size_dtyp_double := by
    change Store_size_dtyp (DTYPE_Base (DTYPE_FP FP_double)) = 8
    rw [Store_size_dtyp]; rfl
  store_size_dtyp_ptr_pos := by
    change 0 < Store_size_dtyp (DTYPE_Base DTYPE_Pointer)
    rw [Store_size_dtyp]; decide
  store_size_dtyp_iptr_pos := by
    change 0 < Store_size_dtyp (DTYPE_Base DTYPE_Iptr)
    rw [Store_size_dtyp]; decide
  store_size_dtyp_Struct_alloc := by
    intro ts
    change pad_to (Dtyp_alignment (DTYPE_Struct false ts)).preferred_alignment
      (Store_size_dtyp (DTYPE_Struct false ts)) = Store_size_dtyp (DTYPE_Struct false ts)
    rw [preferred_Dtyp_alignment_Struct, Store_size_dtyp, pad_to_idem]

end Vellvm.Semantics.Implementations.Sizeof
