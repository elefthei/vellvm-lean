import Vellvm.Theory.I2F.I2F_memory.Address
import Vellvm.Theory.I2F.I2F_memory.State
import Vellvm.Semantics.Implementations.Memory.Primitives
import Vellvm.Semantics.Handlers.Memory.Allocation

namespace Vellvm.Theory.I2F.I2F_memory
open Refinement Semantics.Implementations.Memory Semantics.Handlers.Memory Utils.IntMaps

theorem I2F_next_key_with_alignment (m1 m2) (h : I2F_memory m1 m2) (align : Nat) :
    next_key_with_alignment m1 align = next_key_with_alignment m2 align := by
  unfold next_key_with_alignment
  rw [IM_greatest_key_morph m1 m2 h.1]

theorem I2F_free_frame_memory (f g) (hf : I2F_Frame f g) : ∀ m n, I2F_memory m n →
    I2F_memory (@free_frame_memory PInf f m) (@free_frame_memory PFin g n) := by
  induction hf with
  | nil => exact fun _ _ h ↦ h
  | @cons p q _ _ hp _ ih =>
    intro m n h
    apply ih
    change IM_Refine I2F_byte (delete (PInf.P2I.ptr_to_int p) m) (delete (PFin.P2I.ptr_to_int q) n)
    rw [I2F_Addr_ptr_to_int p q hp]
    exact IM_Refine_remove _ m n _ h

theorem I2F_free_block_memory (f g) (h : List.Forall₂ I2F_Addr f g) : ∀ m n, I2F_memory m n →
    I2F_memory (@free_block_memory PInf f m) (@free_block_memory PFin g n) :=
  I2F_free_frame_memory f g h

theorem I2F_add_to_frame (m n) (hm : I2F_Memory_stack m n) (p q) (hp : I2F_Addr p q) :
    I2F_Memory_stack (@add_to_frame PInf m p) (@add_to_frame PFin n q) := by
  rcases m with ⟨m, s, h⟩
  rcases n with ⟨n, t, h'⟩
  obtain ⟨hm, hs, hh⟩ := hm
  change I2F_Framestack s t at hs
  cases hs with
  | I2F_FS_Singleton hf => exact ⟨hm, .I2F_FS_Singleton (.cons hp hf), hh⟩
  | I2F_FS_Snoc hs hf => exact ⟨hm, .I2F_FS_Snoc hs (.cons hp hf), hh⟩

theorem I2F_add_all_to_frame (ps qs) (h : List.Forall₂ I2F_Addr ps qs) :
    ∀ m n, I2F_Memory_stack m n → I2F_Memory_stack (@add_all_to_frame PInf ps m) (@add_all_to_frame PFin qs n) := by
  induction h with
  | nil => exact fun _ _ h ↦ h
  | cons hp _ ih => exact fun m n hm ↦ ih _ _ (I2F_add_to_frame m n hm _ _ hp)

theorem I2F_add_to_heap (m n) (hm : I2F_Memory_stack m n) (r s) (hr : I2F_Addr r s)
    (p q) (hp : I2F_Addr p q) : I2F_Memory_stack (@add_to_heap PInf m r p) (@add_to_heap PFin n s q) := by
  refine ⟨hm.i2f_ms_memory, hm.i2f_ms_fs, ?_⟩
  change IM_Refine (List.Forall₂ I2F_Addr)
    (add_with (PInf.P2I.ptr_to_int r) p _ _ (@Memory_stack_heap PInf m))
    (add_with (PFin.P2I.ptr_to_int s) q _ _ (@Memory_stack_heap PFin n))
  rw [I2F_Addr_ptr_to_int r s hr]
  unfold add_with
  apply IM_Refine_add _ _ _ _ _ _ hm.i2f_ms_heap
  have h := IM_Refine_lookup _ _ _ hm.i2f_ms_heap (PFin.P2I.ptr_to_int s)
  generalize lookup (PFin.P2I.ptr_to_int s) (@Memory_stack_heap PInf m) = xs,
    lookup (PFin.P2I.ptr_to_int s) (@Memory_stack_heap PFin n) = ys at h ⊢
  cases h with
  | none => exact .cons hp .nil
  | some _ _ h => exact .cons hp h

theorem I2F_add_all_to_heap' (m n) (hm : I2F_Memory_stack m n) (r s) (hr : I2F_Addr r s)
    (ps qs) (h : List.Forall₂ I2F_Addr ps qs) :
    I2F_Memory_stack (@add_all_to_heap' PInf m r ps) (@add_all_to_heap' PFin n s qs) := by
  induction h generalizing m n with
  | nil => exact hm
  | cons hp _ ih => exact ih _ _ (I2F_add_to_heap m n hm r s hr _ _ hp)

theorem I2F_add_all_to_heap (ps qs) (h : List.Forall₂ I2F_Addr ps qs) :
    ∀ m n, I2F_Memory_stack m n → I2F_Memory_stack (@add_all_to_heap PInf ps m) (@add_all_to_heap PFin qs n) := by
  cases h with
  | nil => exact fun _ _ h ↦ h
  | cons hp ht => exact fun m n hm ↦ I2F_add_all_to_heap' m n hm _ _ hp _ _ (.cons hp ht)

end Vellvm.Theory.I2F.I2F_memory
