import Vellvm.Theory.I2F.I2F_memory.Primitives

namespace Vellvm.Theory.I2F.I2F_memory
open Refinement I2F_exp I2F_memS Semantics.Implementations.Memory Semantics.MemoryBytes
open Utils.ListUtil

theorem I2F_read_bytes (p : PInf.PTR.ptr) (q : PFin.PTR.ptr) (hp : I2F_Addr p q) (n : Nat) :
    I2F_memS I2F_State (List.Forall₂ I2F_memory_byte) (read_bytes (Pa := PInf) p n)
      (read_bytes (Pa := PFin) q n) := by
  unfold read_bytes
  refine I2F_memS_bind _ _ _ _ _ _ _ (I2F_memS_lift _ _ _ _ (I2F_get_consecutive_ptrs p q hp n)) ?_
  intro ps qs hps
  exact I2F_memS_map_monad_acc2 _ _ _ _ _ ps qs hps I2F_Read_byte

theorem I2F_write_bytes (p : PInf.PTR.ptr) (q : PFin.PTR.ptr) (hp : I2F_Addr p q)
    (xs : List (@memory_byte PInf)) (ys : List (@memory_byte PFin))
    (h : List.Forall₂ I2F_memory_byte xs ys) :
    I2F_memS I2F_State (fun (_ _ : Unit) ↦ True) (write_bytes (Pa := PInf) p xs)
      (write_bytes (Pa := PFin) q ys) := by
  unfold write_bytes
  rw [h.length_eq]
  refine I2F_memS_bind _ _ _ _ _ _ _ (I2F_memS_lift _ _ _ _ (I2F_get_consecutive_ptrs p q hp _)) ?_
  intro ps qs hps
  simp only [zip_acc_eq]
  apply I2F_memS_loop_monad2 _ _ _ _ _ _ (Forall2_zip _ _ ps qs hps xs ys h)
  intro ⟨a, x⟩ ⟨b, y⟩ hab
  exact I2F_Write_byte a b hab.1 x y hab.2

end Vellvm.Theory.I2F.I2F_memory
