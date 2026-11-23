import Vellvm.Theory.I2F.I2F_exp.BytesAddress
import Vellvm.Theory.I2F.I2F_exp.MemoryByte
import Vellvm.Theory.I2F.Refinement.EOU
import Vellvm.Semantics.Implementations.Memory.Bytes
import Vellvm.Semantics.DynamicValues.Arithmetic

namespace Vellvm.Theory.I2F.I2F_memory
open Refinement I2F_exp Semantics.Interfaces.Params Semantics.Interfaces.Pointer
open Semantics.Interfaces.IPtr Semantics.Implementations.Memory Semantics.DynamicValues
open Semantics.MemoryBytes Semantics.EOU Syntax.DynamicTypes Numeric.Integers Utils.ListUtil

theorem I2F_Addr_ptr_to_int (p : PInf.PTR.ptr) (q : PFin.PTR.ptr) (hp : I2F_Addr p q) :
    PInf.P2I.ptr_to_int p = PFin.P2I.ptr_to_int q := hp.1

theorem I2F_intptr_seq (start size : Nat) : I2F_EOU (List.Forall₂ I2F_Iptr)
    (@intptr_seq PInf.IPTR start size) (@intptr_seq PFin.IPTR start size) := by
  simp only [intptr_seq, seq_map_monad_acc_eq]
  exact I2F_EOU_map_monad _ _ _ fun a _ ↦ I2F_from_Z (Int.ofNat a)

theorem I2F_ptr_byte_offset (p : PInf.PTR.ptr) (q : PFin.PTR.ptr)
    (i : PInf.IPTR.iptr) (j : PFin.IPTR.iptr) (hp : I2F_Addr p q) (hi : I2F_Iptr i j) :
    I2F_EOU I2F_Addr (@ptr_byte_offset PInf p i) (@ptr_byte_offset PFin q j) := by
  rcases p with ⟨x, pr⟩
  rcases q with ⟨y, pr'⟩
  change x = unsigned y ∧ pr = pr' at hp
  change i = unsigned j at hi
  obtain ⟨rfl, rfl⟩ := hp
  subst i
  exact I2F_int_to_ptr _ _

theorem I2F_get_consecutive_ptrs (p : PInf.PTR.ptr) (q : PFin.PTR.ptr)
    (hp : I2F_Addr p q) (n : Nat) : I2F_EOU (List.Forall₂ I2F_Addr)
    (@get_consecutive_ptrs PInf p n) (@get_consecutive_ptrs PFin q n) := by
  refine I2F_EOU_bind (map_monad_acc (@ptr_byte_offset PInf p))
    (map_monad_acc (@ptr_byte_offset PFin q)) (I2F_intptr_seq 0 n) fun _ _ h ↦ ?_
  exact I2F_EOU_map_monad_acc2 _ _ h fun i j hij ↦ I2F_ptr_byte_offset p q i j hp hij

theorem I2F_coerce_integer_to_int (b : Option Positive) (z : Int) : I2F_EOU I2F_dvalue_base
    (@coerce_integer_to_int PInf b z) (@coerce_integer_to_int PFin b z) := by
  cases b with
  | some w => exact .I2F_EOU_ret _ _ (.I2F_dvalue_Int _)
  | none =>
    exact I2F_EOU_bind (fun i ↦ raise_ret (@DVALUE_Iptr PInf i))
      (fun j ↦ raise_ret (@DVALUE_Iptr PFin j)) (I2F_from_Z z)
      fun _ _ hij ↦ .I2F_EOU_ret _ _ (.I2F_dvalue_Ptr hij)

theorem I2F_no_overlap (a b : PInf.PTR.ptr) (n : Nat) (a' b' : PFin.PTR.ptr) (m : Nat)
    (ha : I2F_Addr a a') (hb : I2F_Addr b b') :
    @no_overlap PInf.PROV PInf.PTR (@overlaps_ptoi PInf.PROV PInf.PTR PInf.P2I) a n b m =
      @no_overlap PFin.PROV PFin.PTR (@overlaps_ptoi PFin.PROV PFin.PTR PFin.P2I) a' n b' m := by
  let apart (x y : Int) := !(decide (x ≤ y + Int.ofNat m - 1) && decide (y ≤ x + Int.ofNat n - 1))
  change apart (PInf.P2I.ptr_to_int a) (PInf.P2I.ptr_to_int b) =
    apart (PFin.P2I.ptr_to_int a') (PFin.P2I.ptr_to_int b')
  rw [I2F_Addr_ptr_to_int a a' ha, I2F_Addr_ptr_to_int b b' hb]

theorem generate_num_poison_bytes_h_0 {Pa : Params} (start : Nat) :
    @generate_num_poison_bytes_h Pa start 0 = [] := rfl

theorem generate_num_poison_bytes_h_succ {Pa : Params} (start num : Nat) :
    @generate_num_poison_bytes_h Pa start num.succ =
      @poison_memory_byte Pa :: @generate_num_poison_bytes_h Pa start.succ num :=
  List.replicate_succ ..

theorem I2F_generate_num_poison_bytes_h (start num : Nat) : List.Forall₂ I2F_memory_byte
    (@generate_num_poison_bytes_h PInf start num) (@generate_num_poison_bytes_h PFin start num) := by
  induction num generalizing start with
  | zero => exact .nil
  | succ n ih =>
    rw [generate_num_poison_bytes_h_succ, generate_num_poison_bytes_h_succ]
    refine .cons (.I2F_BYTE_Mixed ?_) (ih start.succ)
    repeat constructor

theorem I2F_generate_num_poison_bytes (num : Nat) : List.Forall₂ I2F_memory_byte
    (@generate_num_poison_bytes PInf num) (@generate_num_poison_bytes PFin num) :=
  I2F_generate_num_poison_bytes_h 0 num

theorem I2F_generate_poison_bytes (dt : dtyp) : List.Forall₂ I2F_memory_byte
    (@generate_poison_bytes PInf dt) (@generate_poison_bytes PFin dt) :=
  I2F_generate_num_poison_bytes (PInf.SIZE.store_size_dtyp dt)

end Vellvm.Theory.I2F.I2F_memory
