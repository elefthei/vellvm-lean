import Vellvm.Theory.I2F.I2F_memory.Maps
import Vellvm.Theory.I2F.I2F_memS

namespace Vellvm.Theory.I2F.I2F_memory
open Vellvm Vellvm.Semantics.MemoryBytes Vellvm.Semantics.Interfaces.Memory
open Vellvm.Semantics.Implementations.Memory Vellvm.Utils.IntMaps Vellvm.Utils.RelationsUtil
open Vellvm.Theory.I2F.Refinement Vellvm.Theory.I2F.I2F_exp Vellvm.Theory.I2F.I2F_memS

theorem I2F_get_mem : I2F_memS I2F_State I2F_memory
    (get_mem (Pa := PInf)) (get_mem (Pa := PFin)) := by
  apply I2F_Mget
  intro _ _ h
  exact I2F_Mret _ _ h.i2f_st_ms.i2f_ms_memory

theorem I2F_get_frame_stack : I2F_memS I2F_State I2F_Framestack
    (get_frame_stack (Pa := PInf)) (get_frame_stack (Pa := PFin)) := by
  apply I2F_Mget
  intro _ _ h
  exact I2F_Mret _ _ h.i2f_st_ms.i2f_ms_fs

theorem I2F_get_framestack : I2F_memS I2F_State I2F_Framestack
    (get_framestack (Pa := PInf)) (get_framestack (Pa := PFin)) := by
  exact I2F_get_frame_stack

theorem I2F_get_frame : I2F_memS I2F_State I2F_Frame
    (get_frame (Pa := PInf)) (get_frame (Pa := PFin)) := by
  unfold get_frame
  refine I2F_memS_bind _ _ _ _ _ _ _ I2F_get_frame_stack ?_
  intro s t h
  cases h <;> constructor <;> assumption

theorem I2F_get_heap : I2F_memS I2F_State I2F_Heap
    (get_heap (Pa := PInf)) (get_heap (Pa := PFin)) := by
  apply I2F_Mget
  intro _ _ h
  exact I2F_Mret _ _ h.i2f_st_ms.i2f_ms_heap

theorem I2F_app_mem_stack : ∀ (f1 : @Memory_stack PInf → @Memory_stack PInf) (f2 : @Memory_stack PFin → @Memory_stack PFin),
    (∀ x y, I2F_Memory_stack x y → I2F_Memory_stack (f1 x) (f2 y)) →
    I2F_memS I2F_State (fun (_ _ : Unit) ↦ True)
    (app_mem_stack (Pa := PInf) f1) (app_mem_stack (Pa := PFin) f2) := by
  intro f g hf
  apply I2F_Mget
  intro s t h
  apply I2F_memS_put
  exact ⟨hf _ _ h.i2f_st_ms, h.i2f_st_prov⟩

theorem I2F_app_mem : ∀ (f1 : @memory PInf → @memory PInf) (f2 : @memory PFin → @memory PFin),
    (∀ x y, I2F_memory x y → I2F_memory (f1 x) (f2 y)) →
    I2F_memS I2F_State (fun (_ _ : Unit) ↦ True)
    (app_mem (Pa := PInf) f1) (app_mem (Pa := PFin) f2) := by
  intro f g hf
  unfold app_mem
  apply I2F_app_mem_stack
  intro s t h
  exact ⟨hf _ _ h.i2f_ms_memory, h.i2f_ms_fs, h.i2f_ms_heap⟩

theorem I2F_app_heap : ∀ (f1 : @Heap PInf → @Heap PInf) (f2 : @Heap PFin → @Heap PFin),
    (∀ x y, I2F_Heap x y → I2F_Heap (f1 x) (f2 y)) →
    I2F_memS I2F_State (fun (_ _ : Unit) ↦ True)
    (app_heap (Pa := PInf) f1) (app_heap (Pa := PFin) f2) := by
  intro f g hf
  unfold app_heap
  apply I2F_app_mem_stack
  intro s t h
  exact ⟨h.i2f_ms_memory, h.i2f_ms_fs, hf _ _ h.i2f_ms_heap⟩

theorem I2F_app_frame_stack : ∀ (f1 : @Framestack PInf → @Framestack PInf) (f2 : @Framestack PFin → @Framestack PFin),
    (∀ x y, I2F_Framestack x y → I2F_Framestack (f1 x) (f2 y)) →
    I2F_memS I2F_State (fun (_ _ : Unit) ↦ True)
    (app_frame_stack (Pa := PInf) f1) (app_frame_stack (Pa := PFin) f2) := by
  intro f g hf
  unfold app_frame_stack
  apply I2F_app_mem_stack
  intro s t h
  exact ⟨h.i2f_ms_memory, hf _ _ h.i2f_ms_fs, h.i2f_ms_heap⟩

theorem I2F_upd_mem : ∀ m1 m2, I2F_memory m1 m2 →
    I2F_memS I2F_State (fun (_ _ : Unit) ↦ True)
    (upd_mem (Pa := PInf) m1) (upd_mem (Pa := PFin) m2) := by
  intro x y h
  unfold upd_mem
  exact I2F_app_mem _ _ (fun _ _ _ ↦ h)

theorem I2F_upd_heap : ∀ h1 h2, I2F_Heap h1 h2 →
    I2F_memS I2F_State (fun (_ _ : Unit) ↦ True)
    (upd_heap (Pa := PInf) h1) (upd_heap (Pa := PFin) h2) := by
  intro x y h
  unfold upd_heap
  exact I2F_app_heap _ _ (fun _ _ _ ↦ h)

theorem I2F_upd_frame_stack : ∀ fs1 fs2, I2F_Framestack fs1 fs2 →
    I2F_memS I2F_State (fun (_ _ : Unit) ↦ True)
    (upd_frame_stack (Pa := PInf) fs1) (upd_frame_stack (Pa := PFin) fs2) := by
  intro x y h
  unfold upd_frame_stack
  exact I2F_app_frame_stack _ _ (fun _ _ _ ↦ h)

theorem I2F_pop_frame_stack : ∀ fs1 fs2, I2F_Framestack fs1 fs2 →
    I2F_EOU I2F_Framestack (pop_frame_stack (Pa := PInf) fs1) (pop_frame_stack (Pa := PFin) fs2) := by
  intro s t h
  cases h <;> constructor <;> assumption

theorem I2F_app_frame_stack_eob : I2F_memS I2F_State (fun (_ _ : Unit) ↦ True)
    (app_frame_stack_eob (Pa := PInf) (pop_frame_stack (Pa := PInf))) (app_frame_stack_eob (Pa := PFin) (pop_frame_stack (Pa := PFin))) := by
  unfold app_frame_stack_eob
  refine I2F_memS_bind _ _ _ _ _ _ _ I2F_get_framestack ?_
  intro s t h
  refine I2F_memS_bind _ _ _ _ _ _ _ (I2F_memS_lift _ _ _ _ (I2F_pop_frame_stack s t h)) ?_
  exact I2F_upd_frame_stack

theorem I2F_read_byte_raw : ∀ (msg : IRString) (addr : Int), I2F_memS I2F_State I2F_byte
    (read_byte_raw (Pa := PInf) msg addr) (read_byte_raw (Pa := PFin) msg addr) := by
  intro msg addr
  unfold read_byte_raw read_byte_raw_mem
  refine I2F_memS_bind _ _ _ _ _ _ _ I2F_get_mem ?_
  intro m n h
  have hlookup := IM_Refine_lookup I2F_byte m n h addr
  generalize lookup addr m = x, lookup addr n = y at hlookup ⊢
  cases hlookup <;> constructor <;> assumption

theorem I2F_set_byte_raw : ∀ addr b1 b2, I2F_byte b1 b2 →
    I2F_memS I2F_State (fun (_ _ : Unit) ↦ True)
    (set_byte_raw (Pa := PInf) addr b1) (set_byte_raw (Pa := PFin) addr b2) := by
  intro addr b c hb
  unfold set_byte_raw
  refine I2F_memS_bind _ _ _ _ _ _ _ I2F_get_mem ?_
  intro m n h
  exact I2F_upd_mem _ _ (IM_Refine_add I2F_byte m n addr b c h hb)

theorem I2F_Read_byte : ∀ (p1 : PInf.PTR.ptr) (p2 : PFin.PTR.ptr), I2F_Addr p1 p2 →
    I2F_memS I2F_State I2F_memory_byte
    (Read_byte (Pa := PInf) p1) (Read_byte (Pa := PFin) p2) := by
  intro p q hp
  have hprov : PInf.PTR.ptr_provenance p = PFin.PTR.ptr_provenance q := hp.2
  unfold Read_byte
  dsimp only
  rw [I2F_Addr_ptr_to_int p q hp]
  refine I2F_memS_bind _ _ _ _ _ _ _ (I2F_read_byte_raw _ _) ?_
  rintro ⟨x, a⟩ ⟨y, a'⟩ ⟨hxy, ha⟩
  change a = a' at ha
  subst a'
  dsimp only
  rw [hprov]
  by_cases ok : PFin.PROV.access_allowed (PFin.PTR.ptr_provenance q) a = true
  · simp only [ok, if_true]
    exact I2F_Mret _ _ hxy
  · simp only [ok, if_false]
    constructor

theorem I2F_Write_byte : ∀ (p1 : PInf.PTR.ptr) (p2 : PFin.PTR.ptr), I2F_Addr p1 p2 →
    ∀ b1 b2, I2F_memory_byte b1 b2 →
    I2F_memS I2F_State (fun (_ _ : Unit) ↦ True)
    (Write_byte (Pa := PInf) p1 b1) (Write_byte (Pa := PFin) p2 b2) := by
  intro p q hp b c hbc
  have hprov : PInf.PTR.ptr_provenance p = PFin.PTR.ptr_provenance q := hp.2
  unfold Write_byte
  dsimp only
  rw [I2F_Addr_ptr_to_int p q hp]
  refine I2F_memS_bind _ _ _ _ _ _ _ (I2F_read_byte_raw _ _) ?_
  rintro ⟨x, a⟩ ⟨y, a'⟩ ⟨hxy, ha⟩
  change a = a' at ha
  subst a'
  dsimp only
  rw [hprov]
  by_cases ok : PFin.PROV.access_allowed (PFin.PTR.ptr_provenance q) a = true
  · simp only [ok, if_true]
    exact I2F_set_byte_raw _ _ _ ⟨hbc, rfl⟩
  · simp only [ok, if_false]
    constructor

theorem I2F_get_free_block : ∀ (size align : Nat) (pr : PInf.PROV.provenance),
    I2F_memS I2F_State (prod_rel I2F_Addr (List.Forall₂ I2F_Addr))
    (get_free_block (Pa := PInf) size align pr) (get_free_block (Pa := PFin) size align pr) := by
  intro size align pr
  unfold get_free_block
  refine I2F_memS_bind _ _ _ _ _ _ _ (I2F_memS_next_key _ size align) ?_
  rintro addr _ rfl
  refine I2F_memS_bind _ _ _ _ _ _ _ (I2F_memS_lift _ _ _ _ (I2F_int_to_ptr addr _)) ?_
  intro p q hp
  refine I2F_memS_bind _ _ _ _ _ _ _ (I2F_memS_lift _ _ _ _ (I2F_get_consecutive_ptrs p q hp size)) ?_
  intro ps qs hps
  exact I2F_Mret _ _ ⟨hp, hps⟩

theorem I2F_memory_bytes_to_bytes : ∀ (aid : PInf.PROV.allocationId) (bytes1 : List (@memory_byte PInf)) (bytes2 : List (@memory_byte PFin)),
    List.Forall₂ I2F_memory_byte bytes1 bytes2 → List.Forall₂ I2F_byte
    (memory_bytes_to_bytes (Pa := PInf) aid bytes1) (memory_bytes_to_bytes (Pa := PFin) aid bytes2) := by
  intro aid xs ys h
  induction h with
  | nil => exact .nil
  | cons hxy _ ih => exact .cons ⟨hxy, rfl⟩ ih

theorem I2F_add_block : ∀ (aid : PInf.PROV.allocationId) (p1 : PInf.PTR.ptr) (p2 : PFin.PTR.ptr), I2F_Addr p1 p2 →
    ∀ (ptrs1 : List PInf.PTR.ptr) (ptrs2 : List PFin.PTR.ptr)
      (bytes1 : List (@memory_byte PInf)) (bytes2 : List (@memory_byte PFin)), List.Forall₂ I2F_memory_byte bytes1 bytes2 →
    I2F_memS I2F_State (fun (_ _ : Unit) ↦ True)
    (add_block (Pa := PInf) aid p1 ptrs1 bytes1) (add_block (Pa := PFin) aid p2 ptrs2 bytes2) := by
  intro aid p q hp ps qs xs ys hxy
  unfold add_block
  rw [I2F_Addr_ptr_to_int p q hp]
  refine I2F_memS_bind _ _ _ _ _ _ _ I2F_get_mem ?_
  intro m n h
  exact I2F_upd_mem _ _ (IM_Refine_add_all_index_acc I2F_byte _ _ _ m n
    (I2F_memory_bytes_to_bytes aid xs ys hxy) h)

theorem I2F_add_ptrs_to_frame : ∀ (ptrs1 : List PInf.PTR.ptr) (ptrs2 : List PFin.PTR.ptr),
    List.Forall₂ I2F_Addr ptrs1 ptrs2 →
    I2F_memS I2F_State (fun (_ _ : Unit) ↦ True)
    (add_ptrs_to_frame (Pa := PInf) ptrs1) (add_ptrs_to_frame (Pa := PFin) ptrs2) := by
  intro ps qs h
  exact I2F_app_mem_stack _ _ (I2F_add_all_to_frame ps qs h)

theorem I2F_add_ptrs_to_heap : ∀ (ptrs1 : List PInf.PTR.ptr) (ptrs2 : List PFin.PTR.ptr),
    List.Forall₂ I2F_Addr ptrs1 ptrs2 →
    I2F_memS I2F_State (fun (_ _ : Unit) ↦ True)
    (add_ptrs_to_heap (Pa := PInf) ptrs1) (add_ptrs_to_heap (Pa := PFin) ptrs2) := by
  intro ps qs h
  exact I2F_app_mem_stack _ _ (I2F_add_all_to_heap ps qs h)

theorem I2F_add_block_to_stack : ∀ (aid : PInf.PROV.allocationId) (p1 : PInf.PTR.ptr) (p2 : PFin.PTR.ptr), I2F_Addr p1 p2 →
    ∀ (ptrs1 : List PInf.PTR.ptr) (ptrs2 : List PFin.PTR.ptr), List.Forall₂ I2F_Addr ptrs1 ptrs2 →
    ∀ (bytes1 : List (@memory_byte PInf)) (bytes2 : List (@memory_byte PFin)), List.Forall₂ I2F_memory_byte bytes1 bytes2 →
    I2F_memS I2F_State (fun (_ _ : Unit) ↦ True)
    (add_block_to_stack (Pa := PInf) aid p1 ptrs1 bytes1) (add_block_to_stack (Pa := PFin) aid p2 ptrs2 bytes2) := by
  intro aid p q hp ps qs hps xs ys hxy
  unfold add_block_to_stack
  refine I2F_memS_bind _ _ _ _ _ _ _ (I2F_add_block aid p q hp ps qs xs ys hxy) ?_
  exact fun _ _ _ ↦ I2F_add_ptrs_to_frame ps qs hps

theorem I2F_add_block_to_heap : ∀ (aid : PInf.PROV.allocationId) (p1 : PInf.PTR.ptr) (p2 : PFin.PTR.ptr), I2F_Addr p1 p2 →
    ∀ (ptrs1 : List PInf.PTR.ptr) (ptrs2 : List PFin.PTR.ptr), List.Forall₂ I2F_Addr ptrs1 ptrs2 →
    ∀ (bytes1 : List (@memory_byte PInf)) (bytes2 : List (@memory_byte PFin)), List.Forall₂ I2F_memory_byte bytes1 bytes2 →
    I2F_memS I2F_State (fun (_ _ : Unit) ↦ True)
    (add_block_to_heap (Pa := PInf) aid p1 ptrs1 bytes1) (add_block_to_heap (Pa := PFin) aid p2 ptrs2 bytes2) := by
  intro aid p q hp ps qs hps xs ys hxy
  unfold add_block_to_heap
  refine I2F_memS_bind _ _ _ _ _ _ _ (I2F_add_block aid p q hp ps qs xs ys hxy) ?_
  exact fun _ _ _ ↦ I2F_add_ptrs_to_heap ps qs hps

theorem I2F_Allocate_bytes_with_pr : ∀ (bytes1 : List (@memory_byte PInf)) (bytes2 : List (@memory_byte PFin)),
    List.Forall₂ I2F_memory_byte bytes1 bytes2 → ∀ (align : Nat) (pr : PInf.PROV.provenance),
    I2F_memS I2F_State I2F_Addr
    (Allocate_bytes_with_pr (Pa := PInf) bytes1 align pr) (Allocate_bytes_with_pr (Pa := PFin) bytes2 align pr) := by
  intro xs ys hxy align pr
  unfold Allocate_bytes_with_pr
  rw [hxy.length_eq]
  refine I2F_memS_bind _ _ _ _ _ _ _ (I2F_get_free_block ys.length align pr) ?_
  rintro ⟨p, ps⟩ ⟨q, qs⟩ ⟨hp, hps⟩
  refine I2F_memS_bind _ _ _ _ _ _ _ (I2F_add_block_to_stack _ p q hp ps qs hps xs ys hxy) ?_
  exact fun _ _ _ ↦ I2F_Mret _ _ hp

theorem I2F_Malloc_bytes_with_pr : ∀ (bytes1 : List (@memory_byte PInf)) (bytes2 : List (@memory_byte PFin)),
    List.Forall₂ I2F_memory_byte bytes1 bytes2 → ∀ (align : Nat) (pr : PInf.PROV.provenance),
    I2F_memS I2F_State I2F_Addr
    (Malloc_bytes_with_pr (Pa := PInf) bytes1 align pr) (Malloc_bytes_with_pr (Pa := PFin) bytes2 align pr) := by
  intro xs ys hxy align pr
  unfold Malloc_bytes_with_pr
  rw [hxy.length_eq]
  refine I2F_memS_bind _ _ _ _ _ _ _ (I2F_get_free_block ys.length align pr) ?_
  rintro ⟨p, ps⟩ ⟨q, qs⟩ ⟨hp, hps⟩
  refine I2F_memS_bind _ _ _ _ _ _ _ (I2F_add_block_to_heap _ p q hp ps qs hps xs ys hxy) ?_
  exact fun _ _ _ ↦ I2F_Mret _ _ hp

theorem I2F_push_frame_stack : ∀ (f1 : @Frame PInf) (f2 : @Frame PFin), I2F_Frame f1 f2 →
    ∀ fs1 fs2, I2F_Framestack fs1 fs2 →
    I2F_Framestack (push_frame_stack (Pa := PInf) f1 fs1) (push_frame_stack (Pa := PFin) f2 fs2) := by
  intro f g h s t hs
  constructor <;> assumption

theorem I2F_Mempush : I2F_memS I2F_State (fun (_ _ : Unit) ↦ True)
    (Mempush (Pa := PInf)) (Mempush (Pa := PFin)) := by
  apply I2F_app_frame_stack
  exact I2F_push_frame_stack [] [] .nil

theorem I2F_Mempop : I2F_memS I2F_State (fun (_ _ : Unit) ↦ True)
    (Mempop (Pa := PInf)) (Mempop (Pa := PFin)) := by
  unfold Mempop
  refine I2F_memS_bind _ _ _ _ _ _ _ I2F_get_frame ?_
  intro f g hf
  refine I2F_memS_bind _ _ _ _ _ _ _ I2F_app_frame_stack_eob ?_
  exact fun _ _ _ ↦ I2F_app_mem _ _ (I2F_free_frame_memory f g hf)

theorem I2F_Free : ∀ (p1 : PInf.PTR.ptr) (p2 : PFin.PTR.ptr), I2F_Addr p1 p2 →
    I2F_memS I2F_State (fun (_ _ : Unit) ↦ True)
    (Free (Pa := PInf) p1) (Free (Pa := PFin) p2) := by
  intro p q hp
  unfold Free
  dsimp only
  rw [I2F_Addr_ptr_to_int p q hp]
  refine I2F_memS_bind _ _ _ _ _ _ _ I2F_get_heap ?_
  intro m n h
  have hlookup := IM_Refine_lookup (List.Forall₂ I2F_Addr) m n h (PFin.P2I.ptr_to_int q)
  generalize lookup (PFin.P2I.ptr_to_int q) m = x, lookup (PFin.P2I.ptr_to_int q) n = y at hlookup ⊢
  cases hlookup with
  | none => constructor
  | some b c hbc =>
    refine I2F_memS_bind _ _ _ _ _ _ _ (I2F_app_mem _ _ (I2F_free_block_memory b c hbc)) ?_
    exact fun _ _ _ ↦ I2F_upd_heap _ _ (IM_Refine_remove _ m n _ h)

end Vellvm.Theory.I2F.I2F_memory
