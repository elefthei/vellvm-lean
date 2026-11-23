import Vellvm.Theory.I2F.I2F_memory.Transfers
import Vellvm.Theory.I2F.I2F_exp.Values
import Vellvm.Semantics.Handlers.Memory
import Vellvm.Theory.I2F.Refinement.Events

namespace Vellvm.Theory.I2F.I2F_memory
open Vellvm.Semantics.DynamicValues Vellvm.Semantics.Implementations.Memory
open Vellvm.Semantics.MemoryBytes
open Vellvm.Semantics.LLVMEvents Vellvm.Theory.I2F.Refinement
open Vellvm.Theory.I2F.I2F_memS
open Vellvm.Theory.I2F.I2F_exp

theorem I2F_memcpy (s d : PInf.PTR.ptr) (s' d' : PFin.PTR.ptr)
    (hs : I2F_Addr s s') (hd : I2F_Addr d d') (size : Nat) (vol : Bool) :
    I2F_memS I2F_State (fun (_ _ : Unit) ↦ True)
      (@memcpy PInf (@MemoryModelPrimitivesV PInf) s d size vol)
      (@memcpy PFin (@MemoryModelPrimitivesV PFin) s' d' size vol) := by
  unfold memcpy
  rw [I2F_no_overlap d s size d' s' size hd hs, I2F_Addr_ptr_to_int _ _ hs,
    I2F_Addr_ptr_to_int _ _ hd]
  split <;> rename_i hc <;> try simp only [hc, if_true, if_false]
  · exact I2F_memS_bind _ _ _ _ _ _ _ (I2F_read_bytes _ _ hs size) (I2F_write_bytes _ _ hd)
  · apply I2F_Mub_l

theorem I2F_memmove (s d : PInf.PTR.ptr) (s' d' : PFin.PTR.ptr)
    (hs : I2F_Addr s s') (hd : I2F_Addr d d') (size : Nat) (vol : Bool) :
    I2F_memS I2F_State (fun (_ _ : Unit) ↦ True)
      (@memmove PInf (@MemoryModelPrimitivesV PInf) s d size vol)
      (@memmove PFin (@MemoryModelPrimitivesV PFin) s' d' size vol) := by
  exact I2F_memS_bind _ _ _ _ _ _ _ (I2F_read_bytes _ _ hs size) (I2F_write_bytes _ _ hd)

theorem I2F_memset (d : PInf.PTR.ptr) (d' : PFin.PTR.ptr)
    (hd : I2F_Addr d d') (x : @memory_byte PInf) (y : @memory_byte PFin)
    (h : I2F_memory_byte x y) (size : Nat) (vol : Bool) :
    I2F_memS I2F_State (fun (_ _ : Unit) ↦ True)
      (@memset PInf (@MemoryModelPrimitivesV PInf) d x size vol)
      (@memset PFin (@MemoryModelPrimitivesV PFin) d' y size vol) := by
  apply I2F_write_bytes _ _ hd
  induction size with
  | zero => exact .nil
  | succ n ih => exact .cons h ih

theorem I2F_malloc_bytes (xs : List (@memory_byte PInf)) (ys : List (@memory_byte PFin))
    (h : List.Forall₂ I2F_memory_byte xs ys) (align : Nat) :
    I2F_memS I2F_State I2F_Addr
      (@malloc_bytes PInf (@MemoryModelPrimitivesV PInf) xs align)
      (@malloc_bytes PFin (@MemoryModelPrimitivesV PFin) ys align) := by
  unfold malloc_bytes
  apply I2F_memS_bind _ Eq _ _ _ _ _ (I2F_memS_fresh_prov _)
  rintro pr _ rfl
  exact I2F_Malloc_bytes_with_pr xs ys h align pr

theorem I2F_handle_memtransfer (overlap : Bool) (xs : List (@dvalue_base PInf)) (ys : List (@dvalue_base PFin))
    (h : List.Forall₂ I2F_dvalue_base xs ys) :
    I2F_memS I2F_State (fun (_ _ : Unit) ↦ True)
      (@handle_memtransfer PInf (@MemoryModelPrimitivesV PInf) overlap xs)
      (@handle_memtransfer PFin (@MemoryModelPrimitivesV PFin) overlap ys) := by
  rcases h with _ | ⟨hd, h⟩ <;> try apply I2F_Merr
  rcases h with _ | ⟨hv, h⟩ <;> try apply I2F_Merr
  rcases h with _ | ⟨hn, h⟩ <;> try apply I2F_Merr
  rcases h with _ | ⟨hvol, h⟩ <;> try apply I2F_Merr
  cases h <;> cases hvol <;> try apply I2F_Merr
  cases hn <;> first | apply I2F_Merr | apply I2F_Mub_l | skip
  all_goals try (rename_i hp; unfold I2F_Iptr at hp; subst_vars)
  all_goals cases hd <;> cases hv <;> try apply I2F_Merr
  all_goals simp only [handle_memtransfer, pure, Bind.bind, Semantics.Interfaces.Memory.memS_bind]; split <;> rename_i hc
  all_goals first
    | exact I2F_memcpy _ _ _ _ (by assumption) (by assumption) _ _
    | exact I2F_memmove _ _ _ _ (by assumption) (by assumption) _ _
    | exact .I2F_Mret _ _ trivial
    | apply I2F_Mub_l
    | rw [if_pos (by exact hc)]; exact .I2F_Mret _ _ trivial

theorem I2F_handle_memcpy (xs : List (@dvalue_base PInf)) (ys : List (@dvalue_base PFin))
    (h : List.Forall₂ I2F_dvalue_base xs ys) :
    I2F_memS I2F_State (fun (_ _ : Unit) ↦ True)
      (@handle_memcpy PInf (@MemoryModelPrimitivesV PInf) xs)
      (@handle_memcpy PFin (@MemoryModelPrimitivesV PFin) ys) := by
  exact I2F_handle_memtransfer false xs ys h

theorem I2F_handle_memmove (xs : List (@dvalue_base PInf)) (ys : List (@dvalue_base PFin))
    (h : List.Forall₂ I2F_dvalue_base xs ys) :
    I2F_memS I2F_State (fun (_ _ : Unit) ↦ True)
      (@handle_memmove PInf (@MemoryModelPrimitivesV PInf) xs)
      (@handle_memmove PFin (@MemoryModelPrimitivesV PFin) ys) := by
  exact I2F_handle_memtransfer true xs ys h

theorem I2F_handle_memset (xs : List (@dvalue_base PInf)) (ys : List (@dvalue_base PFin))
    (h : List.Forall₂ I2F_dvalue_base xs ys) :
    I2F_memS I2F_State (fun (_ _ : Unit) ↦ True)
      (@handle_memset PInf (@MemoryModelPrimitivesV PInf) xs)
      (@handle_memset PFin (@MemoryModelPrimitivesV PFin) ys) := by
  rcases h with _ | ⟨hd, h⟩ <;> try apply I2F_Merr
  rcases h with _ | ⟨hv, h⟩ <;> try apply I2F_Merr
  rcases h with _ | ⟨hn, h⟩ <;> try apply I2F_Merr
  rcases h with _ | ⟨hvol, h⟩ <;> try apply I2F_Merr
  cases h <;> cases hvol <;> try apply I2F_Merr
  cases hv <;> first | apply I2F_Merr | skip
  case' I2F_dvalue_Int sz v =>
    by_cases h8 : (sz.val == 8) = true <;> simp only [handle_memset, h8, if_true, if_false] <;>
      try apply I2F_Merr
  all_goals cases hn <;> first | apply I2F_Merr | apply I2F_Mub_l | skip
  all_goals cases hd <;> first | apply I2F_Merr | skip
  all_goals simp only [handle_memset, pure, Bind.bind, Semantics.Interfaces.Memory.memS_bind]
  all_goals first
    | exact I2F_memset _ _ (by assumption) _ _ (I2F_BYTE_I _) _ _
    | exact I2F_memset _ _ (by assumption) _ _ (I2F_BYTE_Mixed (by repeat constructor)) _ _
    | split <;> first | exact .I2F_Mret _ _ trivial | apply I2F_Mub_l

theorem I2F_handle_malloc (xs : List (@dvalue_base PInf)) (ys : List (@dvalue_base PFin))
    (h : List.Forall₂ I2F_dvalue_base xs ys) (align : Nat) :
    I2F_memS I2F_State I2F_Addr
      (@handle_malloc PInf (@MemoryModelPrimitivesV PInf) xs align)
      (@handle_malloc PFin (@MemoryModelPrimitivesV PFin) ys align) := by
  rcases h with _ | ⟨hv, h⟩ <;> try apply I2F_Merr
  cases h <;> cases hv <;> try apply I2F_Merr
  · exact I2F_malloc_bytes _ _ (I2F_generate_num_poison_bytes _) align
  · rename_i hp
    unfold I2F_Iptr at hp
    subst_vars
    exact I2F_malloc_bytes _ _ (I2F_generate_num_poison_bytes _) align

theorem I2F_handle_free (xs : List (@dvalue_base PInf)) (ys : List (@dvalue_base PFin))
    (h : List.Forall₂ I2F_dvalue_base xs ys) :
    I2F_memS I2F_State (fun (_ _ : Unit) ↦ True)
      (@handle_free PInf (@MemoryModelPrimitivesV PInf) xs)
      (@handle_free PFin (@MemoryModelPrimitivesV PFin) ys) := by
  rcases h with _ | ⟨hv, h⟩ <;> try apply I2F_Merr
  cases h <;> cases hv <;> first | apply I2F_Merr | apply I2F_Mub_l | skip
  rename_i hp
  simp only [handle_free, I2F_Addr_ptr_to_int _ _ hp]
  split <;> rename_i hc
  · first | exact .I2F_Mret _ _ trivial | rw [if_pos (by exact hc)]; apply I2F_Mret; trivial
  · first | exact I2F_Free _ _ hp | rw [if_neg (by exact hc)]; exact I2F_Free _ _ hp

private theorem intrinsicArgs {xs ys} (h : I2F_targs xs ys)
    (acc : List (@dvalue_base PInf)) (acc' : List (@dvalue_base PFin))
    (ha : List.Forall₂ I2F_dvalue_base acc acc') : I2F_EOU (List.Forall₂ I2F_dvalue_base)
      (List.mapM.loop (fun a ↦ @dvalue_to_dvalue_base PInf a.2) xs acc)
      (List.mapM.loop (fun a ↦ @dvalue_to_dvalue_base PFin a.2) ys acc') := by
  induction h generalizing acc acc' with
  | nil => exact I2F_EOU_ret _ _ (List.forall₂_reverse_iff.mpr ha)
  | cons hab _ ih =>
    exact I2F_EOU_bind _ _ (I2F_dvalue_to_dvalue_base hab.2)
      (fun a b hr ↦ ih (a :: acc) (b :: acc') (.cons hr ha))

theorem I2F_handle_intrinsicM (e : @IntrinsicRequest PInf) (e' : @IntrinsicRequest PFin)
    (h : I2FE_Intrinsic e e') :
    I2F_memS I2F_State (fun x y ↦ I2FA_Intrinsic e x e' y)
      (@handle_intrinsicM PInf (@MemoryModelPrimitivesV PInf) e)
      (@handle_intrinsicM PFin (@MemoryModelPrimitivesV PFin) e') := by
  rcases e with ⟨t, name, args, va⟩
  rcases e' with ⟨t', name', args', va'⟩
  rcases h with ⟨ht, hf, ha, _⟩
  subst t'; subst name'
  unfold handle_intrinsicM
  apply I2F_memS_bind _ (List.Forall₂ I2F_dvalue_base) _ _ _ _ _
  · apply I2F_memS_lift
    exact intrinsicArgs ha [] [] .nil
  · intro xs ys hxy
    cases he : Vellvm.Semantics.IntrinsicsDefinitions.lookup_intrinsic name with
    | none => apply I2F_Merr
    | some tag =>
      cases tag <;> first
        | apply I2F_Merr
        | apply I2F_memS_bind _ _ _ _ _ _ _ (I2F_handle_memcpy xs ys hxy)
        | apply I2F_memS_bind _ _ _ _ _ _ _ (I2F_handle_memmove xs ys hxy)
        | apply I2F_memS_bind _ _ _ _ _ _ _ (I2F_handle_memset xs ys hxy)
        | apply I2F_memS_bind _ _ _ _ _ _ _ (I2F_handle_malloc xs ys hxy 8)
        | apply I2F_memS_bind _ _ _ _ _ _ _ (I2F_handle_free xs ys hxy)
      all_goals intro x y hr; apply I2F_Mret; constructor; constructor; constructor <;> assumption

end Vellvm.Theory.I2F.I2F_memory
