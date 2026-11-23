import Vellvm.Theory.I2F.I2F_memory.Transfers
import Vellvm.Theory.I2F.I2F_exp
import Vellvm.Theory.I2F.Refinement.Events
import Vellvm.Semantics.Implementations.Memory.Conversion
import Vellvm.Semantics.Handlers.Memory

namespace Vellvm.Theory.I2F.I2F_memory
open Refinement I2F_exp I2F_memS
open Semantics Semantics.DynamicValues Semantics.MemoryBytes Semantics.LLVMEvents
open Interfaces.Memory Implementations.Memory Operations.Conversion Syntax.DynamicTypes Syntax.LLVMAst
open Utils.ListUtil

theorem I2F_read_dvalue (p : PInf.PTR.ptr) (q : PFin.PTR.ptr) (hp : I2F_Addr p q) (dt : dtyp) :
    I2F_memS I2F_State I2F_dvalue (read_dvalue (Pa := PInf) dt p) (read_dvalue (Pa := PFin) dt q) := by
  unfold read_dvalue
  refine I2F_memS_bind _ _ _ _ _ _ _ (I2F_read_bytes p q hp _) ?_
  intro xs ys h
  exact I2F_memS_lift _ _ _ _ (@I2F_memory_bytes_to_dvalue dt xs ys h)

theorem I2F_write_dvalue (p : PInf.PTR.ptr) (q : PFin.PTR.ptr) (hp : I2F_Addr p q) (dt : dtyp)
    (v : @dvalue PInf) (w : @dvalue PFin) (h : I2F_dvalue v w) :
    I2F_memS I2F_State (fun (_ _ : Unit) ↦ True) (write_dvalue (Pa := PInf) p dt v)
      (write_dvalue (Pa := PFin) q dt w) := by
  unfold write_dvalue
  exact I2F_memS_bind _ _ _ _ _ _ _
    (I2F_memS_lift _ _ _ _ (@I2F_memory_dvalue_to_memory_bytes dt v w h none))
    (I2F_write_bytes p q hp)

theorem I2F_allocate_bytes (xs : List (@memory_byte PInf)) (ys : List (@memory_byte PFin))
    (h : List.Forall₂ I2F_memory_byte xs ys) (align : Nat) :
    I2F_memS I2F_State I2F_Addr (allocate_bytes (Pa := PInf) xs align)
      (allocate_bytes (Pa := PFin) ys align) := by
  unfold allocate_bytes
  refine I2F_memS_bind _ _ _ _ _ _ _ (I2F_memS_fresh_prov _) ?_
  intro pr _ heq
  cases heq
  exact I2F_Allocate_bytes_with_pr xs ys h align pr

theorem I2F_allocate_dtyp (dt : dtyp) (n align : Nat) :
    I2F_memS I2F_State I2F_Addr (allocate_dtyp (Pa := PInf) dt n align)
      (allocate_dtyp (Pa := PFin) dt n align) := by
  unfold allocate_dtyp
  split
  · exact .I2F_Mub_l _ _
  · exact I2F_allocate_bytes _ _ (I2F_generate_num_poison_bytes _) align

theorem I2F_assert_inttoptr_types_ok (t u : dtyp_base) :
    I2F_memS I2F_State (fun (_ _ : Unit) ↦ True) (assert_inttoptr_types_ok (Pa := PInf) t u)
      (assert_inttoptr_types_ok (Pa := PFin) t u) := by
  cases t <;> cases u <;> first | exact .I2F_Mub_l _ _ | exact .I2F_Mret _ _ trivial

theorem I2F_convert_impure_base (c : impure_conversion) (t u : dtyp_base)
    (v : @dvalue_base PInf) (w : @dvalue_base PFin) (h : I2F_dvalue_base v w) :
    I2F_memS I2F_State I2F_dvalue_base (convert_impure_base (Pa := PInf) c t v u)
      (convert_impure_base (Pa := PFin) c t w u) := by
  cases c with
  | Inttoptr =>
    unfold convert_impure_base
    refine I2F_memS_bind _ _ _ _ _ _ _ (I2F_assert_inttoptr_types_ok t u) ?_
    intro _ _ _
    have hp : I2F_EOU I2F_dvalue_base
        (DVALUE_Pointer (Pa := PInf) <$> PInf.P2I.int_to_ptr
          (@dvalue_base_int_unsigned PInf v) PInf.PROV.wildcard_prov)
        (DVALUE_Pointer (Pa := PFin) <$> PFin.P2I.int_to_ptr
          (@dvalue_base_int_unsigned PFin w) PFin.PROV.wildcard_prov) := by
      rw [@I2F_dvalue_base_int_unsigned v w h]
      exact I2F_EOU_bind _ _ (I2F_int_to_ptr _ _) fun p q hp ↦
        .I2F_EOU_ret _ _ (.I2F_dvalue_Pointer p q hp)
    cases h <;> first
      | exact .I2F_Mret _ _ I2F_dvalue_Poison
      | exact I2F_memS_lift _ _ _ _ hp
  | Ptrtoint | Ptrtoaddr =>
    cases h with
    | I2F_dvalue_Pointer p q hp =>
      cases u <;> first
        | exact .I2F_Mub_l _ _
        | (simp only [convert_impure_base, I2F_Addr_ptr_to_int p q hp]
           exact I2F_memS_lift _ _ _ _ (I2F_coerce_integer_to_int _ _))
    | I2F_dvalue_Poison =>
      cases u <;> first | exact .I2F_Mub_l _ _ | exact .I2F_Mret _ _ I2F_dvalue_Poison
    | _ => exact .I2F_Mub_l _ _
  | Addrspacecast => exact .I2F_Merr _ _

theorem I2F_convert_impure (c : impure_conversion) (t u : dtyp)
    (v : @dvalue PInf) (w : @dvalue PFin) (h : I2F_dvalue v w) :
    I2F_memS I2F_State I2F_dvalue (convert_impure (Pa := PInf) c t v u)
      (convert_impure (Pa := PFin) c t w u) := by
  cases t with
  | DTYPE_Base src =>
    cases h with
    | I2F_dvalue_Base hb =>
      cases u <;> first
        | exact .I2F_Merr _ _
        | exact I2F_memS_bind _ _ _ _ _ _ _ (I2F_convert_impure_base c src _ _ _ hb)
            fun _ _ hb' ↦ .I2F_Mret _ _ (.I2F_dvalue_Base hb')
    | _ => exact .I2F_Merr _ _
  | DTYPE_Struct _ _ => cases h <;> exact .I2F_Merr _ _
  | DTYPE_Array vec n t =>
    cases vec with
    | false => cases h <;> exact .I2F_Merr _ _
    | true =>
      cases ht : get_vector_conversion_type (.DTYPE_Array true n t) u with
      | none => simp only [convert_impure, ht]; exact .I2F_Merr _ _
      | some tys =>
        obtain ⟨src, dst⟩ := tys
        have hl := @I2F_vector_elts n v w h
        cases hx : @vector_elts PInf n v <;> cases hy : @vector_elts PFin n w <;>
          simp only [hx, hy] at hl <;> simp only [convert_impure, ht, hx, hy]
        · exact .I2F_Merr _ _
        · refine I2F_memS_bind _ _ _ _ _ _ _ (I2F_memS_lift _ _ _ _
            (I2F_EOU_map_monad2 _ _ hl @I2F_dvalue_to_dvalue_base)) ?_
          intro xs ys hxs
          refine I2F_memS_bind _ _ _ _ _ _ _ (I2F_memS_map_monad2 _ _ _ _ _ xs ys hxs
            (I2F_convert_impure_base c src dst)) ?_
          intro bs cs hbs
          exact .I2F_Mret _ _ (I2F_canonicalize_agg u (Forall2_map_Base hbs))

theorem I2F_handle_memoryM (e : (@MemoryE PInf).I) (f : (@MemoryE PFin).I) (h : I2FE_Memory e f) :
    I2F_memS I2F_State (fun a b ↦ I2FA_Memory e a f b) (handle_memoryM (Pa := PInf) e)
      (handle_memoryM (Pa := PFin) f) := by
  cases e <;> cases f <;> simp only [I2FE_Memory] at h
  · exact I2F_Mempush
  · exact I2F_Mempop
  · rcases h with ⟨rfl, rfl, rfl⟩
    exact I2F_memS_bind _ _ _ _ _ _ _ (I2F_allocate_dtyp _ _ _) fun p q hp ↦
      .I2F_Mret _ _ (I2F_dvalue_Base (I2F_dvalue_Pointer p q hp))
  · rcases h with ⟨rfl, ha⟩
    cases ha with
    | I2F_dvalue_Base hb =>
      cases hb <;> first | exact .I2F_Mub_l _ _ | exact I2F_read_dvalue _ _ ‹I2F_Addr _ _› _
    | _ => exact .I2F_Mub_l _ _
  · rcases h with ⟨rfl, ha, hv⟩
    cases ha with
    | I2F_dvalue_Base hb =>
      cases hb <;> first | exact .I2F_Mub_l _ _ | exact I2F_write_dvalue _ _ ‹I2F_Addr _ _› _ _ _ hv
    | _ => exact .I2F_Mub_l _ _
  · rcases h with ⟨rfl, rfl, hv, rfl⟩
    exact I2F_convert_impure _ _ _ _ _ hv

end Vellvm.Theory.I2F.I2F_memory
