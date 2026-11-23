import Vellvm.Semantics.Denotation.Terminators
import Vellvm.Syntax.ScopeTheory
import Vellvm.Theory.Equational.Post

namespace Vellvm.Theory.Equational

open Semantics Semantics.Denotation Semantics.DynamicValues Semantics.Interfaces.Params
open Syntax.DynamicTypes Syntax.LLVMAst Syntax.Scope Utils.ListUtil

variable [Pa : Params]

private theorem select_switch_mem (v : dvalue) (fallback : block_id)
    (arms : List (dvalue × block_id)) {id : block_id}
    (h : select_switch v fallback arms = .raise_ret id) : id ∈ fallback :: arms.map Prod.snd := by
  induction arms with
  | nil => cases h; exact .head _
  | cons arm arms ih =>
    rcases arm with ⟨w, dest⟩
    unfold select_switch at h
    split at h
    · split at h
      · split at h
        · cases h; exact .tail _ (.head _)
        · rcases List.mem_cons.mp (ih h) with rfl | hmem
          · exact .head _
          · exact .tail _ (.tail _ hmem)
      · contradiction
    · contradiction

private theorem map_switch_labels {arms : List (tint_literal × block_id)}
    {converted : List (dvalue × block_id)}
    (h : map_monad (fun (.TInt_Literal sz x, dest) ↦ do
      let s ← coerce_integer_to_int (some sz) (Attributes.denote_int_syntax x)
      return (DVALUE_Base s, dest)) arms = EOU.raise_ret converted) :
    converted.map Prod.snd = arms.map Prod.snd := by
  have hrel := (EOU.map_monad_EOU_Forall2 _ _ _).mp h
  clear h
  induction hrel with
  | nil => rfl
  | @cons arm result _ _ hhead _ ih =>
    rcases arm with ⟨⟨sz, x⟩, dest⟩
    obtain ⟨s, _, hs⟩ := EOU.EOU_bind_ret_inv _ _ result hhead
    cases hs
    exact congrArg (dest :: ·) ih

private theorem lifted_switch_post (r : EOU.EOU block_id) (P : block_id → Prop)
    (h : ∀ id, r = .raise_ret id → P id) :
    has_post (LLVMEvents.EOU_to_itree r : LLVMEvents.CFGtop block_id) P := by
  cases r with
  | raise_ret id => exact has_post_ret _ _ (h id rfl)
  | raise_error s => exact raise_has_all_posts s P
  | raise_oom s => exact raiseOOM_has_all_posts s P
  | raise_ub s => exact raiseUB_has_all_posts s P

theorem denote_terminator_exits_in_outputs
    (term : (instr_id × terminator dtyp) × List (metadata dtyp)) :
    has_post (denote_terminator term)
      (Sum.elim (fun id ↦ id ∈ terminator_outputs term.1.2) (fun _ ↦ True)) := by
  rcases term with ⟨⟨iid, t⟩, md⟩
  unfold denote_terminator Denotation.Worker.denote_terminator
  apply has_post_bind_weak
  intro _
  cases t with
  | TERM_Ret arg =>
    rcases arg with ⟨dt, e⟩
    exact has_post_bind_weak fun _ ↦ has_post_ret _ _ trivial
  | TERM_Ret_void => exact has_post_ret _ _ trivial
  | TERM_Br_1 b => exact has_post_ret _ _ (.head _)
  | TERM_Br arg b₁ b₂ =>
    rcases arg with ⟨dt, e⟩
    apply has_post_bind_weak
    intro v
    cases v with
    | DVALUE_Base base =>
      cases base with
      | DVALUE_I w bit =>
        dsimp only
        split
        · apply has_post_ret
          split <;> simp [Sum.elim, terminator_outputs]
        · apply raise_has_all_posts
      | DVALUE_Poison => apply raiseUB_has_all_posts
      | _ => apply raise_has_all_posts
    | _ => apply raise_has_all_posts
  | TERM_Switch arg fallback arms =>
    rcases arg with ⟨dt, e⟩
    apply has_post_bind_weak
    intro v
    dsimp only
    split
    · apply raiseUB_has_all_posts
    · apply has_post_bind (P := fun id ↦ id ∈ fallback :: arms.map Prod.snd)
      · apply lifted_switch_post
        intro id h
        obtain ⟨converted, hc, hs⟩ := EOU.EOU_bind_ret_inv _ _ id h
        rw [← map_switch_labels hc]
        exact select_switch_mem v fallback converted hs
      · exact fun id h ↦ has_post_ret _ _ h
  | TERM_IndirectBr arg brs fn =>
    rcases arg with ⟨dt, e⟩
    apply has_post_bind_weak
    intro v
    dsimp only
    split
    · apply raiseUB_has_all_posts
    · cases fn with
      | none => apply raise_has_all_posts
      | some f =>
        apply has_post_bind_weak
        intro addrs
        cases dvalue_ptr_address v with
        | none => apply raise_has_all_posts
        | some z =>
          cases h : indirectbr_target z (brs.zip addrs) with
          | none => simp only [h]; apply raiseUB_has_all_posts
          | some b =>
            simp only [h]
            exact has_post_ret _ _ (indirectbr_target_In z brs addrs h)
  | TERM_Invoke fnptr args dest unwind anns obs =>
    rcases fnptr with ⟨dt, e⟩
    iterate 5 (apply has_post_bind_weak; intro _)
    rename_i rv
    cases rv with
    | inl exn => exact has_post_bind_weak fun _ ↦ has_post_ret _ _ (.tail _ (.head _))
    | inr value =>
      cases iid with
      | IVoid _ => exact has_post_ret _ _ (.head _)
      | IId id => exact has_post_bind_weak fun _ ↦ has_post_ret _ _ (.head _)
  | TERM_Resume arg =>
    rcases arg with ⟨dt, e⟩
    apply has_post_bind_weak
    intro exn
    apply raiseLLVM_has_all_posts
  | TERM_Unreachable => apply raiseUB_has_all_posts

theorem denote_bk_exits_in_outputs (vararg : Option Pa.PTR.ptr) (b : block dtyp)
    (from_ : block_id) :
    has_post (denote_block b from_ vararg) (Sum.elim (fun id ↦ id ∈ successors b) (fun _ ↦ True)) :=
  has_post_bind_weak fun _ ↦ has_post_bind_weak fun _ ↦ denote_terminator_exits_in_outputs b.blk_term

end Vellvm.Theory.Equational
