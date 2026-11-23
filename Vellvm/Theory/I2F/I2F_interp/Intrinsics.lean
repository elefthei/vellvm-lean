module

public import Vellvm.Semantics.Handlers.Intrinsics
public import Vellvm.Theory.I2F.I2F_exp.Values
public import Vellvm.Theory.I2F.Refinement.TreeLaws

@[expose] public section
namespace Vellvm.Theory.I2F.I2F_interp
open Semantics.DynamicValues Semantics.LLVMEvents Semantics.IntrinsicsDefinitions
open Semantics.Handlers.Intrinsics Syntax.DynamicTypes Numeric.Rocqlib
open Refinement I2F_exp
open Utils.rutt_cutoff (ruttc_bind ruttc_ret ruttc_trigger')

local notation "BaseResult" => Sum.LiftRel I2F_dvalue_base I2F_dvalue_base

theorem I2F_pure_base_to_semantic (f : @pure_base_function PInf) (g : @pure_base_function PFin)
    (hf : ∀ xs ys, List.Forall₂ I2F_dvalue_base xs ys → I2F_EOU BaseResult (f xs) (g ys))
    (xs ys va vb) (h : List.Forall₂ I2F_dvalue xs ys) : I2F_refine_MCFG I2F_exc_dvalue
      (pure_base_to_semantic (Pa := PInf) f xs va) (pure_base_to_semantic (Pa := PFin) g ys vb) := by
  apply I2F_refine_lift
  refine I2F_EOU_bind _ _ (I2F_EOU_map_monad2 _ _ h fun _ _ hv ↦ I2F_dvalue_to_dvalue_base hv) ?_
  intro bs cs hbc
  refine I2F_EOU_bind _ _ (hf bs cs hbc) ?_
  intro a b hab
  cases hab with
  | inl hv => exact .I2F_EOU_ret _ _ (.inl (.I2F_dvalue_Base hv))
  | inr hv => exact .I2F_EOU_ret _ _ (.inr (.I2F_dvalue_Base hv))

theorem I2F_llvm_fabs (xs ys) (h : List.Forall₂ I2F_dvalue_base xs ys) :
    I2F_EOU BaseResult (@llvm_fabs PInf xs) (@llvm_fabs PFin ys) := by
  rcases h with _ | ⟨hx, hs⟩ <;> try exact .I2F_EOU_error _ _
  cases hx <;> cases hs <;> first
    | exact .I2F_EOU_error _ _
    | exact .I2F_EOU_ret _ _ (.inr (.I2F_dvalue_Float _))
    | exact .I2F_EOU_ret _ _ (.inr (.I2F_dvalue_Double _))

local macro "binary_float_cases" h:Lean.Parser.Tactic.elimTarget : tactic => `(tactic| (
  rcases $h with _ | ⟨ha, hs⟩ <;> try exact .I2F_EOU_error _ _
  cases ha <;> try exact .I2F_EOU_error _ _
  all_goals rcases hs with _ | ⟨hb, hs⟩ <;> try exact .I2F_EOU_error _ _
  all_goals cases hb <;> cases hs <;> first
    | exact .I2F_EOU_error _ _
    | exact .I2F_EOU_ret _ _ (.inr (.I2F_dvalue_Float _))
    | exact .I2F_EOU_ret _ _ (.inr (.I2F_dvalue_Double _))))

theorem I2F_llvm_maxnum (xs ys) (h : List.Forall₂ I2F_dvalue_base xs ys) :
    I2F_EOU BaseResult (@llvm_maxnum PInf xs) (@llvm_maxnum PFin ys) := by
  binary_float_cases h

theorem I2F_llvm_minimum (xs ys) (h : List.Forall₂ I2F_dvalue_base xs ys) :
    I2F_EOU BaseResult (@llvm_minimum PInf xs) (@llvm_minimum PFin ys) := by
  binary_float_cases h

theorem I2F_llvm_assume (xs ys) (h : List.Forall₂ I2F_dvalue_base xs ys) :
    I2F_EOU BaseResult (@llvm_assume PInf xs) (@llvm_assume PFin ys) := by
  rcases h with _ | ⟨hx, hs⟩ <;> try exact .I2F_EOU_error _ _
  cases hx <;> try (cases hs <;> first | exact .I2F_EOU_error _ _ | exact .I2F_EOU_ub _ _)
  rename_i sz i
  rcases sz with ⟨_ | (_ | n), hsz⟩
  · exact False.elim (Nat.lt_irrefl 0 hsz)
  · cases hs <;> try exact .I2F_EOU_error _ _
    simp only [llvm_assume]; split
    · exact .I2F_EOU_ret _ _ (.inr .I2F_dvalue_None)
    · exact .I2F_EOU_ub _ _
  · exact .I2F_EOU_error _ _

theorem I2F_llvm_vellvm_internal_throw (xs ys) (h : List.Forall₂ I2F_dvalue_base xs ys) :
    I2F_EOU BaseResult (@llvm_vellvm_internal_throw PInf xs) (@llvm_vellvm_internal_throw PFin ys) := by
  cases h with
  | nil => exact .I2F_EOU_ret _ _ (.inl .I2F_dvalue_None)
  | cons _ _ => exact .I2F_EOU_error _ _

private theorem lane_eq (x y) (h : I2F_dvalue x y) (acc : Option ival) :
    @dvalue_to_ival.lane PInf x acc = @dvalue_to_ival.lane PFin y acc := by
  cases h with
  | I2F_dvalue_Base hb =>
    cases hb <;> cases acc with
    | none => rfl
    | some a => cases a <;> rfl
  | I2F_dvalue_Struct _ _ | I2F_dvalue_Array _ _ => rfl

theorem I2F_dvalue_to_ival (x y) (h : I2F_dvalue x y) :
    @dvalue_to_ival PInf x = @dvalue_to_ival PFin y := by
  cases h with
  | I2F_dvalue_Base hb => cases hb <;> rfl
  | I2F_dvalue_Struct _ _ => rfl
  | I2F_dvalue_Array v hs =>
    cases v with
    | false => rfl
    | true =>
      simp only [dvalue_to_ival]
      induction hs with
      | nil => rfl
      | cons hx _ ih => simp only [List.foldr_cons, ih, lane_eq _ _ hx]

theorem I2F_dvalues_to_ivals (xs ys) (h : List.Forall₂ I2F_dvalue xs ys) :
    @dvalues_to_ivals PInf xs = @dvalues_to_ivals PFin ys := by
  unfold dvalues_to_ivals
  induction h with
  | nil => rfl
  | cons hx _ ih => simp only [List.mapM_cons, I2F_dvalue_to_ival _ _ hx, ih]

theorem I2F_llvm_int_intrinsic (f : int_intrinsic) (t : dtyp) (xs ys va vb)
    (h : List.Forall₂ I2F_dvalue xs ys) : I2F_refine_MCFG I2F_exc_dvalue
      (pure_to_semantic (Pa := PInf) (@llvm_int_intrinsic PInf f t) xs va)
      (pure_to_semantic (Pa := PFin) (@llvm_int_intrinsic PFin f t) ys vb) := by
  apply I2F_refine_lift
  simp only [llvm_int_intrinsic, I2F_dvalues_to_ivals _ _ h]
  split
  · rename_i r _
    apply I2F_EOU_ret; apply Sum.LiftRel.inr
    cases r with
    | IR_Int _ _ => exact .I2F_dvalue_Base (.I2F_dvalue_Int _)
    | IR_Poison => exact .I2F_dvalue_Base .I2F_dvalue_Poison
    | IR_Overflow _ _ _ =>
      exact .I2F_dvalue_Struct _ (.cons (.I2F_dvalue_Base (.I2F_dvalue_Int _))
        (.cons (.I2F_dvalue_Base (.I2F_dvalue_Int _)) .nil))
  · exact .I2F_EOU_error _ _

private theorem related_emit {D F : ITree.Effect} [l : D -< @MCFGEtop PInf]
    [r : F -< @MCFGEtop PFin] (e : D.I) (f : F.I) (R : D.O e → F.O f → Prop)
    (h : I2FE_MCFG (requestIn e) (requestIn f))
    (ha : ∀ a b, I2FA_MCFG (requestIn e) a (requestIn f) b → R ((l.map e).2 a) ((r.map f).2 b)) :
    I2F_refine_MCFG R (Tree.Runtime.emit (E := D) e) (Tree.Runtime.emit (E := F) f) := by
  exact ruttc_trigger' _ _ _ _ h fun a b hab ↦ ruttc_ret _ _ (ha a b hab)

private theorem store_none (t : dtyp) (x y v w) (hp : I2F_dvalue x y) (hv : I2F_dvalue v w) :
    I2F_refine_MCFG I2F_exc_dvalue
      (do Semantics.LLVMEvents.Worker.store (Pa := PInf) t x v
          pure (.inr (@DVALUE_Base PInf (@DVALUE_None PInf))))
      (do Semantics.LLVMEvents.Worker.store (Pa := PFin) t y w
          pure (.inr (@DVALUE_Base PFin (@DVALUE_None PFin)))) := by
  refine ruttc_bind _ _ _ _ (fun (_ _ : Unit) ↦ True) _ _ _ _ _ ?_ ?_
  · exact related_emit (D := @MemoryE PInf) (F := @MemoryE PFin) (@Store PInf t x v) (@Store PFin t y w) _
      ⟨rfl, hp, hv⟩ fun _ _ _ ↦ trivial
  · exact fun _ _ _ ↦ ruttc_ret _ _ (.inr (.I2F_dvalue_Base .I2F_dvalue_None))

private theorem bad_args (msg : IRString) : I2F_refine_MCFG I2F_exc_dvalue
    (Semantics.LLVMEvents.Worker.«raise» msg) (Semantics.LLVMEvents.Worker.«raise» msg) :=
  I2F_refine_lift _ _ _ (.I2F_EOU_error msg msg)

theorem I2F_llvm_va_start (xs ys va vb) (h : List.Forall₂ I2F_dvalue xs ys)
    (hp : option_rel I2F_Addr va vb) : I2F_refine_MCFG I2F_exc_dvalue
      (llvm_va_start (Pa := PInf) xs va) (llvm_va_start (Pa := PFin) ys vb) := by
  rcases h with _ | ⟨hx, hs⟩ <;> try exact bad_args _
  cases hs <;> try exact bad_args _
  cases hp with
  | none => exact bad_args _
  | some p q hp =>
    have hv := I2F_dvalue_Base (I2F_dvalue_Pointer p q hp)
    have hd := hx
    cases hx with
    | I2F_dvalue_Base hb =>
      cases hb <;> first
        | exact store_none _ _ _ _ _ hd hv
        | exact I2F_refine_lift _ _ _ (.I2F_EOU_ub _ (.raise_ub _))
    | I2F_dvalue_Struct a hs => exact store_none _ _ _ _ _ (.I2F_dvalue_Struct a hs) hv
    | I2F_dvalue_Array a hs => exact store_none _ _ _ _ _ (.I2F_dvalue_Array a hs) hv

theorem I2F_llvm_va_copy (xs ys va vb) (h : List.Forall₂ I2F_dvalue xs ys) :
    I2F_refine_MCFG I2F_exc_dvalue (llvm_va_copy (Pa := PInf) xs va) (llvm_va_copy (Pa := PFin) ys vb) := by
  rcases h with _ | ⟨hd, hs⟩ <;> try exact bad_args _
  rcases hs with _ | ⟨hs, tail⟩ <;> try exact bad_args _
  cases tail <;> try exact bad_args _
  refine ruttc_bind _ _ _ _ I2F_dvalue _ _ _ _ _ ?_ fun _ _ hv ↦ store_none _ _ _ _ _ hd hv
  exact related_emit (D := @MemoryE PInf) (F := @MemoryE PFin)
    (@Load PInf (.DTYPE_Base .DTYPE_Pointer) _) (@Load PFin (.DTYPE_Base .DTYPE_Pointer) _) _
    ⟨rfl, hs⟩ fun _ _ hab ↦ hab

theorem I2F_llvm_va_end (xs ys va vb) : I2F_refine_MCFG I2F_exc_dvalue
    (llvm_va_end (Pa := PInf) xs va) (llvm_va_end (Pa := PFin) ys vb) :=
  ruttc_ret _ _ (.inr (.I2F_dvalue_Base .I2F_dvalue_None))

theorem I2F_handle_intrinsics (e : @IntrinsicRequest PInf) (f : @IntrinsicRequest PFin)
    (h : I2FE_Intrinsic e f) : I2F_refine_MCFG (fun x y ↦ I2FA_Intrinsic e x f y)
      (handle_intrinsics (Pa := PInf) e) (handle_intrinsics (Pa := PFin) f) := by
  rcases e with ⟨t, name, xs, va⟩
  rcases f with ⟨t', name', ys, vb⟩
  rcases h with ⟨rfl, rfl, hs, hv⟩
  have hargs := I2F_targs_snd hs
  have pass := related_emit (D := @IntrinsicE PInf) (F := @IntrinsicE PFin)
    (@Intrinsic PInf t name xs va) (@Intrinsic PFin t name ys vb) I2F_exc_dvalue
    ⟨rfl, rfl, hs, hv⟩ (fun _ _ hab ↦ hab)
  simp only [handle_intrinsics, Semantics.Handlers.Intrinsics.Worker.handle_intrinsics,
    Semantics.IntrinsicsDefinitions.Worker.named_intrinsic_semantics]
  cases lookup_intrinsic name with
  | none => exact pass
  | some family =>
    cases family <;> first
      | exact pass
      | exact I2F_llvm_int_intrinsic _ _ _ _ _ _ hargs
      | exact I2F_llvm_va_start _ _ _ _ hargs hv
      | exact I2F_llvm_va_copy _ _ _ _ hargs
      | exact I2F_llvm_va_end _ _ _ _
      | apply I2F_pure_base_to_semantic _ _ _ _ _ _ _ hargs
        first | exact I2F_llvm_fabs | exact I2F_llvm_maxnum | exact I2F_llvm_minimum
              | exact I2F_llvm_assume | exact I2F_llvm_vellvm_internal_throw

end Vellvm.Theory.I2F.I2F_interp
