module

public import Vellvm.Semantics.Denotation.Frames
public import Vellvm.Theory.I2F.Refinement.Basic

@[expose] public section
namespace Vellvm.Theory.I2F.I2F_denotation
open Vellvm.Tree Semantics.Interfaces.Params Semantics.LLVMEvents Semantics.Denotation Refinement
open Numeric.Rocqlib (option_rel)
open Utils.rutt_cutoff (sum_rel cmp)
open CTree (CTree)

/-- The native catch loop forwards a visible request or step with a guard on resumption. -/
theorem unfold_run_exc_strong [Pa : Params] {A : Type} (t : CFGtop A) :
    eqit Eq false false (run_exc t) (match t.unfold with
      | .ret a => .ret (.inr a)
      | .guard u => .guard (run_exc u)
      | .stuck => .stuck
      | .step u => .step (.guard (run_exc u))
      | .br c _ => nomatch c
      | .vis e k => match exc_of_event e with
        | some x => .ret (.inl x)
        | none => .vis e fun a ↦ .guard (run_exc (k a))) := by
  apply eqit_strict_iff_eq.mpr
  rw (occs := .pos [1]) [← CTree.fold_unfold (run_exc t)]
  change CTree.fold (Catch.ctreeRun exc_of_event t).unfold = _
  rw [Catch.unfold_ctreeRun]
  cases t.unfold with
  | br c _ => exact nomatch c
  | vis e k => dsimp only; cases exc_of_event e <;> rfl
  | _ => rfl

/-- Source UB stays visible at the unwind boundary. -/
theorem cutUB_exc_of_event [Pa : Params] (e : CFGEtop.I) (h : cutUB (E := CFGEtop) e) :
    exc_of_event e = none := by cases h; rfl

/-- Target OOM stays visible at the unwind boundary. -/
theorem cutOOM_exc_of_event [Pa : Params] (e : CFGEtop.I) (h : cutOOM (E := CFGEtop) e) :
    exc_of_event e = none := by cases h; rfl

/-- Only the LLVM exception injection projects a payload, related by `I2FE_Exc`. -/
theorem I2FE_CFG_exc_of_event (e : (@CFGEtop PInf).I) (f : (@CFGEtop PFin).I) (h : I2FE_CFG e f) :
    option_rel I2F_dvalue (@exc_of_event PInf e) (@exc_of_event PFin f) := by
  iterate 9
    rcases e with e | e <;> rcases f with f | f <;> first | exact .none | exact False.elim h | skip
  cases e; cases f; exact .some _ _ h

/-- Catching function exceptions preserves cutoff refinement, including native observable steps. -/
theorem I2F_run_exc {X Y : Type} {RR : X → Y → Prop} (t : @CFGtop PInf X) (s : @CFGtop PFin Y) :
    ruttc cutUB cutOOM I2FE_CFG I2FA_CFG RR t s →
    ruttc cutUB cutOOM I2FE_CFG I2FA_CFG (sum_rel I2F_dvalue RR) (@run_exc PInf X t) (@run_exc PFin Y s) := by
  revert t s
  coinduction C hc ih
  intro t s h
  have guarded {a : @CFGtop PInf X} {b : @CFGtop PFin Y} (hab : I2F_refine_CFG RR a b) :
      C (@run_exc PInf X a).guard (@run_exc PFin Y b).guard := by
    apply Coinduction.b_chain hc
    change Layer _ C _ _
    rw [CTree.unfold_guard, CTree.unfold_guard]
    exact .guard (ih a b hab)
  suffices ∀ l r, Layer (cmp cutUB cutOOM I2FE_CFG I2FA_CFG RR) (I2F_refine_CFG RR) l r →
      Layer (cmp cutUB cutOOM I2FE_CFG I2FA_CFG (sum_rel I2F_dvalue RR)) C
        (Catch.ctreeRun (@exc_of_event PInf) (CTree.fold l)).unfold
        (Catch.ctreeRun (@exc_of_event PFin) (CTree.fold r)).unfold by
    change Layer _ C (Catch.ctreeRun (@exc_of_event PInf) t).unfold
      (Catch.ctreeRun (@exc_of_event PFin) s).unfold
    simpa only [CTree.fold_unfold] using this _ _ (related_iff.mp h)
  intro l r hl
  induction hl with
  | ret h => simp only [Catch.unfold_ctreeRun, CTree.unfold_fold]; exact .ret (.inr h)
  | stuck => simp only [Catch.unfold_ctreeRun, CTree.unfold_fold]; exact .stuck
  | guard h => simp only [Catch.unfold_ctreeRun, CTree.unfold_fold]; exact .guard (ih _ _ h)
  | step h => simp only [Catch.unfold_ctreeRun, CTree.unfold_fold]; exact .step (guarded h)
  | @br c _ _ _ => exact nomatch c
  | @vis e f k j he hk =>
    have hx := I2FE_CFG_exc_of_event e f he
    simp only [Catch.unfold_ctreeRun, CTree.unfold_fold]
    generalize @exc_of_event PInf e = x at hx ⊢
    generalize @exc_of_event PFin f = y at hx ⊢
    cases hx with
    | some _ _ h => exact .ret (.inl h)
    | none => exact .vis he fun a b hab ↦ guarded (hk a b hab)
  | skipL flag _ hi =>
    rw [Catch.unfold_ctreeRun, CTree.unfold_fold]
    exact .skipL flag (by simpa only [CTree.fold_unfold] using hi)
  | skipR flag _ hi =>
    rw (occs := .pos [2]) [Catch.unfold_ctreeRun]
    rw [CTree.unfold_fold]
    exact .skipR flag (by simpa only [CTree.fold_unfold] using hi)
  | cutL h =>
    simp only [Catch.unfold_ctreeRun, CTree.unfold_fold, @cutUB_exc_of_event PInf _ h]
    exact .cutL h
  | cutR h =>
    simp only [Catch.unfold_ctreeRun, CTree.unfold_fold, @cutOOM_exc_of_event PFin _ h]
    exact .cutR h

end Vellvm.Theory.I2F.I2F_denotation
