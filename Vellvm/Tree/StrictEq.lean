module

public import Vellvm.Tree.ExecutionFacts
public import Vellvm.Tree.ExecutionStateFacts
public import Vellvm.Tree.ExecutionMrecFacts

@[expose] public section
namespace Vellvm.Tree

open CTree (CTree CTreeF)
open ITree (Effect Subeffect)

universe u
variable {E F B D : Effect.{u}} {X Y St : Type u}

/-- Without stuttering or cuts, `eqit Eq` identifies exactly the same finite approximations. -/
@[simp] theorem eqit_strict_iff_eq {t s : CTree E B X} : eqit Eq false false t s ↔ t = s := by
  constructor
  · intro h
    apply Coinductive.CoInd.ext
    intro n
    induction n generalizing t s with
    | zero => rfl
    | succ n ih =>
      have layer := related_iff.mp h
      rw [← CTree.fold_unfold t, ← CTree.fold_unfold s]
      generalize t.unfold = l, s.unfold = r at layer
      cases layer with
      | ret he => cases he; rfl
      | stuck => rfl
      | step hs => exact congrArg CTreeF.step (ih hs)
      | guard hs => exact congrArg CTreeF.guard (ih hs)
      | vis he hk =>
        cases he
        rw [CTree.fold_vis_approx_1, CTree.fold_vis_approx_1]
        exact congrArg (CTreeF.vis _) (funext fun a ↦ ih (hk a a HEq.rfl))
      | br hk =>
        rw [CTree.fold_br_approx_1, CTree.fold_br_approx_1]
        exact congrArg (CTreeF.br _) (funext fun a ↦ ih (hk a))
      | skipL hf _ | skipR hf _ => cases hf
      | cutL hf | cutR hf => exact hf.elim
  · rintro rfl
    exact eqit_refl false false t

namespace Producer

@[simp] theorem meaning_ret_eq (x : X) : (ret (E := E) (B := B) x).meaning = .ret x :=
  eqit_strict_iff_eq.mp (meaning_ret x)

@[simp] theorem meaning_trigger_eq (e : E.I) : (trigger (B := B) e).meaning = .trigger e :=
  eqit_strict_iff_eq.mp (meaning_trigger e)

@[simp] theorem meaning_branch_eq (b : B.I) : (branch (E := E) b).meaning = .branch b :=
  eqit_strict_iff_eq.mp (meaning_branch b)

@[simp] theorem meaning_translate_eq (h : (e : E.I) → (f : F.I) × (F.O f → E.O e))
    (p : Producer E B X) : (translate h p).meaning = CTree.translate h p.meaning :=
  eqit_strict_iff_eq.mp (meaning_translate h p)

@[simp] theorem meaning_bind_eq (p : Producer E B X) (k : X → Producer E B Y) :
    (bind p k).meaning = (p.meaning >>= fun x ↦ (k x).meaning) :=
  eqit_strict_iff_eq.mp (meaning_bind p k)

@[simp] theorem meaning_iter_eq (body : X → Producer E B (X ⊕ Y)) (x : X) :
    (iter body x).meaning = CTree.iter (fun i ↦ (body i).meaning) x :=
  eqit_strict_iff_eq.mp (meaning_iter body x)

@[simp] theorem meaning_interp_eq [B -< D] (h : (e : E.I) → Producer F D (E.O e))
    (p : Producer E B X) : (interp h p).meaning = CTree.interp (fun e ↦ (h e).meaning) p.meaning :=
  eqit_strict_iff_eq.mp (interp_meaningAt h p (.source p.initial) false false)

@[simp] theorem meaning_interp_state_eq [B -< D] (h : (e : E.I) → St → Producer F D (E.O e × St))
    (p : Producer E B X) (st : St) :
    (interp_state h p st).meaning = CTree.interp_state (fun e s ↦ (h e s).meaning) p.meaning st :=
  eqit_strict_iff_eq.mp (interp_state_meaningAt h p st (.source (p.initial, st)) false false)

@[simp] theorem meaning_interp_mrec_eq (ctx : (d : D.I) → Producer (D ⊕ₑ E) B (D.O d))
    (root : Producer (D ⊕ₑ E) B X) :
    (interp_mrec ctx root).meaning = CTree.interp_mrec (fun d ↦ (ctx d).meaning) root.meaning :=
  eqit_strict_iff_eq.mp (interp_mrec_meaning ctx root false false)

@[simp] theorem meaning_mrec_eq (ctx : (d : D.I) → Producer (D ⊕ₑ E) B (D.O d)) (d : D.I) :
    (mrec ctx d).meaning = CTree.mrec (fun i ↦ (ctx i).meaning) d :=
  eqit_strict_iff_eq.mp (mrec_meaning ctx d false false)

end Producer
end Vellvm.Tree
