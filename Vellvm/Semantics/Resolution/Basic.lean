module

public import Vellvm.Semantics.Choices
public import Vellvm.Utils.ListUtil

/-! Local rules for comparing the model with its branch-free reference interpretation. -/
@[expose] public section
namespace Vellvm.Semantics.Resolution
open ITree (Effect)
open CTree
open Vellvm.Tree Interfaces.IPtr LLVMEvents

variable [IP : IPtr] [T : IPtrTheory] {X Y : Type}

abbrev Resolves (m : CTree MCFGEbot (Choice (@Implementations.ParamsV.ParamsV IP T)) X)
    (r : MCFGbot X) : Prop := eutt Eq (refine canonical m) r

theorem resolves_pure (x : X) : Resolves (pure x) (pure x) := by
  unfold Resolves
  rw [refine_ret]
  exact eqit_refl true true _

theorem resolves_bind {m r} {k l} (h : Resolves (X := X) m r)
    (hk : ∀ x, Resolves (X := Y) (k x) (l x)) : Resolves (m >>= k) (r >>= l) := by
  unfold Resolves
  rw [refine_bind]
  exact Utils.ListUtil.eqit_bind (fun x _ eq ↦ eq ▸ hk x) _ _ h

theorem resolves_emit {E : Effect} [E -< MCFGEbot] (e : E.I) :
    Resolves (Runtime.emit (E := E) e) (Runtime.emit (E := E) e) := by
  change eutt Eq (refine canonical (Runtime.emit (E := E) e)) (Runtime.emit (E := E) e)
  unfold Runtime.emit
  generalize ITree.Subeffect.map (E₁ := E) (E₂ := MCFGEbot) e = p
  obtain ⟨f, back⟩ := p
  change eutt Eq (refine canonical (CTree.trigger f >>= fun a ↦ pure (back a)))
    (CTree.trigger f >>= fun a ↦ pure (back a))
  simp only [CTree.trigger, vis_bind, pure_bind', refine_vis, mtrigger, CTree.trigger', CTree.vis',
    refine_ret]
  have self (i : MCFGEbot.I) :
      ITree.Subeffect.map (E₁ := MCFGEbot) (E₂ := MCFGEbot) i = ⟨i, id⟩ := by
    rcases i with i | i | i | i | i | i <;> rfl
  rw [self f, eutt_vis_same_iff]
  intro a
  exact Related.guard_left rfl (eqit_refl true true _)

theorem resolves_choice (c : ChoiceRequest (@Implementations.ParamsV.ParamsV IP T)) :
    Resolves (branchingChooser c) (referenceChooser c) := by
  change eutt Eq (refine canonical (CTree.branch c >>= fun a ↦ pure a.val)) (pure c.reference)
  simp only [CTree.branch, br_bind, pure_bind', refine_br, canonical, refine_ret]
  exact Related.guard_left rfl (eqit_refl true true _)

end Vellvm.Semantics.Resolution
