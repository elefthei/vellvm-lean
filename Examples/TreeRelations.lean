import Vellvm.Tree.Relations

namespace Examples.TreeRelations

open ITree (Effect)
open CTree (CTree)
open Vellvm.Tree

universe u
variable {E F B : Effect.{u}} {X Y : Type u}

/-- The two event rows may have different request and answer types, as in I2F. -/
theorem cutoff_polarity (ubL oomL : E.I) (ubR oomR : F.I)
    (distinctL : oomL ≠ ubL) (distinctR : ubR ≠ oomR)
    (event : E.I → F.I → Prop) (answer : (e : E.I) → E.O e → (f : F.I) → F.O f → Prop)
    (RR : X → Y → Prop) (x : X) (y : Y)
    (lu : E.O ubL → CTree E B X) (lo : E.O oomL → CTree E B X)
    (ru : F.O ubR → CTree F B Y) (ro : F.O oomR → CTree F B Y) :
    let R := ruttc (· = ubL) (· = oomR) event answer RR (B := B)
    R (.vis ubL lu) (.ret y) ∧ R (.ret x) (.vis oomR ro) ∧
      ¬ R (.vis oomL lo) (.ret y) ∧ ¬ R (.ret x) (.vis ubR ru) := by
  exact ⟨Related.cut_left _ _ _ rfl, Related.cut_right _ _ _ rfl,
    fun h ↦ distinctL ((related_vis_ret_iff _ _ _).mp h),
    fun h ↦ distinctR ((related_ret_vis_iff _ _ _).mp h)⟩

/-- An uncut request cannot be discarded just because every answer subsequently reaches a cut. -/
example (p : Comparison E F X Y) (first ub : E.I) (hfirst : ¬ p.cutL first) (hub : p.cutL ub)
    (k : E.O ub → CTree E B X) (y : Y) :
    Related p (.vis ub k) (.ret y) ∧ ¬ Related p (.vis first (fun _ ↦ .vis ub k)) (.ret y) :=
  ⟨Related.cut_left _ _ _ hub, fun h ↦ hfirst ((related_vis_ret_iff _ _ _).mp h)⟩

/-- Two distinct abort requests remain distinguishable even when neither can resume. -/
example (ub failure : E.I) (hne : ub ≠ failure)
    (hu : E.O ub → False) (hf : E.O failure → False) :
    ¬ eutt Eq (.vis ub (fun a ↦ (hu a).elim) : CTree E B X)
      (.vis failure (fun a ↦ (hf a).elim)) :=
  eutt_vis_ne _ _ hne _ _ _

example (x : X) (n : Nat) : euttge Eq (n.repeat CTree.guard (.ret x : CTree E B X)) (.ret x) :=
  euttge_guards_left _ _

example (x : X) : eqit Eq false false (Nat.repeat CTree.guard 0 (.ret x : CTree E B X)) (.ret x) :=
  eqit_refl _ _ _

example (x : X) (n : Nat) :
    ¬ eqit Eq false false ((n + 1).repeat CTree.guard (.ret x : CTree E B X)) (.ret x) := by
  intro h
  have hl := related_iff.mp h
  change Layer _ _ (CTree.guard _).unfold _ at hl
  rw [CTree.unfold_guard, CTree.unfold_ret] at hl
  cases hl with | skipL bad _ => cases bad

example (x : X) : ¬ euttge Eq (.ret x : CTree E B X) (.guard (.ret x)) :=
  not_euttge_ret_guard_ret _ _ _

example (x : X) : ¬ eutt Eq (.spin : CTree E B X) (.ret x) := not_eutt_spin_ret _ _

private abbrev Ask : Effect := ⟨Unit, fun _ ↦ Bool⟩

/-- Both continuations return `false` on the first answer. The other answer separates them. -/
example {B : Effect} : ¬ eutt Eq (.vis () (fun b ↦ .ret b) : CTree Ask B Bool)
    (.vis () (fun _ ↦ .ret false)) := by
  intro h
  have ht := related_iff.mp ((eutt_vis_same_iff _ _ _ _).mp h true)
  rw [CTree.unfold_ret, CTree.unfold_ret] at ht
  cases ht with | ret he => cases he

end Examples.TreeRelations
