module

public import CTree.Core.Definitions
public import Coinductive.Tower

/-!
# Head-sensitive relations on choice trees

`Layer` adapts `src/rocq/Utils/rutt_cutoff.v` to native CTree heads. Its two recursive
premises skip a finite number of unmatched guards. Matched guards, visible actions,
observable steps and branches instead hand their continuations to the Pous tower.
-/

@[expose] public section
namespace Vellvm.Tree

open CTree Coinduction
open ITree (Effect)

universe u
variable {E F B : Effect.{u}} {X Y : Type u}

abbrev Head (E B : Effect.{u}) (X : Type u) := CTreeF E B X (CTree E B X)

/-- Parameters of the heterogeneous comparison; cuts inspect the current request only. -/
structure Comparison (E F : Effect.{u}) (X Y : Type u) where
  skipL : Bool
  skipR : Bool
  cutL : E.I → Prop
  cutR : F.I → Prop
  event : E.I → F.I → Prop
  answer : (e : E.I) → E.O e → (f : F.I) → F.O f → Prop
  result : X → Y → Prop

inductive Layer (p : Comparison E F X Y) (sim : CTree E B X → CTree F B Y → Prop) :
    Head E B X → Head F B Y → Prop where
  | ret {x y} : p.result x y → Layer p sim (.ret x) (.ret y)
  | guard {t s} : sim t s → Layer p sim (.guard t) (.guard s)
  | vis {e f k l} : p.event e f →
      (∀ a b, p.answer e a f b → sim (k a) (l b)) → Layer p sim (.vis e k) (.vis f l)
  | skipL {t : CTree E B X} {r} : p.skipL = true → Layer p sim t.unfold r →
      Layer p sim (.guard t) r
  | skipR {l} {s : CTree F B Y} : p.skipR = true → Layer p sim l s.unfold →
      Layer p sim l (.guard s)
  | cutL {e k r} : p.cutL e → Layer p sim (.vis e k) r
  | cutR {l f k} : p.cutR f → Layer p sim l (.vis f k)
  | stuck : Layer p sim .stuck .stuck
  | step {t s} : sim t s → Layer p sim (.step t) (.step s)
  | br {c k l} : (∀ a, sim (k a) (l a)) → Layer p sim (.br c k) (.br c l)

variable {p : Comparison E F X Y} {R S : Rel (CTree E B X) (CTree F B Y)}

theorem Layer.mono (le : ∀ t s, R t s → S t s) {l r} (h : Layer p R l r) : Layer p S l r := by
  induction h with
  | ret h => exact .ret h
  | guard h => exact .guard (le _ _ h)
  | vis he hk => exact .vis he fun a b hab ↦ le _ _ (hk a b hab)
  | skipL h _ ih => exact .skipL h ih
  | skipR h _ ih => exact .skipR h ih
  | cutL h => exact .cutL h
  | cutR h => exact .cutR h
  | stuck => exact .stuck
  | step h => exact .step (le _ _ h)
  | br hk => exact .br fun a ↦ le _ _ (hk a)

/-- One application of `Layer`, observing both roots. -/
def layerMon (B : Effect.{u}) (p : Comparison E F X Y) : Mon (Rel (CTree E B X) (CTree F B Y)) where
  body R t s := Layer p R t.unfold s.unfold
  mono le _ _ h := h.mono le

abbrev Related (p : Comparison E F X Y) : Rel (CTree E B X) (CTree F B Y) := gfp (layerMon B p)

/-- The two directions are the unfold and fold rules, respectively. -/
theorem related_iff {t : CTree E B X} {s : CTree F B Y} :
    Related p t s ↔ Layer p (Related p) t.unfold s.unfold :=
  ⟨gfp_pfp (b := layerMon B p) t s, b_chain (gfp_chain (layerMon B p)) t s⟩

abbrev ruttc (cutL : E.I → Prop) (cutR : F.I → Prop) (event : E.I → F.I → Prop)
    (answer : (e : E.I) → E.O e → (f : F.I) → F.O f → Prop) (RR : X → Y → Prop) :
    Rel (CTree E B X) (CTree F B Y) := Related ⟨true, true, cutL, cutR, event, answer, RR⟩

/-- Matching requests have the same answer type; compare answers after that identification. -/
abbrev eqitComparison (E : Effect.{u}) (RR : X → Y → Prop) (bL bR : Bool) : Comparison E E X Y :=
  ⟨bL, bR, fun _ ↦ False, fun _ ↦ False, Eq, fun _ a _ b ↦ HEq a b, RR⟩

abbrev eqit (RR : X → Y → Prop) (bL bR : Bool) : Rel (CTree E B X) (CTree E B Y) :=
  Related (eqitComparison E RR bL bR)

abbrev eutt (RR : X → Y → Prop) : Rel (CTree E B X) (CTree E B Y) := eqit RR true true
abbrev euttge (RR : X → Y → Prop) : Rel (CTree E B X) (CTree E B Y) := eqit RR true false

/-- Reflexivity does not use stuttering, even on a tree with infinitely many guards. -/
theorem eqit_refl (bL bR : Bool) : ∀ t : CTree E B X, eqit Eq bL bR t t := by
  coinduction R hR ih
  intro t
  change Layer _ R t.unfold t.unfold
  cases t.unfold with
  | ret _ => exact .ret rfl
  | stuck => exact .stuck
  | step _ => exact .step (ih _)
  | guard _ => exact .guard (ih _)
  | vis e k =>
    refine .vis rfl fun a b h ↦ ?_
    cases eq_of_heq h
    exact ih _
  | br _ _ => exact .br fun _ ↦ ih _

theorem Related.guard_left {t : CTree E B X} {s : CTree F B Y} (flag : p.skipL = true)
    (h : Related p t s) : Related p t.guard s := by
  apply related_iff.mpr
  rw [unfold_guard]
  exact .skipL flag (related_iff.mp h)

theorem Related.guard_right {t : CTree E B X} {s : CTree F B Y} (flag : p.skipR = true)
    (h : Related p t s) : Related p t s.guard := by
  apply related_iff.mpr
  rw [unfold_guard]
  exact .skipR flag (related_iff.mp h)

/-- Neither an empty answer type nor equal continuations identify different request heads. -/
theorem related_vis_iff (e : E.I) (f : F.I) (k : E.O e → CTree E B X) (l : F.O f → CTree F B Y) :
    Related p (.vis e k) (.vis f l) ↔ p.cutL e ∨ p.cutR f ∨
      p.event e f ∧ ∀ a b, p.answer e a f b → Related p (k a) (l b) := by
  rw [related_iff, unfold_vis, unfold_vis]
  constructor
  · intro h
    cases h with
    | vis he hk => exact .inr (.inr ⟨he, hk⟩)
    | cutL h => exact .inl h
    | cutR h => exact .inr (.inl h)
  · rintro (h | h | ⟨he, hk⟩)
    · exact .cutL h
    · exact .cutR h
    · exact .vis he hk

theorem eutt_vis_ne (e f : E.I) (hne : e ≠ f) (k : E.O e → CTree E B X)
    (l : E.O f → CTree E B Y) (RR : X → Y → Prop) : ¬ eutt RR (.vis e k) (.vis f l) := by
  intro h
  rcases related_vis_iff e f k l |>.mp h with h | h | ⟨h, _⟩
  · exact h.elim
  · exact h.elim
  · exact hne h

theorem eutt_vis_same_iff (RR : X → Y → Prop) (e : E.I) (k : E.O e → CTree E B X)
    (l : E.O e → CTree E B Y) : eutt RR (.vis e k) (.vis e l) ↔ ∀ a, eutt RR (k a) (l a) := by
  refine (related_vis_iff (p := eqitComparison E RR true true) e e k l).trans ?_
  constructor
  · rintro (h | h | ⟨_, hk⟩)
    · exact h.elim
    · exact h.elim
    · exact fun a ↦ hk a a HEq.rfl
  · intro h
    refine .inr (.inr ⟨rfl, fun a b hab ↦ ?_⟩)
    cases eq_of_heq hab
    exact h a

theorem Related.cut_left (e : E.I) (k : E.O e → CTree E B X) (s : CTree F B Y)
    (cut : p.cutL e) : Related p (.vis e k) s := by
  apply related_iff.mpr
  rw [unfold_vis]
  exact .cutL cut

theorem Related.cut_right (t : CTree E B X) (f : F.I) (k : F.O f → CTree F B Y)
    (cut : p.cutR f) : Related p t (.vis f k) := by
  apply related_iff.mpr
  rw [unfold_vis]
  exact .cutR cut

/-- A return opposite a visible event isolates the exact directional cutoff. -/
theorem related_vis_ret_iff (e : E.I) (k : E.O e → CTree E B X) (y : Y) :
    Related p (.vis e k) (.ret y) ↔ p.cutL e := by
  rw [related_iff, unfold_vis, unfold_ret]
  exact ⟨fun h ↦ by cases h with | cutL h => exact h, .cutL⟩

theorem related_ret_vis_iff (x : X) (f : F.I) (k : F.O f → CTree F B Y) :
    Related p (.ret x) (.vis f k) ↔ p.cutR f := by
  rw [related_iff, unfold_ret, unfold_vis]
  exact ⟨fun h ↦ by cases h with | cutR h => exact h, .cutR⟩

/-- A one-sided attempt to match `spin` with a return would need an infinite `Layer` proof. -/
theorem not_eutt_spin_ret (RR : X → Y → Prop) (y : Y) :
    ¬ eutt RR (.spin : CTree E B X) (.ret y) := by
  intro h
  have hh := related_iff.mp h
  generalize hl : (CTree.spin : CTree E B X).unfold = l at hh
  generalize hr : (CTree.ret y : CTree E B Y).unfold = r at hh
  rw [spin_unfold] at hl
  rw [unfold_ret] at hr
  induction hh with
  | skipL _ _ ih =>
    cases hl
    exact ih spin_unfold.symm hr
  | _ => first | contradiction | cases hl | cases hr

/-- One-sided improvement allows a guard only on the left. -/
theorem not_euttge_ret_guard_ret (RR : X → Y → Prop) (x : X) (y : Y) :
    ¬ euttge RR (.ret x : CTree E B X) (.guard (.ret y)) := by
  intro h
  have hh := related_iff.mp h
  rw [unfold_ret, unfold_guard] at hh
  cases hh with | skipR h _ => cases h

theorem not_strong_guard_ret (RR : X → Y → Prop) (x : X) (y : Y) :
    ¬ eqit RR false false (.guard (.ret x) : CTree E B X) (.ret y) := by
  intro h
  have hh := related_iff.mp h
  rw [unfold_guard, unfold_ret] at hh
  cases hh with | skipL h _ => cases h

/-- A finite prefix of left guards is admitted, including the zero-length prefix. -/
theorem euttge_guards_left (n : Nat) (t : CTree E B X) :
    euttge Eq (n.repeat CTree.guard t) t := by
  induction n with
  | zero => exact eqit_refl true false t
  | succ n ih => exact Related.guard_left rfl ih

/-- Observable steps and branches, including branches without answers, are not guards. -/
theorem not_eutt_step_ret (RR : X → Y → Prop) (t : CTree E B X) (y : Y) :
    ¬ eutt RR (.step t) (.ret y) := by
  intro h
  have hh := related_iff.mp h
  rw [unfold_step, unfold_ret] at hh
  cases hh

theorem not_eutt_br_ret (RR : X → Y → Prop) (c : B.I) (k : B.O c → CTree E B X) (y : Y) :
    ¬ eutt RR (.br c k) (.ret y) := by
  intro h
  have hh := related_iff.mp h
  rw [unfold_br, unfold_ret] at hh
  cases hh

end Vellvm.Tree
