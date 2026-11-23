module

public import Vellvm.Tree.Relations
public import Vellvm.Utils.CTreeUtil
public import CTree.Interp.RecursionFacts
public import Vellvm.Utils.ListUtil

/-! Cutoffs and heterogeneous, head-sensitive simulation (`Utils/rutt_cutoff.v`). -/
@[expose] public section
namespace Vellvm.Utils.rutt_cutoff

open CTree Coinduction Vellvm.Utils.CTreeUtil
open ITree (Effect)
open Vellvm.Tree (Comparison Head Layer layerMon Related related_iff eqit euttge eutt)

universe u
variable {E F G H B : Effect.{u}} {X Y : Type u}

abbrev pred1 (E : Effect.{u}) := E.I → Prop
abbrev prerel (E F : Effect.{u}) := E.I → F.I → Prop
abbrev postrel (E F : Effect.{u}) := (e : E.I) → E.O e → (f : F.I) → F.O f → Prop
abbrev eqp1 (p q : pred1 E) := ∀ e, p e ↔ q e
abbrev eq_REv (p q : prerel E F) := ∀ e f, p e f ↔ q e f
abbrev eq_RAns (p q : postrel E F) := ∀ e x f y, p e x f y ↔ q e x f y
inductive sum_pred1 (p : pred1 E) (q : pred1 F) : pred1 (E ⊕ₑ F) where
  | inl (e) : p e → sum_pred1 p q (.inl e)
  | inr (e) : q e → sum_pred1 p q (.inr e)
abbrev sum_pred1_inl := @sum_pred1.inl
abbrev sum_pred1_inr := @sum_pred1.inr
abbrev TT1 : pred1 E := fun _ ↦ True
abbrev FF1 : pred1 E := fun _ ↦ False
abbrev TT4 : prerel E F := fun _ _ ↦ True
abbrev FF4 : prerel E F := fun _ _ ↦ False
abbrev TT6 : postrel E F := fun _ _ _ _ ↦ True
abbrev FF6 : postrel E F := fun _ _ _ _ ↦ False
abbrev sum_rel {I J X Y : Type u} (P : I → J → Prop) (Q : X → Y → Prop) := Sum.LiftRel P Q
abbrev sum_prerel (p : prerel E F) (q : prerel G H) : prerel (E ⊕ₑ G) (F ⊕ₑ H) := Sum.LiftRel p q
def sum_postrel (p : postrel E F) (q : postrel G H) : postrel (E ⊕ₑ G) (F ⊕ₑ H)
  | .inl e, x, .inl f, y => p e x f y
  | .inr e, x, .inr f, y => q e x f y
  | .inl _, _, .inr _, _ | .inr _, _, .inl _, _ => False
inductive inl_prerel (p : prerel (E ⊕ₑ G) (F ⊕ₑ H)) : prerel E F where
  | intro (e f) : p (.inl e) (.inl f) → inl_prerel p e f
inductive inr_prerel (p : prerel (E ⊕ₑ G) (F ⊕ₑ H)) : prerel G H where
  | intro (e f) : p (.inr e) (.inr f) → inr_prerel p e f
inductive inl_postrel (p : postrel (E ⊕ₑ G) (F ⊕ₑ H)) : postrel E F where
  | intro (e x f y) : p (.inl e) x (.inl f) y → inl_postrel p e x f y
inductive inr_postrel (p : postrel (E ⊕ₑ G) (F ⊕ₑ H)) : postrel G H where
  | intro (e x f y) : p (.inr e) x (.inr f) y → inr_postrel p e x f y
abbrev Inl_prerel := @inl_prerel.intro
abbrev Inr_prerel := @inr_prerel.intro
abbrev Inl_postrel := @inl_postrel.intro
abbrev Inr_postrel := @inr_postrel.intro

abbrev cmp (L : pred1 E) (K : pred1 F) (V : prerel E F) (A : postrel E F) (Q : X → Y → Prop) :
    Comparison E F X Y := ⟨true, true, L, K, V, A, Q⟩
abbrev ruttcF L K V A (Q : X → Y → Prop) := @Layer E F B X Y (cmp L K V A Q)
abbrev ruttc_mon L K V A (Q : X → Y → Prop) := @layerMon E F X Y B (cmp L K V A Q)
abbrev ruttc_ L K V A (Q : X → Y → Prop) := (ruttc_mon (E := E) (F := F) (B := B) L K V A Q).body
abbrev ruttc L K V A (Q : X → Y → Prop) := @Vellvm.Tree.ruttc E F B X Y L K V A Q

section Constructors
variable {L : pred1 E} {K : pred1 F} {V : prerel E F} {A : postrel E F} {Q : X → Y → Prop}
variable {C : Rel (CTree E B X) (CTree F B Y)}
theorem EqRet (x y) (h : Q x y) : ruttcF L K V A Q C (.ret x) (.ret y) := .ret h
theorem EqTau (t s) (h : C t s) : ruttcF L K V A Q C (.guard t) (.guard s) := .guard h
theorem EqVis (e f k l) (h : V e f) (hk : ∀ x y, A e x f y → C (k x) (l y)) :
    ruttcF L K V A Q C (.vis e k) (.vis f l) := .vis h hk
theorem EqTauL (t : CTree E B X) (r) (h : ruttcF L K V A Q C t.unfold r) :
    ruttcF L K V A Q C (.guard t) r := .skipL rfl h
theorem EqTauR (l) (s : CTree F B Y) (h : ruttcF L K V A Q C l s.unfold) :
    ruttcF L K V A Q C l (.guard s) := .skipR rfl h
theorem EqCutL (e k r) (h : L e) : ruttcF L K V A Q C (.vis e k) r := .cutL h
theorem EqCutR (f l k) (h : K f) : ruttcF L K V A Q C l (.vis f k) := .cutR h
end Constructors

abbrev inrMap (G : Effect.{u}) {E : Effect.{u}} (e : E.I) : (f : (G ⊕ₑ E).I) × ((G ⊕ₑ E).O f → E.O e) :=
  ⟨.inr e, id⟩

theorem eq_REv_sum_prerel : ∀ {E F G H : Effect.{u}} (v v' : prerel E F),
    eq_REv v v' → ∀ (w w' : prerel G H), eq_REv w w' →
    eq_REv (sum_prerel v w) (sum_prerel v' w') := by
  intro E F G H v v' hv w w' hw i j
  constructor <;> intro h <;> cases h with
  | inl h => exact .inl (by first | exact (hv _ _).mp h | exact (hv _ _).mpr h)
  | inr h => exact .inr (by first | exact (hw _ _).mp h | exact (hw _ _).mpr h)

theorem eq_REv_sum_rel_inl : ∀ {E F G H : Effect.{u}} (v : prerel E F) (w : prerel G H),
    eq_REv (inl_prerel (sum_prerel v w)) v := by
  intro E F G H v w i j
  constructor
  · rintro ⟨_, _, h⟩; cases h with | inl h => exact h
  · exact fun h ↦ .intro _ _ (.inl h)

theorem eq_REv_sum_rel_inr : ∀ {E F G H : Effect.{u}} (v : prerel E F) (w : prerel G H),
    eq_REv (inr_prerel (sum_prerel v w)) w := by
  intro E F G H v w i j
  constructor
  · rintro ⟨_, _, h⟩; cases h with | inr h => exact h
  · exact fun h ↦ .intro _ _ (.inr h)

theorem eq_RAns_sum_rel_inr : ∀ {E F G H : Effect.{u}} (a : postrel E F) (b : postrel G H),
    eq_RAns (inr_postrel (sum_postrel a b)) b := by
  intro E F G H a b i x j y
  exact ⟨fun ⟨_, _, _, _, h⟩ ↦ h, fun h ↦ .intro _ _ _ _ h⟩

theorem ruttcF_ind : ∀ {E F B : Effect.{u}} {X Y : Type u} (L : pred1 E) (K : pred1 F) (V : prerel E F) (A : postrel E F) (Q : X → Y → Prop) (C : Rel (CTree E B X) (CTree F B Y)) (P : Head E B X → Head F B Y → Prop),
    (∀ x y, Q x y → P (.ret x) (.ret y)) →
    (∀ t s, C t s → P (.guard t) (.guard s)) →
    (∀ e f k l, V e f → (∀ a b, A e a f b → C (k a) (l b)) → P (.vis e k) (.vis f l)) →
    (∀ (t : CTree E B X) s, ruttcF L K V A Q C t.unfold s → P t.unfold s → P (.guard t) s) →
    (∀ t (s : CTree F B Y), ruttcF L K V A Q C t s.unfold → P t s.unfold → P t (.guard s)) →
    (∀ e k s, L e → P (.vis e k) s) → (∀ f k t, K f → P t (.vis f k)) →
    P .stuck .stuck → (∀ t s, C t s → P (.step t) (.step s)) →
    (∀ c k l, (∀ a, C (k a) (l a)) → P (.br c k) (.br c l)) →
    ∀ l r, ruttcF L K V A Q C l r → P l r := by
  intro E F B X Y L K V A Q C P ret guard vis skL skR cutL cutR stuck step br l r h
  induction h with
  | ret h => exact ret _ _ h
  | guard h => exact guard _ _ h
  | vis h hk => exact vis _ _ _ _ h hk
  | skipL _ h ih => exact skL _ _ h ih
  | skipR _ h ih => exact skR _ _ h ih
  | cutL h => exact cutL _ _ _ h
  | cutR h => exact cutR _ _ _ h
  | stuck => exact stuck
  | step h => exact step _ _ h
  | br h => exact br _ _ _ h

theorem ruttcF_sind : ∀ {E F B : Effect.{u}} {X Y : Type u} (L : pred1 E) (K : pred1 F) (V : prerel E F) (A : postrel E F) (Q : X → Y → Prop) (C : Rel (CTree E B X) (CTree F B Y)) (P : Head E B X → Head F B Y → Prop),
    (∀ x y, Q x y → P (.ret x) (.ret y)) →
    (∀ t s, C t s → P (.guard t) (.guard s)) →
    (∀ e f k l, V e f → (∀ a b, A e a f b → C (k a) (l b)) → P (.vis e k) (.vis f l)) →
    (∀ (t : CTree E B X) s, ruttcF L K V A Q C t.unfold s → P t.unfold s → P (.guard t) s) →
    (∀ t (s : CTree F B Y), ruttcF L K V A Q C t s.unfold → P t s.unfold → P t (.guard s)) →
    (∀ e k s, L e → P (.vis e k) s) → (∀ f k t, K f → P t (.vis f k)) →
    P .stuck .stuck → (∀ t s, C t s → P (.step t) (.step s)) →
    (∀ c k l, (∀ a, C (k a) (l a)) → P (.br c k) (.br c l)) →
    ∀ l r, ruttcF L K V A Q C l r → P l r := by
  exact @ruttcF_ind

theorem ruttc_mono : ∀ {E F B : Effect.{u}} {X Y : Type u} (L : pred1 E) (K : pred1 F) (V : prerel E F) (A : postrel E F) (Q : X → Y → Prop) (C D : Rel (CTree E B X) (CTree F B Y)),
    C ≤ D → (ruttc_mon (B := B) L K V A Q) C ≤ (ruttc_mon (B := B) L K V A Q) D := by
  intro E F B X Y L K V A Q C D h; exact (ruttc_mon (B := B) L K V A Q).mono h

theorem ruttc_to_mon_obs : ∀ {E F B : Effect.{u}} {X Y : Type u} (L : pred1 E) (K : pred1 F) (V : prerel E F) (A : postrel E F) (Q : X → Y → Prop) (C : Rel (CTree E B X) (CTree F B Y)) (t : CTree E B X) (s : CTree F B Y),
    ruttcF L K V A Q C t.unfold s.unfold = (ruttc_mon (B := B) L K V A Q) C t s := by
  intros; rfl

theorem ruttc_to_mon_go : ∀ {E F B : Effect.{u}} {X Y : Type u} (L : pred1 E) (K : pred1 F) (V : prerel E F) (A : postrel E F) (Q : X → Y → Prop) (C : Rel (CTree E B X) (CTree F B Y)) (l : Head E B X) (r : Head F B Y),
    ruttcF L K V A Q C l r = (ruttc_mon (B := B) L K V A Q) C (.fold l) (.fold r) := by
  intros; simp only [ruttc_mon, layerMon, unfold_fold]

theorem ruttc_weaken : ∀ {E F B : Effect.{u}} {X Y : Type u} (L L' : pred1 E) (K K' : pred1 F) (V V' : prerel E F)
    (A A' : postrel E F) (Q Q' : X → Y → Prop),
    (∀ e, L e → L' e) → (∀ f, K f → K' f) → (∀ e f, V e f → V' e f) →
    (∀ e a f b, A' e a f b → A e a f b) → (∀ x y, Q x y → Q' x y) →
    ∀ (t : CTree E B X) (s : CTree F B Y), ruttc L K V A Q t s → ruttc L' K' V' A' Q' t s := by
  intro E F B X Y L L' K K' V V' A A' Q Q' hl hk hv ha hq
  apply gfp_mono (b := ruttc_mon (B := B) L K V A Q) (c := ruttc_mon L' K' V' A' Q')
  intro R t s h
  change Layer _ R t.unfold s.unfold at h ⊢
  generalize t.unfold = u at h ⊢
  generalize s.unfold = v at h ⊢
  induction h with
  | ret h => exact .ret (hq _ _ h)
  | guard h => exact .guard h
  | vis h k => exact .vis (hv _ _ h) fun x y xy ↦ k x y (ha _ _ _ _ xy)
  | skipL _ _ ih => exact .skipL rfl ih
  | skipR _ _ ih => exact .skipR rfl ih
  | cutL h => exact .cutL (hl _ h)
  | cutR h => exact .cutR (hk _ h)
  | stuck => exact .stuck
  | step h => exact .step h
  | br h => exact .br h

theorem ruttc_Proper_R : ∀ {E F B : Effect.{u}} {X Y : Type u} (L L' : pred1 E),
    eqp1 L L' → ∀ K K', eqp1 K K' → ∀ V V', eq_REv V V' → ∀ A A', eq_RAns A A' →
    ∀ (Q Q' : X → Y → Prop), (∀ x y, Q x y ↔ Q' x y) →
    ∀ (t t' : CTree E B X), t = t' → ∀ (s s' : CTree F B Y), s = s' →
    (ruttc L K V A Q t s ↔ ruttc L' K' V' A' Q' t' s') := by
  intro E F B X Y L L' hl K K' hk V V' hv A A' ha Q Q' hq t _ rfl s _ rfl
  constructor
  · apply ruttc_weaken <;> intros <;> first | exact (hl _).mp ‹_› | exact (hk _).mp ‹_› | exact (hv _ _).mp ‹_› | exact (ha _ _ _ _).mpr ‹_› | exact (hq _ _).mp ‹_›
  · apply ruttc_weaken <;> intros <;> first | exact (hl _).mpr ‹_› | exact (hk _).mpr ‹_› | exact (hv _ _).mpr ‹_› | exact (ha _ _ _ _).mp ‹_› | exact (hq _ _).mpr ‹_›

theorem ruttc_ret : ∀ {E F B : Effect.{u}} {X Y : Type u} {L : pred1 E} {K : pred1 F} {V : prerel E F} {A : postrel E F} {Q : X → Y → Prop} (x : X) (y : Y),
    Q x y → ruttc L K V A (B := B) Q (.ret x) (.ret y) := by
  intro E F B X Y L K V A Q x y h
  apply related_iff.mpr; rw [unfold_ret, unfold_ret]; exact .ret h

theorem ruttc_trigger : ∀ {E F B : Effect.{u}} {L : pred1 E} {K : pred1 F} {V : prerel E F} {A : postrel E F} (e : E.I) (f : F.I) {Q : E.O e → F.O f → Prop},
    V e f → (∀ a b, A e a f b → Q a b) →
    ruttc L K V A (B := B) Q (CTree.trigger e) (CTree.trigger f) := by
  intro E F B L K V A e f Q h hk
  apply related_iff.mpr; simp only [CTree.trigger, unfold_vis]
  exact .vis h fun a b ab ↦ ruttc_ret a b (hk a b ab)

theorem ruttc_trigger_cast : ∀ {E F B : Effect.{u}} {X Y : Type u} {L : pred1 E} {K : pred1 F} {V : prerel E F} {A : postrel E F} {Q : X → Y → Prop} (e : E.I) (f : F.I) (he : E.O e = PEmpty) (hf : F.O f = PEmpty),
    V e f → ruttc L K V A (B := B) Q (trigger_cast' e he) (trigger_cast' f hf) := by
  intro E F B X Y L K V A Q e f he hf h
  apply related_iff.mpr; simp only [trigger_cast', CTree.trigger, vis_bind, unfold_vis]
  exact .vis h fun a ↦ PEmpty.elim (he ▸ a)

theorem ruttc_trigger_cutl : ∀ {E F B : Effect.{u}} {X Y : Type u} {L : pred1 E} {K : pred1 F} {V : prerel E F} {A : postrel E F} {Q : X → Y → Prop} (e : E.I) (k : E.O e → CTree E B X) (s : CTree F B Y),
    L e → ruttc L K V A Q (CTree.trigger e >>= k) s := by
  intro E F B X Y L K V A Q e k s h
  apply related_iff.mpr; simp only [CTree.trigger, vis_bind, unfold_vis]; exact .cutL h

theorem ruttc_trigger_cutr : ∀ {E F B : Effect.{u}} {X Y : Type u} {L : pred1 E} {K : pred1 F} {V : prerel E F} {A : postrel E F} {Q : X → Y → Prop} (t : CTree E B X) (f : F.I) (k : F.O f → CTree F B Y),
    K f → ruttc L K V A Q t (CTree.trigger f >>= k) := by
  intro E F B X Y L K V A Q t e k h
  apply related_iff.mpr; simp only [CTree.trigger, vis_bind, unfold_vis]; exact .cutR h

theorem ruttc_trigger' : ∀ {E F B : Effect.{u}} {X Y : Type u} {L : pred1 E} {K : pred1 F} {V : prerel E F} {A : postrel E F} {Q : X → Y → Prop} (e : E.I) (f : F.I)
    (k : E.O e → CTree E B X) (l : F.O f → CTree F B Y),
    V e f → (∀ a b, A e a f b → ruttc L K V A Q (k a) (l b)) →
    ruttc L K V A Q (CTree.trigger e >>= k) (CTree.trigger f >>= l) := by
  intro E F B X Y L K V A Q e f k l h hk
  apply related_iff.mpr; simp only [CTree.trigger, vis_bind, unfold_vis, pure_bind]; exact .vis h hk

theorem ruttc_bind_chain : ∀ {E F B : Effect.{u}} {X Y : Type u} (L : pred1 E) (K : pred1 F) (V : prerel E F) (A : postrel E F) (Q : X → Y → Prop) (C : Rel (CTree E B X) (CTree F B Y)) (hc : Chain (ruttc_mon (B := B) L K V A Q) C) (U W : Type u) (P : U → W → Prop)
    (t : CTree E B U) (s : CTree F B W) (k : U → CTree E B X) (l : W → CTree F B Y),
    ruttc L K V A P t s → (∀ x y, P x y → C (k x) (l y)) →
    C (t >>= k) (s >>= l) := by
  intro E F B X Y L K V A Q C hc
  induction hc with
  | inf h ih =>
    intro U W P t s k l hts hk
    exact Rel.inf_apply.mpr fun R hr ↦ ih R hr U W P t s k l hts
      (fun x y xy ↦ Rel.inf_apply.mp (hk x y xy) R hr)
  | step hc ih =>
    intro U W P t s k l hts hk
    have resume := fun a b (hab : ruttc L K V A P a b) ↦ ih U W P a b k l hab
      (fun x y xy ↦ b_chain hc _ _ (hk x y xy))
    have hh := related_iff.mp hts
    suffices ∀ u v, ruttcF L K V A P (ruttc L K V A P) u v →
        ruttcF L K V A Q _ ((CTree.fold u >>= k).unfold) ((CTree.fold v >>= l).unfold) by
      simpa only [layerMon, fold_unfold] using this _ _ hh
    intro u v h
    induction h with
    | ret h => simpa only [fold_ret, ret_eq_pure, pure_bind', layerMon] using hk _ _ h
    | guard h => simp only [fold_guard, guard_bind, unfold_guard]; exact .guard (resume _ _ h)
    | vis h ks => simp only [fold_vis, vis_bind, unfold_vis]; exact .vis h fun x y xy ↦ resume _ _ (ks x y xy)
    | skipL _ _ hi => simp only [fold_guard, guard_bind, unfold_guard]; exact .skipL rfl (by simpa only [fold_unfold] using hi)
    | skipR _ _ hi => simp only [fold_guard, guard_bind, unfold_guard]; exact .skipR rfl (by simpa only [fold_unfold] using hi)
    | cutL h => simp only [fold_vis, vis_bind, unfold_vis]; exact .cutL h
    | cutR h => simp only [fold_vis, vis_bind, unfold_vis]; exact .cutR h
    | stuck => simp only [fold_stuck, stuck_bind, unfold_stuck]; exact .stuck
    | step h => simp only [fold_step, step_bind, unfold_step]; exact .step (resume _ _ h)
    | br h => simp only [fold_br, br_bind, unfold_br]; exact .br fun x ↦ resume _ _ (h x)

theorem ruttc_bind_bchain : ∀ {E F B : Effect.{u}} {X Y : Type u} (L : pred1 E) (K : pred1 F) (V : prerel E F) (A : postrel E F) (Q : X → Y → Prop) (C : Rel (CTree E B X) (CTree F B Y)) (hc : Chain (ruttc_mon (B := B) L K V A Q) C) (U W : Type u) (P : U → W → Prop)
    (t : CTree E B U) (s : CTree F B W) (k : U → CTree E B X) (l : W → CTree F B Y),
    ruttc L K V A P t s → (∀ x y, P x y → (ruttc_mon (B := B) L K V A Q) C (k x) (l y)) →
    (ruttc_mon (B := B) L K V A Q) C (t >>= k) (s >>= l) := by
  intro E F B X Y L K V A Q C hc
  exact ruttc_bind_chain L K V A Q _ (.step hc)

theorem ruttc_bind : ∀ {E F B : Effect.{u}} {X Y U W : Type u} (L : pred1 E) (K : pred1 F) (V : prerel E F) (A : postrel E F) (Q : X → Y → Prop) (P : U → W → Prop) (t : CTree E B X) (s : CTree F B Y)
    (k : X → CTree E B U) (l : Y → CTree F B W),
    ruttc L K V A Q t s → (∀ x y, Q x y → ruttc L K V A P (k x) (l y)) →
    ruttc L K V A P (t >>= k) (s >>= l) := by
  intro E F B X Y U W L K V A Q P t s k l
  exact ruttc_bind_chain L K V A P _ (gfp_chain _) X Y Q t s k l

theorem ruttc_iter : ∀ {E F B : Effect.{u}} {U W X Y : Type u} (L : pred1 E) (K : pred1 F) (V : prerel E F) (A : postrel E F) (Q : X → Y → Prop) (P : U → W → Prop)
    (f : U → CTree E B (U ⊕ X)) (g : W → CTree F B (W ⊕ Y)),
    (∀ i j, P i j → ruttc L K V A (sum_rel P Q) (f i) (g j)) → ∀ i j, P i j →
    ruttc L K V A Q (CTree.iter f i) (CTree.iter g j) := by
  intro E F B U W X Y L K V A Q P f g hb
  coinduction C hc ih
  intro i j ij
  rw [unfold_iter, unfold_iter]
  apply ruttc_bind_bchain L K V A Q C hc _ _ (sum_rel P Q) _ _ _ _ (hb i j ij)
  intro a b hab
  cases hab with
  | inl h => change Layer _ C _ _; simp only [unfold_guard]; exact .guard (ih _ _ h)
  | inr h => change Layer _ C _ _; simp only [unfold_pure]; exact .ret h

private abbrev swap (p : Comparison E F X Y) : Comparison F E Y X :=
  ⟨p.skipR, p.skipL, p.cutR, p.cutL, fun f e ↦ p.event e f,
    fun f b e a ↦ p.answer e a f b, fun y x ↦ p.result x y⟩

private theorem flipLayer {p : Comparison E F X Y} {C : Rel (CTree E B X) (CTree F B Y)}
    {l r} (h : Layer p C l r) : Layer (swap p) (fun s t ↦ C t s) r l := by
  induction h with
  | ret h => exact .ret h
  | guard h => exact .guard h
  | vis h k => exact .vis h fun b a ab ↦ k a b ab
  | skipL f _ ih => exact .skipR f ih
  | skipR f _ ih => exact .skipL f ih
  | cutL h => exact .cutR h
  | cutR h => exact .cutL h
  | stuck => exact .stuck
  | step h => exact .step h
  | br h => exact .br h

private theorem flipRelated (p : Comparison E F X Y) : ∀ (t : CTree E B X) (s : CTree F B Y),
    Related p t s → Related (swap p) s t := by
  coinduction C hc ih
  intro t s h
  exact (flipLayer (related_iff.mp h)).mono fun _ _ ↦ ih _ _

theorem ruttc_flip : ∀ {E F B : Effect.{u}} {X Y : Type u} {L : pred1 E} {K : pred1 F} {V : prerel E F} {A : postrel E F} {Q : X → Y → Prop} (t : CTree E B X) (s : CTree F B Y),
    ruttc L K V A Q t s ↔ ruttc K L (fun f e ↦ V e f) (fun f b e a ↦ A e a f b) (fun y x ↦ Q x y) s t := by
  intro E F B X Y L K V A Q t s
  exact ⟨flipRelated _ t s, flipRelated (swap (cmp L K V A Q)) s t⟩

private theorem invGuardL {p : Comparison E F X Y} (hr : p.skipR = true)
    (t : CTree E B X) (s : CTree F B Y) (h : Related p t.guard s) : Related p t s := by
  have hh := related_iff.mp h
  rw [unfold_guard] at hh
  apply related_iff.mpr
  suffices peel : ∀ l r, Layer p (Related p) l r → ∀ t : CTree E B X,
      .guard t = l → Layer p (Related p) t.unfold r from peel _ _ hh _ rfl
  intro l r lay
  induction lay with
  | guard h => rintro t ⟨⟩; exact .skipR hr (related_iff.mp h)
  | skipL _ h _ => rintro t ⟨⟩; exact h
  | skipR _ _ ih => intro t he; exact .skipR hr (ih _ he)
  | cutR h => intros; exact .cutR h
  | _ => intros; contradiction

theorem ruttc_inv_Tau_l : ∀ {E F B : Effect.{u}} {X Y : Type u} (K : pred1 F) (L : pred1 E) (V : prerel E F) (A : postrel E F) {Q : X → Y → Prop} (t : CTree E B X) (s : CTree F B Y),
    ruttc L K V A Q t.guard s → ruttc L K V A Q t s := by
  intro E F B X Y K L V A Q t s h; exact invGuardL rfl t s h

theorem ruttc_inv_Tau_r : ∀ {E F B : Effect.{u}} {X Y : Type u} (K : pred1 F) (L : pred1 E) (V : prerel E F) (A : postrel E F) {Q : X → Y → Prop} (t : CTree E B X) (s : CTree F B Y),
    ruttc L K V A Q t s.guard → ruttc L K V A Q t s := by
  intro E F B X Y K L V A Q t s h
  exact (ruttc_flip t s).mpr (invGuardL rfl _ _ ((ruttc_flip t s.guard).mp h))

theorem ruttc_inv_Tau : ∀ {E F B : Effect.{u}} {X Y : Type u} (K : pred1 F) (L : pred1 E) (V : prerel E F) (A : postrel E F) {Q : X → Y → Prop} (t : CTree E B X) (s : CTree F B Y),
    ruttc L K V A Q t.guard s.guard → ruttc L K V A Q t s := by
  intro E F B X Y K L V A Q t s h
  exact ruttc_inv_Tau_l K L V A t s (ruttc_inv_Tau_r K L V A t.guard s h)

private theorem translateRight {L : pred1 E} {K : pred1 F} {V : prerel E F} {A : postrel E F}
    {L' : pred1 (G ⊕ₑ E)} {K' : pred1 (H ⊕ₑ F)} {V' : prerel (G ⊕ₑ E) (H ⊕ₑ F)}
    {A' : postrel (G ⊕ₑ E) (H ⊕ₑ F)} {Q : X → Y → Prop}
    (hl : ∀ e, L e → L' (.inr e)) (hr : ∀ f, K f → K' (.inr f))
    (hv : ∀ e f, V e f → V' (.inr e) (.inr f))
    (ha : ∀ e a f b, A' (.inr e) a (.inr f) b → A e a f b) :
    ∀ (t : CTree E B X) (s : CTree F B Y), ruttc L K V A Q t s →
      ruttc L' K' V' A' Q (translate (inrMap G) t) (translate (inrMap H) s) := by
  coinduction C hc ih
  intro t s h
  suffices go : ∀ u v, ruttcF L K V A Q (ruttc L K V A Q) u v → ruttcF L' K' V' A' Q C
      (translate (inrMap G) (.fold u)).unfold (translate (inrMap H) (.fold v)).unfold by
    simpa only [layerMon, fold_unfold] using go _ _ (related_iff.mp h)
  intro u v hh
  induction hh with
  | ret h => simp only [fold_ret, ret_eq_pure, translate_ret, unfold_pure]; exact .ret h
  | guard h => simp only [fold_guard, translate_guard, unfold_guard]; exact .guard (ih _ _ h)
  | vis h k => simp only [fold_vis, translate_vis, unfold_vis]; exact .vis (hv _ _ h) fun a b ab ↦ ih _ _ (k _ _ (ha _ _ _ _ ab))
  | skipL _ _ hi => simp only [fold_guard, translate_guard, unfold_guard]; exact .skipL rfl (by simpa only [fold_unfold] using hi)
  | skipR _ _ hi => simp only [fold_guard, translate_guard, unfold_guard]; exact .skipR rfl (by simpa only [fold_unfold] using hi)
  | cutL h => simp only [fold_vis, translate_vis, unfold_vis]; exact .cutL (hl _ h)
  | cutR h => simp only [fold_vis, translate_vis, unfold_vis]; exact .cutR (hr _ h)
  | stuck => simp only [fold_stuck, translate_stuck, unfold_stuck]; exact .stuck
  | step h => simp only [fold_step, translate_step, unfold_step]; exact .step (ih _ _ h)
  | br h => simp only [fold_br, translate_br, unfold_br]; exact .br fun a ↦ ih _ _ (h a)

theorem ruttc_translate_inr : ∀ {E F G H B : Effect.{u}} {X Y : Type u} (L : pred1 E) (K : pred1 F) (V : prerel E F) (A : postrel E F) (V' : prerel G H) (A' : postrel G H) (Q : X → Y → Prop) (t : CTree E B X) (s : CTree F B Y),
    ruttc L K V A Q t s → ruttc (sum_pred1 TT1 L) (sum_pred1 TT1 K) (sum_prerel V' V)
      (sum_postrel A' A) Q (translate (inrMap G) t) (translate (inrMap H) s) := by
  intro E F G H B X Y L K V A V' A' Q t s
  exact translateRight (L' := sum_pred1 TT1 L) (K' := sum_pred1 TT1 K)
    (V' := sum_prerel V' V) (A' := sum_postrel A' A) (A := A)
    (fun _ h ↦ .inr _ h) (fun _ h ↦ .inr _ h) (fun _ _ h ↦ .inr h) (fun _ _ _ _ h ↦ h) t s

theorem ruttc_translate_inr' : ∀ {E F G H B : Effect.{u}} {X Y : Type u} (L : pred1 E) (K : pred1 F) (V : prerel E F) (A : postrel E F) (L' : pred1 (G ⊕ₑ E)) (K' : pred1 (H ⊕ₑ F))
    (V' : prerel (G ⊕ₑ E) (H ⊕ₑ F)) (A' : postrel (G ⊕ₑ E) (H ⊕ₑ F)) (Q : X → Y → Prop),
    eqp1 L' (sum_pred1 FF1 L) → eqp1 K' (sum_pred1 FF1 K) →
    eq_REv (inr_prerel V') V → eq_RAns (inr_postrel A') A →
    ∀ (t : CTree E B X) (s : CTree F B Y), ruttc L K V A Q t s →
    ruttc L' K' V' A' Q (translate (inrMap G) t) (translate (inrMap H) s) := by
  intro E F G H B X Y L K V A L' K' V' A' Q hl hr hv ha
  exact translateRight (fun _ h ↦ (hl _).mpr (.inr _ h)) (fun _ h ↦ (hr _).mpr (.inr _ h))
    (fun e f h ↦ by obtain ⟨_, _, h⟩ := (hv e f).mpr h; exact h)
    (fun e a f b h ↦ (ha e a f b).mp (.intro _ _ _ _ h))

private theorem chainGuard {p : Comparison E F X Y} {C : Rel (CTree E B X) (CTree F B Y)}
    (hc : Chain (layerMon B p) C) {t s} (h : C t s) : C t.guard s.guard := by
  apply b_chain hc
  change Layer p C _ _
  rw [unfold_guard, unfold_guard]; exact .guard h

theorem ruttc_interp_mrec : ∀ {D G E F B : Effect.{u}} {X Y : Type u} (L : pred1 E) (K : pred1 F) (V : prerel E F) (J : prerel D G) (N : postrel D G) (A : postrel E F) (Q : X → Y → Prop)
    (f : (d : D.I) → CTree (D ⊕ₑ E) B (D.O d))
    (g : (d : G.I) → CTree (G ⊕ₑ F) B (G.O d)),
    (∀ d e, J d e → ruttc (sum_pred1 FF1 L) (sum_pred1 FF1 K) (sum_prerel J V) (sum_postrel N A)
      (fun x y ↦ N d x e y) (f d) (g e)) → ∀ t s,
    ruttc (sum_pred1 FF1 L) (sum_pred1 FF1 K) (sum_prerel J V) (sum_postrel N A) Q t s → ruttc L K V A Q (interp_mrec f t) (interp_mrec g s) := by
  intro D G E F B X Y L K V J N A Q f g hb
  coinduction C hc ih
  intro t s h
  let op := cmp (sum_pred1 FF1 L) (sum_pred1 FF1 K) (sum_prerel J V) (sum_postrel N A) Q
  suffices go : ∀ u v, Layer op (Related op) u v → ruttcF L K V A Q C
      (interp_mrec f (.fold u)).unfold (interp_mrec g (.fold v)).unfold by
    simpa only [layerMon, fold_unfold] using go _ _ (related_iff.mp h)
  intro u v hh
  induction hh with
  | ret h => simp only [fold_ret, ret_eq_pure, interp_mrec_ret, unfold_pure]; exact .ret h
  | guard h => simp only [fold_guard, interp_mrec_guard_eq, unfold_guard]; exact .guard (ih _ _ h)
  | vis h k =>
    cases h with
    | inl h =>
      simp only [fold_vis, interp_mrec_vis_inl, unfold_guard]
      exact .guard (ih _ _ (ruttc_bind _ _ _ _ _ _ _ _ _ _ (hb _ _ h) fun a b ab ↦ k _ _ ab))
    | inr h =>
      simp only [fold_vis, interp_mrec_vis_inr, unfold_vis]
      exact .vis h fun a b ab ↦ chainGuard hc (ih _ _ (k a b ab))
  | skipL _ _ hi => simp only [fold_guard, interp_mrec_guard_eq, unfold_guard]; exact .skipL rfl (by simpa only [fold_unfold] using hi)
  | skipR _ _ hi => simp only [fold_guard, interp_mrec_guard_eq, unfold_guard]; exact .skipR rfl (by simpa only [fold_unfold] using hi)
  | cutL h =>
    cases h with
    | inl _ h => exact h.elim
    | inr _ h => simp only [fold_vis, interp_mrec_vis_inr, unfold_vis]; exact .cutL h
  | cutR h =>
    cases h with
    | inl _ h => exact h.elim
    | inr _ h => simp only [fold_vis, interp_mrec_vis_inr, unfold_vis]; exact .cutR h
  | stuck => simp only [fold_stuck, interp_mrec_stuck, unfold_stuck]; exact .stuck
  | step h => simp only [fold_step, interp_mrec_step, unfold_step]; exact .step (chainGuard hc (ih _ _ h))
  | br h => simp only [fold_br, interp_mrec_br, unfold_br]; exact .br fun a ↦ chainGuard hc (ih _ _ (h a))

theorem ruttc_mrec : ∀ {D G E F B : Effect.{u}} (L : pred1 E) (K : pred1 F) (V : prerel E F) (A : postrel E F) (J : prerel D G) (N : postrel D G)
    (f : (d : D.I) → CTree (D ⊕ₑ E) B (D.O d))
    (g : (d : G.I) → CTree (G ⊕ₑ F) B (G.O d)),
    (∀ d e, J d e → ruttc (sum_pred1 FF1 L) (sum_pred1 FF1 K) (sum_prerel J V) (sum_postrel N A)
      (fun x y ↦ N d x e y) (f d) (g e)) → ∀ d e, J d e →
    ruttc L K V A (fun x y ↦ N d x e y) (mrec f d) (mrec g e) := by
  intro D G E F B L K V A J N f g hb d e de
  exact ruttc_interp_mrec L K V J N A _ f g hb _ _ (hb d e de)

private theorem strongVis {e : E.I} {k : E.O e → CTree E B X} {t : CTree E B X}
    (h : eqit Eq false false t (.vis e k)) : ∃ l, t = .vis e l := by
  have hh := related_iff.mp h
  rw [unfold_vis] at hh
  obtain ⟨l, eq⟩ : ∃ l, t.unfold = .vis e l := by
    generalize t.unfold = u at hh ⊢
    cases hh with
    | vis he _ => cases he; exact ⟨_, rfl⟩
    | skipL h _ => cases h
    | cutL h => exact h.elim
    | cutR h => exact h.elim
  exact ⟨l, unfold_inj (eq.trans (unfold_vis _ _).symm)⟩

theorem ruttc_interp_itree : ∀ {E F B : Effect.{u}} {X Y : Type u} {L : pred1 E} {K : pred1 F} {V : prerel E F} {A : postrel E F} {Q : X → Y → Prop} (f : (e : E.I) → CTree E B (E.O e))
    (g : (e : F.I) → CTree F B (F.O e)),
    (∀ e, L e → eqit Eq false false (f e) (CTree.trigger e)) →
    (∀ e, K e → eqit Eq false false (g e) (CTree.trigger e)) →
    (∀ e d, V e d → ruttc L K V A (fun x y ↦ A e x d y) (f e) (g d)) →
    ∀ (t : CTree E B X) (s : CTree F B Y), ruttc L K V A Q t s → ruttc L K V A Q (interp f t) (interp g s) := by
  intro E F B X Y L K V A Q f g hl hr hv
  coinduction C hc ih
  intro t s h
  suffices go : ∀ u v, ruttcF L K V A Q (ruttc L K V A Q) u v → ruttcF L K V A Q C
      (interp f (.fold u)).unfold (interp g (.fold v)).unfold by
    simpa only [layerMon, fold_unfold] using go _ _ (related_iff.mp h)
  intro u v hh
  induction hh with
  | ret h => simp only [fold_ret, ret_eq_pure, interp_ret, unfold_pure]; exact .ret h
  | guard h => simp only [fold_guard, interp_guard, unfold_guard]; exact .guard (ih _ _ h)
  | vis h k =>
    simp only [fold_vis, interp_vis]
    apply ruttc_bind_bchain L K V A Q C hc _ _ _ _ _ _ _ (hv _ _ h)
    intro a b ab
    change Layer _ C _ _; rw [unfold_guard, unfold_guard]; exact .guard (ih _ _ (k a b ab))
  | skipL _ _ hi => simp only [fold_guard, interp_guard, unfold_guard]; exact .skipL rfl (by simpa only [fold_unfold] using hi)
  | skipR _ _ hi => simp only [fold_guard, interp_guard, unfold_guard]; exact .skipR rfl (by simpa only [fold_unfold] using hi)
  | cutL h =>
    obtain ⟨k, hk⟩ := strongVis (hl _ h)
    simp only [fold_vis, interp_vis, hk, vis_bind, unfold_vis]; exact .cutL h
  | cutR h =>
    obtain ⟨k, hk⟩ := strongVis (hr _ h)
    simp only [fold_vis, interp_vis, hk, vis_bind, unfold_vis]; exact .cutR h
  | stuck => simp only [fold_stuck, interp_stuck, unfold_stuck]; exact .stuck
  | step h => simp only [fold_step, interp_step, unfold_step]; exact .step (chainGuard hc (ih _ _ h))
  | br h => simp only [fold_br, interp_br', CTree.br', unfold_br]; exact .br fun a ↦ chainGuard hc (ih _ _ (h a))

private inductive Lead : Head E B X → Head E B X → Prop where
  | refl (u) : Lead u u
  | more {t : CTree E B X} {u} : Lead t.unfold u → Lead (.guard t) u

private theorem leadLayer {p : Comparison E F X Y} {C : Rel (CTree E B X) (CTree F B Y)}
    {a b r} (hl : p.skipL = true) (h : Lead a b) (x : Layer p C b r) : Layer p C a r := by
  induction h with
  | refl => exact x
  | more _ ih => exact .skipL hl (ih x)

private inductive Sync (R : Rel (CTree E B X) (CTree E B X)) : Head E B X → Head E B X → Prop where
  | ret (x) : Sync R (.ret x) (.ret x)
  | guard {t s} : R t s → Sync R (.guard t) (.guard s)
  | vis (e) {k l} : (∀ a, R (k a) (l a)) → Sync R (.vis e k) (.vis e l)
  | stuck : Sync R .stuck .stuck
  | step {t s} : R t s → Sync R (.step t) (.step s)
  | br (c) {k l} : (∀ a, R (k a) (l a)) → Sync R (.br c k) (.br c l)

private abbrev LeftView (R : Rel (CTree E B X) (CTree E B X)) (u v : Head E B X) :=
  ∃ w, Lead u w ∧ Sync R w v

private theorem viewGE {u v : Head E B X}
    (h : Layer (Vellvm.Tree.eqitComparison E Eq true false) (euttge Eq) u v) :
    LeftView (euttge Eq) u v := by
  induction h with
  | ret h => cases h; exact ⟨_, .refl _, .ret _⟩
  | guard h => exact ⟨_, .refl _, .guard h⟩
  | vis e h => cases e; exact ⟨_, .refl _, .vis _ fun a ↦ h a a HEq.rfl⟩
  | skipL _ _ ih => obtain ⟨_, lead, sync⟩ := ih; exact ⟨_, .more lead, sync⟩
  | skipR h _ => cases h
  | cutL h => exact h.elim
  | cutR h => exact h.elim
  | stuck => exact ⟨_, .refl _, .stuck⟩
  | step h => exact ⟨_, .refl _, .step h⟩
  | br h => exact ⟨_, .refl _, .br _ h⟩

private theorem moveLeft {p : Comparison E F X Y} {C D : Rel (CTree E B X) (CTree F B Y)}
    {R : Rel (CTree E B X) (CTree E B X)} (hl : p.skipL = true) (good : Head E B X → Prop)
    (tail : ∀ {a b}, good (.guard b) → R a b → good b.unfold ∧ LeftView R a.unfold b.unfold)
    (resume : ∀ {t u s}, R t u → D u s → C t s) {l r} (h : Layer p D l r) :
    good l → ∀ l', LeftView R l' l → Layer p C l' r := by
  induction h with
  | ret h =>
    rintro _ _ ⟨_, lead, sync⟩; apply leadLayer hl lead
    cases sync with | ret => exact .ret h
  | guard h =>
    rintro _ _ ⟨_, lead, sync⟩; apply leadLayer hl lead
    cases sync with | guard eq => exact .guard (resume eq h)
  | vis h k =>
    rintro _ _ ⟨_, lead, sync⟩; apply leadLayer hl lead
    cases sync with | vis _ eq => exact .vis h fun a b ab ↦ resume (eq a) (k a b ab)
  | skipL _ _ ih =>
    rintro g _ ⟨_, lead, sync⟩; apply leadLayer hl lead
    cases sync with | guard eq => exact .skipL hl (ih (tail g eq).1 _ (tail g eq).2)
  | skipR hr _ ih => intro g l v; exact .skipR hr (ih g l v)
  | cutL h =>
    rintro _ _ ⟨_, lead, sync⟩; apply leadLayer hl lead
    cases sync with | vis => exact .cutL h
  | cutR h => intros; exact .cutR h
  | stuck =>
    rintro _ _ ⟨_, lead, sync⟩; apply leadLayer hl lead
    cases sync with | stuck => exact .stuck
  | step h =>
    rintro _ _ ⟨_, lead, sync⟩; apply leadLayer hl lead
    cases sync with | step eq => exact .step (resume eq h)
  | br h =>
    rintro _ _ ⟨_, lead, sync⟩; apply leadLayer hl lead
    cases sync with | br _ eq => exact .br fun a ↦ resume (eq a) (h a)

private theorem moveGE {p : Comparison E F X Y} {C : Rel (CTree E B X) (CTree F B Y)}
    (hl : p.skipL = true) (resume : ∀ {t u s}, euttge Eq t u → C u s → C t s) {u r}
    (h : Layer p C u r) {t t' : CTree E B X} (eq : euttge Eq t t') (he : t'.unfold = u) :
    Layer p C t.unfold r := by
  subst u
  exact moveLeft (C := C) (D := C) (R := euttge Eq) hl (fun _ ↦ True)
    (fun _ eq ↦ ⟨trivial, viewGE (related_iff.mp eq)⟩)
    resume h trivial _ (viewGE (related_iff.mp eq))

theorem euttge_proper_ruttcChain : ∀ {E F B : Effect.{u}} {X Y : Type u} {L : pred1 E} {K : pred1 F} {V : prerel E F} {A : postrel E F} {Q : X → Y → Prop} (C : Rel (CTree E B X) (CTree F B Y)) (hc : Chain (ruttc_mon (B := B) L K V A Q) C) (t t' : CTree E B X),
    euttge Eq t t' → ∀ (s s' : CTree F B Y), euttge Eq s s' →
    C t' s' → C t s := by
  intro E F B X Y L K V A Q C hc
  induction hc with
  | inf h ih =>
    intro t u tu s v sv h
    exact Rel.inf_apply.mpr fun R hr ↦ ih _ hr _ _ tu _ _ sv (Rel.inf_apply.mp h _ hr)
  | step hc ih =>
    intro t u tu s v sv h
    have left := moveGE (p := cmp L K V A Q) rfl
      (fun {a b z} eq hab ↦ ih a b eq z z (Vellvm.Tree.eqit_refl true false z) hab) h tu rfl
    have right := moveGE (p := swap (cmp L K V A Q)) rfl
      (fun {a b z} eq hab ↦ ih z z (Vellvm.Tree.eqit_refl true false z) a b eq hab)
      (flipLayer left) sv rfl
    exact flipLayer right

theorem euttge_proper_ruttcChain_mon : ∀ {E F B : Effect.{u}} {X Y : Type u} {L : pred1 E} {K : pred1 F} {V : prerel E F} {A : postrel E F} {Q : X → Y → Prop} (C : Rel (CTree E B X) (CTree F B Y)) (hc : Chain (ruttc_mon (B := B) L K V A Q) C) (t t' : CTree E B X),
    euttge Eq t t' → ∀ (s s' : CTree F B Y), euttge Eq s s' →
    (ruttc_mon (B := B) L K V A Q) C t' s' → (ruttc_mon (B := B) L K V A Q) C t s := by
  intro E F B X Y L K V A Q C hc
  exact euttge_proper_ruttcChain _ (.step hc)

theorem euttge_proper_ruttc : ∀ {E F B : Effect.{u}} {X Y : Type u} {L : pred1 E} {K : pred1 F} {V : prerel E F} {A : postrel E F} {Q : X → Y → Prop}  (t t' : CTree E B X),
    euttge Eq t t' → ∀ (s s' : CTree F B Y), euttge Eq s s' →
    ruttc L K V A Q t' s' → ruttc L K V A Q t s := by
  intro E F B X Y L K V A Q
  exact euttge_proper_ruttcChain _ (gfp_chain _)

private abbrev Stable (v : Head E B X) := ∀ t, v ≠ .guard t
private abbrev HasFront (t : CTree E B X) := ∃ v, Lead t.unfold v ∧ Stable v

private theorem viewStable {u v : Head E B X}
    (h : Layer (Vellvm.Tree.eqitComparison E Eq true true) (eutt Eq) u v) :
    Stable v → LeftView (eutt Eq) u v := by
  induction h with
  | ret h => intro _; cases h; exact ⟨_, .refl _, .ret _⟩
  | guard h => intro _; exact ⟨_, .refl _, .guard h⟩
  | vis e h => intro _; cases e; exact ⟨_, .refl _, .vis _ fun a ↦ h a a HEq.rfl⟩
  | skipL _ _ ih => intro hv; obtain ⟨_, lead, sync⟩ := ih hv; exact ⟨_, .more lead, sync⟩
  | skipR _ _ _ => intro hv; exact (hv _ rfl).elim
  | cutL h => exact h.elim
  | cutR h => exact h.elim
  | stuck => intro _; exact ⟨_, .refl _, .stuck⟩
  | step h => intro _; exact ⟨_, .refl _, .step h⟩
  | br h => intro _; exact ⟨_, .refl _, .br _ h⟩

private theorem stripLead {p : Comparison E F X Y} (hr : p.skipR = true)
    {u v : Head E B X} (h : Lead u v) {s : CTree F B Y} (r : Related p (.fold u) s) :
    Related p (.fold v) s := by
  induction h with
  | refl => exact r
  | more h ih => exact ih (by simpa only [fold_unfold] using invGuardL hr _ _ r)

private theorem stripRight {p : Comparison E F X Y} (hl : p.skipL = true)
    {u v : Head F B Y} (h : Lead u v) {t : CTree E B X} (r : Related p t (.fold u)) :
    Related p t (.fold v) :=
  flipRelated (swap p) _ _ (stripLead (p := swap p) hl h (flipRelated p _ _ r))

private theorem symEutt {t s : CTree E B X} (h : eutt Eq t s) : eutt Eq s t := by
  let p := Vellvm.Tree.eqitComparison E (@Eq X) true true
  have eq : swap p = p := by
    dsimp [p, swap, Vellvm.Tree.eqitComparison]
    congr 1
    · funext x y; exact propext eq_comm
    · funext e x f y; exact propext ⟨HEq.symm, HEq.symm⟩
    · funext x y; exact propext eq_comm
  have flipped := flipRelated p t s h
  rw [eq] at flipped
  exact flipped

private theorem pullFront {t s : CTree E B X} (h : eutt Eq t s) (hs : HasFront s) : HasFront t := by
  obtain ⟨v, lead, stable⟩ := hs
  have h' := related_iff.mp (stripRight rfl lead (by simpa only [fold_unfold] using h))
  rw [unfold_fold] at h'
  obtain ⟨v', lead', sync⟩ := viewStable h' stable
  refine ⟨v', lead', ?_⟩
  cases sync <;> first | exact (stable _ rfl).elim | intro _ eq; cases eq

private theorem noFront_guard {t : CTree E B X} (h : ¬ HasFront t) :
    ∃ s, t = s.guard ∧ ¬ HasFront s := by
  by_cases hg : ∃ s, t.unfold = .guard s
  · obtain ⟨s, hs⟩ := hg
    refine ⟨s, unfold_inj (hs.trans (unfold_guard s).symm), ?_⟩
    rintro ⟨v, lead, stable⟩
    exact h ⟨v, hs ▸ Lead.more lead, stable⟩
  · exact (h ⟨_, .refl _, fun s hs ↦ hg ⟨s, hs⟩⟩).elim

private theorem noFront_eq {t s : CTree E B X} (ht : ¬ HasFront t) (hs : ¬ HasFront s) : t = s := by
  ext n
  induction n generalizing t s with
  | zero => rfl
  | succ n ih =>
    obtain ⟨t', rfl, ht'⟩ := noFront_guard ht
    obtain ⟨s', rfl, hs'⟩ := noFront_guard hs
    simp only [guard_approx_1, ih ht' hs']

theorem ruttc_cong_eutt_l : ∀ {E F B : Effect.{u}} {X Y : Type u} {L : pred1 E} {K : pred1 F} {V : prerel E F} {A : postrel E F} {Q : X → Y → Prop} (t t' : CTree E B X) (s : CTree F B Y),
    ruttc L K V A Q t s → eutt Eq t t' → ruttc L K V A Q t' s := by
  intro E F B X Y L K V A Q
  coinduction C hc ih
  intro t u s h eq
  by_cases ht : HasFront t
  · obtain ⟨v, lead, stable⟩ := ht
    have mid := related_iff.mp (stripLead rfl lead (by simpa only [fold_unfold] using h))
    have lhs := related_iff.mp (stripRight rfl lead (by simpa only [fold_unfold] using symEutt eq))
    rw [unfold_fold] at mid lhs
    exact moveLeft (p := cmp L K V A Q) (C := C) (D := ruttc L K V A Q) (R := eutt Eq)
      rfl Stable (fun hg _ ↦ (hg _ rfl).elim)
      (fun hEq hR ↦ ih _ _ _ hR (symEutt hEq)) mid stable _ (viewStable lhs stable)
  · have hu : ¬ HasFront u := fun hf ↦ ht (pullFront eq hf)
    rw [← noFront_eq ht hu]
    exact gfp_le_chain (.step hc) _ _ h

theorem ruttc_eutt_l : ∀ {E F B : Effect.{u}} {X Y : Type u} {K : pred1 F} {L : pred1 E} {V : prerel E F} {A : postrel E F} {Q : X → Y → Prop} (t t' : CTree E B X) (s : CTree F B Y),
    eutt Eq t t' → ruttc L K V A Q t' s → ruttc L K V A Q t s := by
  intro E F B X Y K L V A Q t u s eq h
  exact ruttc_cong_eutt_l u t s h (symEutt eq)

theorem ruttc_eutt_r : ∀ {E F B : Effect.{u}} {X Y : Type u} {K : pred1 F} {L : pred1 E} {V : prerel E F} {A : postrel E F} {Q : X → Y → Prop} (t : CTree E B X) (s s' : CTree F B Y),
    eutt Eq s s' → ruttc L K V A Q t s → ruttc L K V A Q t s' := by
  intro E F B X Y K L V A Q t s v eq h
  exact (ruttc_flip t v).mpr (ruttc_cong_eutt_l s v t ((ruttc_flip t s).mp h) eq)

theorem ruttc_eutt : ∀ {E F B : Effect.{u}} {X Y : Type u} {L : pred1 E} {K : pred1 F} {V : prerel E F} {A : postrel E F} {Q : X → Y → Prop} (t t' : CTree E B X),
    eutt Eq t t' → ∀ (s s' : CTree F B Y), eutt Eq s s' → (ruttc L K V A Q t s ↔ ruttc L K V A Q t' s') := by
  intro E F B X Y L K V A Q t u tu s v sv
  exact ⟨fun h ↦ ruttc_eutt_r _ _ _ sv (ruttc_cong_eutt_l _ _ _ h tu),
    fun h ↦ ruttc_eutt_l _ _ _ tu (ruttc_eutt_r _ _ _ (symEutt sv) h)⟩

private theorem strongGE {t s : CTree E B X} (h : eqit Eq false false t s) : euttge Eq t s := by
  apply gfp_mono (b := layerMon B (Vellvm.Tree.eqitComparison E Eq false false))
    (c := layerMon B (Vellvm.Tree.eqitComparison E Eq true false)) _ t s h
  intro R t s h
  change Layer _ R t.unfold s.unfold at h ⊢
  generalize t.unfold = u at h ⊢
  generalize s.unfold = v at h ⊢
  induction h with
  | ret h => exact .ret h
  | guard h => exact .guard h
  | vis e h => exact .vis e h
  | skipL h _ _ => cases h
  | skipR h _ _ => cases h
  | cutL h => exact h.elim
  | cutR h => exact h.elim
  | stuck => exact .stuck
  | step h => exact .step h
  | br h => exact .br h

theorem ruttc_eq_itree : ∀ {E F B : Effect.{u}} {X Y : Type u} {L : pred1 E} {K : pred1 F} {V : prerel E F} {A : postrel E F} {Q : X → Y → Prop} (t t' : CTree E B X),
    eqit Eq false false t t' → ∀ (s s' : CTree F B Y), eqit Eq false false s s' → ruttc L K V A Q t' s' → ruttc L K V A Q t s := by
  intro E F B X Y L K V A Q t u tu s v sv
  exact euttge_proper_ruttc t u (strongGE tu) s v (strongGE sv)

theorem ruttc_map_monad_gen : ∀ {E F B : Effect.{u}} {X Y U W : Type u} (L : pred1 E) (K : pred1 F) (V : prerel E F) (A : postrel E F) (Q : X → Y → Prop)
    (f : U → CTree E B X) (g : W → CTree F B Y) (xs : List U) (ys : List W),
    List.Forall₂ (fun a b ↦ ruttc L K V A Q (f a) (g b)) xs ys →
    ruttc L K V A (List.Forall₂ Q) (Vellvm.Utils.ListUtil.map_monad f xs) (Vellvm.Utils.ListUtil.map_monad g ys) := by
  intro E F B X Y U W L K V A Q f g xs ys h
  induction h with
  | nil => exact ruttc_ret [] [] List.Forall₂.nil
  | cons h _ ih =>
    apply ruttc_bind L K V A Q (List.Forall₂ Q) _ _ _ _ h
    intro x y xy
    apply ruttc_bind L K V A (List.Forall₂ Q) (List.Forall₂ Q) _ _ _ _ ih
    exact fun xs ys eq ↦ ruttc_ret _ _ (.cons xy eq)

theorem ruttc_map_monad : ∀ {E F B : Effect.{u}} {X Y U : Type u} (L : pred1 E) (K : pred1 F) (V : prerel E F) (A : postrel E F) (Q : X → Y → Prop)
    (f : U → CTree E B X) (g : U → CTree F B Y) (xs : List U),
    (∀ a, a ∈ xs → ruttc L K V A Q (f a) (g a)) →
    ruttc L K V A (List.Forall₂ Q) (Vellvm.Utils.ListUtil.map_monad f xs) (Vellvm.Utils.ListUtil.map_monad g xs) := by
  intro E F B X Y U L K V A Q f g xs h
  apply ruttc_map_monad_gen L K V A Q
  induction xs with
  | nil => exact .nil
  | cons a xs ih => exact .cons (h a (.head _)) (ih fun b hb ↦ h b (.tail _ hb))

end Vellvm.Utils.rutt_cutoff
