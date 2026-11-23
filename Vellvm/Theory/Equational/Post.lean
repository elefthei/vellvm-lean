module

public import Vellvm.Semantics.LLVMEvents
public import Vellvm.Utils.rutt_cutoff

@[expose] public section
namespace Vellvm.Theory.Equational

open CTree Coinduction
open ITree (Effect Subeffect)
open Vellvm.Tree Utils.CTreeUtil Utils.rutt_cutoff
open Semantics Semantics.Interfaces.Params Semantics.LLVMEvents

universe u
variable {E B : Effect.{u}} {X Y : Type u}

/-- Unary postconditions are the diagonal of weak bisimulation. -/
def has_post (t : CTree E B X) (P : X → Prop) : Prop := Tree.eutt (fun x _ ↦ P x) t t

private theorem eutt_mono_result {R S : X → Y → Prop} {t : CTree E B X} {s : CTree E B Y}
    (ht : Tree.eutt R t s) (f : ∀ x y, R x y → S x y) : Tree.eutt S t s :=
  ruttc_weaken _ _ _ _ _ _ _ _ R S (fun _ ↦ id) (fun _ ↦ id) (fun _ _ ↦ id)
    (fun _ _ _ _ ↦ id) f t s ht

theorem has_post_weaken {t : CTree E B X} {P Q : X → Prop} (h : has_post t P)
    (f : ∀ x, P x → Q x) : has_post t Q := eutt_mono_result h (fun x _ ↦ f x)

/-- On the diagonal, matching the same response at each node preserves the returned value. -/
theorem strengthen {t : CTree E B X} {P : X → Prop} (ht : has_post t P) :
    Tree.eutt (fun x y ↦ x = y ∧ P x) t t := by
  revert t
  coinduction C hc ih
  intro t hp
  suffices ∀ h : Head E B X, has_post (.fold h) P →
      Layer (eqitComparison E (fun x y ↦ x = y ∧ P x) true true) C h h by
    exact this t.unfold (by simpa only [fold_unfold] using hp)
  intro h hp
  have hh := related_iff.mp hp
  simp only [unfold_fold] at hh
  cases h with
  | ret x => cases hh with | ret hx => exact .ret ⟨rfl, hx⟩
  | stuck => exact .stuck
  | guard t =>
    rw [fold_guard] at hp
    exact .guard (ih (ruttc_inv_Tau _ _ _ _ _ _ hp))
  | step t => cases hh with | step h => exact .step (ih h)
  | br c k => cases hh with | br hk => exact .br fun a ↦ ih (hk a)
  | vis e k =>
    rw [fold_vis] at hp
    refine .vis rfl fun a b hab ↦ ?_
    cases eq_of_heq hab
    exact ih ((eutt_vis_same_iff _ _ _ _).mp hp a)

theorem has_post_bind_weak {t : CTree E B X} {k : X → CTree E B Y} {Q : Y → Prop}
    (hk : ∀ x, has_post (k x) Q) : has_post (t >>= k) Q :=
  ruttc_bind _ _ _ _ Eq _ t t k k (eqit_refl true true t) fun x _ h ↦ h ▸ hk x

theorem has_post_bind {t : CTree E B X} {k : X → CTree E B Y} {P : X → Prop} {Q : Y → Prop}
    (ht : has_post t P) (hk : ∀ x, P x → has_post (k x) Q) : has_post (t >>= k) Q :=
  ruttc_bind _ _ _ _ _ _ t t k k (strengthen ht) fun x _ ⟨rfl, hx⟩ ↦ hk x hx

theorem post_bind_eq {t : CTree E B X} {k l : X → CTree E B Y} {P : X → Prop}
    (ht : has_post t P) (hk : ∀ x, P x → Tree.eutt Eq (k x) (l x)) :
    Tree.eutt Eq (t >>= k) (t >>= l) :=
  ruttc_bind _ _ _ _ _ Eq t t k l (strengthen ht) fun x _ ⟨rfl, hx⟩ ↦ hk x hx

theorem has_post_iter {body : X → CTree E B (X ⊕ Y)} {i : X} {P : X → Prop} {Q : Y → Prop}
    (hi : P i) (hb : ∀ i, P i → has_post (body i) (Sum.elim P Q)) :
    has_post (CTree.iter body i) Q := by
  refine ruttc_iter _ _ _ _ _ (fun i j ↦ i = j ∧ P i) body body ?_ i i ⟨rfl, hi⟩
  rintro j _ ⟨rfl, hj⟩
  apply eutt_mono_result (strengthen (hb j hj))
  rintro (j | y) _ ⟨rfl, h⟩
  · exact .inl ⟨rfl, h⟩
  · exact .inr h

theorem has_post_trigger_cast {E B : Effect.{u}} (e : E.I) (he : E.O e = PEmpty) {A : Type u}
    (P : A → Prop) : has_post (trigger_cast' (B := B) e he) P :=
  has_post_bind_weak fun a ↦ PEmpty.elim (he ▸ a)

theorem has_post_ret {E B : Effect.{u}} {R : Type u} (r : R) (P : R → Prop) (hr : P r) :
    has_post (CTree.ret r : CTree E B R) P := ruttc_ret r r hr

theorem raise_has_all_posts {E B : Effect} {X : Type} [FailureE -< E] (s : IRString) (Q : X → Prop) :
    has_post (LLVMEvents.«raise» (E := E) (B := B) s) Q := by
  unfold LLVMEvents.«raise» Worker.«raise»
  apply has_post_bind_weak
  intro _
  exact has_post_bind_weak fun (a : Empty) ↦ nomatch a

theorem raiseUB_has_all_posts {E B : Effect} {X : Type} [UBE -< E] (s : IRString) (Q : X → Prop) :
    has_post (raiseUB (E := E) (B := B) s) Q := by
  unfold raiseUB Worker.raiseUB
  apply has_post_bind_weak
  intro _
  exact has_post_bind_weak fun (a : Empty) ↦ nomatch a

theorem raiseOOM_has_all_posts {E B : Effect} {X : Type} [OOME -< E] (s : IRString) (Q : X → Prop) :
    has_post (raiseOOM (E := E) (B := B) s) Q := by
  unfold raiseOOM Worker.raiseOOM
  apply has_post_bind_weak
  intro _
  exact has_post_bind_weak fun (a : Empty) ↦ nomatch a

theorem raiseLLVM_has_all_posts [Pa : Params] {E B : Effect} {X : Type} [LLVMExcE -< E]
    (ex : exc) (Q : X → Prop) : has_post (raiseLLVM (E := E) (B := B) ex) Q := by
  unfold raiseLLVM Worker.raiseLLVM
  exact has_post_bind_weak fun (a : Empty) ↦ nomatch a

end Vellvm.Theory.Equational
