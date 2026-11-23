module

public import Vellvm.Tree.Execution
public import CTree.Interp.Fold

@[expose] public section
namespace Vellvm.Tree.Producer

open ITree (Effect)
open CTree (CTree CTreeF)
open Coinductive Coinduction

universe u
variable {E F B : Effect.{u}} {X Y : Type u}

private theorem layer_map {S : Type u} (n : CTreeF E B X S) (l r : S → CTree E B X)
    {R : Rel (CTree E B X) (CTree E B X)} (h : ∀ s, R (l s) (r s)) :
    Layer (eqitComparison E Eq false false) R
      (PF.map (CTreeF E B X) l n) (PF.map (CTreeF E B X) r n) := by
  cases n with
  | ret _ => exact .ret rfl
  | stuck => exact .stuck
  | step s => exact .step (h s)
  | guard s => exact .guard (h s)
  | vis e k =>
    refine .vis rfl fun a b hab ↦ ?_
    cases eq_of_heq hab
    exact h (k a)
  | br _ k => exact .br fun a ↦ h (k a)

/-- Two presentations of a common transition system agree without skipping any heads.
The index can itself be a pair of related states from distinct producers. -/
theorem strict_bisim_of_presentations {S : Type u} (next : S → CTreeF E B X S)
    (l r : S → CTree E B X)
    (hl : ∀ s, (l s).unfold = PF.map _ l (next s))
    (hr : ∀ s, (r s).unfold = PF.map _ r (next s)) :
    ∀ s, eqit Eq false false (l s) (r s) := by
  coinduction R hR ih
  intro s
  change Layer _ R (l s).unfold (r s).unfold
  rw [hl, hr]
  exact layer_map _ _ _ ih

/-- Adequacy of a state-indexed interpretation that preserves each transition exactly. -/
theorem meaningAt_strict (p : Producer E B X) (spec : p.S → CTree E B X)
    (h : ∀ s, (spec s).unfold = PF.map _ spec (p.next s)) :
    ∀ s, eqit Eq false false (p.meaningAt s) (spec s) :=
  strict_bisim_of_presentations p.next _ _ p.observe_meaningAt h

theorem meaning_ret (x : X) : eqit Eq false false (ret (E := E) (B := B) x).meaning (.ret x) :=
  meaningAt_strict (ret x) (fun _ ↦ .ret x) (fun _ ↦ CTree.unfold_ret x) _

theorem meaning_trigger (e : E.I) :
    eqit Eq false false (trigger (B := B) e).meaning (.trigger e) := by
  let spec : Option (E.O e) → CTree E B (E.O e)
    | none => .trigger e
    | some a => .ret a
  apply meaningAt_strict (trigger e) spec _ none
  rintro (_ | a)
  · exact CTree.unfold_vis e _
  · exact CTree.unfold_ret a

theorem meaning_branch (b : B.I) :
    eqit Eq false false (branch (E := E) b).meaning (.branch b) := by
  let spec : Option (B.O b) → CTree E B (B.O b)
    | none => .branch b
    | some a => .ret a
  apply meaningAt_strict (branch b) spec _ none
  rintro (_ | a)
  · exact CTree.unfold_br b _
  · exact CTree.unfold_ret a

theorem meaningAt_translate (h : (e : E.I) → (f : F.I) × (F.O f → E.O e))
    (p : Producer E B X) : ∀ s,
    eqit Eq false false ((translate h p).meaningAt s) (CTree.translate h (p.meaningAt s)) := by
  apply meaningAt_strict
  intro s
  rw [CTree.unfold_translate, observe_meaningAt p s]
  dsimp only [translate]
  cases hn : p.next s with
  | ret _ => exact CTree.unfold_pure _
  | stuck => exact CTree.unfold_stuck
  | step _ => exact CTree.unfold_step _
  | guard _ => exact CTree.unfold_guard _
  | vis e k => cases hh : h e with | mk f g => exact CTree.unfold_vis _ _
  | br _ _ => exact CTree.unfold_br _ _

theorem meaning_translate (h : (e : E.I) → (f : F.I) × (F.O f → E.O e))
    (p : Producer E B X) :
    eqit Eq false false (translate h p).meaning (CTree.translate h p.meaning) :=
  meaningAt_translate h p p.initial

private def bindSpec (p : Producer E B X) (k : X → Producer E B Y) :
    (bind p k).S → CTree E B Y
  | .inl s => p.meaningAt s >>= fun x ↦ (k x).meaning
  | .inr ⟨x, s⟩ => (k x).meaningAt s

private theorem bindSpec_resume (p : Producer E B X) (k : X → Producer E B Y)
    (x : X) (s : (k x).S) :
    ((k x).meaningAt s).unfold = PF.map _ (bindSpec p k)
      (PF.map _ (fun j ↦ Sum.inr (Sigma.mk x j)) ((k x).next s)) := by
  rw [observe_meaningAt]
  cases (k x).next s <;> rfl

theorem meaning_bind (p : Producer E B X) (k : X → Producer E B Y) :
    eqit Eq false false (bind p k).meaning (p.meaning >>= fun x ↦ (k x).meaning) := by
  apply meaningAt_strict (bind p k) (bindSpec p k) _ (.inl p.initial)
  rintro (s | ⟨x, s⟩)
  · change (p.meaningAt s >>= _).unfold = _
    rw [CTree.unfold_bind, observe_meaningAt]
    dsimp only [bind]
    cases p.next s with
    | ret x => exact bindSpec_resume p k x (k x).initial
    | _ => rfl
  · exact bindSpec_resume p k x s

private def iterCont (body : X → Producer E B (X ⊕ Y)) : X ⊕ Y → CTree E B Y
  | .inl x => .guard (.iter (fun x ↦ (body x).meaning) x)
  | .inr y => .ret y

private theorem iter_eq_bind (body : X → Producer E B (X ⊕ Y)) (x : X) :
    CTree.iter (fun x ↦ (body x).meaning) x = (body x).meaning >>= iterCont body := by
  rw [CTree.unfold_iter]
  congr 1
  funext r
  cases r <;> rfl

theorem meaning_iter (body : X → Producer E B (X ⊕ Y)) (initial : X) :
    eqit Eq false false (iter body initial).meaning (CTree.iter (fun x ↦ (body x).meaning) initial) := by
  rw [iter_eq_bind]
  let spec : (iter body initial).S → CTree E B Y := fun ⟨x, s⟩ ↦
    (body x).meaningAt s >>= iterCont body
  apply meaningAt_strict (iter body initial) spec _ ⟨initial, (body initial).initial⟩
  rintro ⟨x, s⟩
  change ((body x).meaningAt s >>= _).unfold = _
  rw [CTree.unfold_bind, observe_meaningAt]
  dsimp only [iter]
  cases (body x).next s with
  | ret r =>
    cases r with
    | inl x' => exact (CTree.unfold_guard _).trans (congrArg CTreeF.guard (iter_eq_bind body x'))
    | inr y => exact CTree.unfold_ret y
  | _ => rfl

end Vellvm.Tree.Producer
