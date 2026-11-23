module

public import Vellvm.Tree.Runtime
public import Vellvm.Tree.StrictEq

@[expose] public section
namespace Vellvm.Tree
open ITree (Effect)
open CTree (CTree CTreeF)
open Coinductive (PF)

universe u v

/-- Catch only selected visible heads, without answering the interrupted event. -/
class Catch (M : Effect.{u} → Effect.{u} → Type u → Type v) where
  run {E B : Effect.{u}} {X A : Type u} (select : E.I → Option X) (t : M E B A) : M E B (X ⊕ A)

namespace Catch
variable {E B : Effect.{u}} {X A : Type u}

def body (select : E.I → Option X) (t : CTree E B A) :
    CTree E B (CTree E B A ⊕ (X ⊕ A)) := match t.unfold with
  | .ret a => .ret (.inr (.inr a))
  | .guard t => .ret (.inl t)
  | .vis e k => match select e with
    | some x => .ret (.inr (.inl x))
    | none => .vis e fun a ↦ .ret (.inl (k a))
  | .stuck => .stuck
  | .step t => .step (.ret (.inl t))
  | .br c k => .br c fun a ↦ .ret (.inl (k a))

def ctreeRun (select : E.I → Option X) (t : CTree E B A) : CTree E B (X ⊕ A) :=
  .iter (body select) t

theorem unfold_ctreeRun (select : E.I → Option X) (t : CTree E B A) :
    (ctreeRun select t).unfold = match t.unfold with
      | .ret a => .ret (.inr a)
      | .guard t => .guard (ctreeRun select t)
      | .vis e k => match select e with
        | some x => .ret (.inl x)
        | none => .vis e fun a ↦ .guard (ctreeRun select (k a))
      | .stuck => .stuck
      | .step t => .step (.guard (ctreeRun select t))
      | .br c k => .br c fun a ↦ .guard (ctreeRun select (k a)) := by
  unfold ctreeRun
  rw (occs := .pos [1]) [CTree.unfold_iter]
  cases h : t.unfold with
  | vis e k => cases he : select e <;> simp [body, h, he]
  | _ => simp [body, h]

/-- Forwarded requests (and native branching/steps) resume the loop underneath an iteration guard. -/
def producerRun (select : E.I → Option X) (p : Producer E B A) : Producer E B (X ⊕ A) where
  S := Bool × p.S
  initial := (false, p.initial)
  next
    | (true, s) => .guard (false, s)
    | (false, s) => match p.next s with
      | .ret a => .ret (.inr a)
      | .guard s' => .guard (false, s')
      | .vis e k => match select e with
        | some x => .ret (.inl x)
        | none => .vis e fun a ↦ (true, k a)
      | .stuck => .stuck
      | .step s' => .step (true, s')
      | .br c k => .br c fun a ↦ (true, k a)

@[simp] theorem meaning_producerRun (select : E.I → Option X) (p : Producer E B A) :
    (producerRun select p).meaning = ctreeRun select p.meaning := by
  let spec : Bool × p.S → CTree E B (X ⊕ A)
    | (true, s) => .guard (ctreeRun select (p.meaningAt s))
    | (false, s) => ctreeRun select (p.meaningAt s)
  apply eqit_strict_iff_eq.mp (Producer.meaningAt_strict (producerRun select p) spec _ (false, p.initial))
  rintro ⟨flag, s⟩
  cases flag with
  | true => exact CTree.unfold_guard _
  | false =>
    change (ctreeRun select (p.meaningAt s)).unfold = _
    rw [unfold_ctreeRun, Producer.observe_meaningAt]
    dsimp only [producerRun]
    cases hp : p.next s with
    | vis e k =>
      change (match select e with
        | some x => CTreeF.ret (Sum.inl x : X ⊕ A)
        | none => CTreeF.vis e (fun x ↦ (ctreeRun select (p.meaningAt (k x))).guard)) =
        PF.map (CTreeF E B (X ⊕ A)) spec (match select e with
          | some x => .ret (.inl x)
          | none => .vis e fun x ↦ (true, k x))
      cases select e <;> rfl
    | _ => rfl

open Coinduction in
theorem ctreeRun_congr (select : E.I → Option X) (left right : Bool) :
    ∀ (t s : CTree E B A), eqit Eq left right t s →
      eqit Eq left right (ctreeRun select t) (ctreeRun select s) := by
  coinduction C hc ih
  intro t s h
  have guarded {a b : CTree E B A} (hab : eqit Eq left right a b) :
      C (ctreeRun select a).guard (ctreeRun select b).guard := by
    apply b_chain hc
    change Layer _ C _ _
    rw [CTree.unfold_guard, CTree.unfold_guard]
    exact .guard (ih a b hab)
  suffices ∀ l r, Layer (eqitComparison E Eq left right) (eqit Eq left right) l r →
      Layer (eqitComparison E Eq left right) C (ctreeRun select (CTree.fold l)).unfold
        (ctreeRun select (CTree.fold r)).unfold by
    simpa only [layerMon, CTree.fold_unfold] using this _ _ (related_iff.mp h)
  intro l r hl
  induction hl with
  | ret he => cases he; simp only [unfold_ctreeRun, CTree.unfold_fold]; exact .ret rfl
  | stuck => simp only [unfold_ctreeRun, CTree.unfold_fold]; exact .stuck
  | guard h => simp only [unfold_ctreeRun, CTree.unfold_fold]; exact .guard (ih _ _ h)
  | step h => simp only [unfold_ctreeRun, CTree.unfold_fold]; exact .step (guarded h)
  | br hk => simp only [unfold_ctreeRun, CTree.unfold_fold]; exact .br fun a ↦ guarded (hk a)
  | @vis e f k j he hk =>
    cases he
    simp only [unfold_ctreeRun, CTree.unfold_fold]
    cases he : select e with
    | some => exact .ret rfl
    | none => exact .vis rfl fun a b h ↦ guarded (hk a b h)
  | skipL flag _ hi =>
    rw [unfold_ctreeRun, CTree.unfold_fold]
    exact .skipL flag (by simpa only [CTree.fold_unfold] using hi)
  | skipR flag _ hi =>
    rw (occs := .pos [2]) [unfold_ctreeRun]
    rw [CTree.unfold_fold]
    exact .skipR flag (by simpa only [CTree.fold_unfold] using hi)
  | cutL hf | cutR hf => exact hf.elim

instance : Catch CTree := ⟨ctreeRun⟩
instance : Catch Producer := ⟨producerRun⟩

end Catch
end Vellvm.Tree
