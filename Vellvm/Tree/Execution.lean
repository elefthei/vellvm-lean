module

public import Vellvm.Tree.Relations

@[expose] public section
namespace Vellvm.Tree
open ITree (Effect)
open CTree (CTree CTreeF)
open Coinductive

universe u

structure Producer (E B : Effect.{u}) (X : Type u) where
  S : Type u
  initial : S
  next : S → CTreeF E B X S

namespace Producer
variable {E F B : Effect.{u}} {X Y : Type u}

def meaningAt (p : Producer E B X) (s : p.S) : CTree E B X := cofix _ p.next s
def meaning (p : Producer E B X) := p.meaningAt p.initial

theorem observe_meaningAt (p : Producer E B X) (s : p.S) :
    (p.meaningAt s).unfold = PF.map (CTreeF E B X) p.meaningAt (p.next s) := by
  unfold meaningAt
  rw [cofix_eq, CTree.CTree.unfold, unfold_fold]

/-- A bounded observation retains every event and branch continuation; no answer is guessed. -/
def observePrefix (p : Producer E B X) (s : p.S) : (n : Nat) → CoIndN (CTreeF E B X) n
  | 0 => PUnit.unit
  | n + 1 => PF.map (CTreeF E B X) (fun s' ↦ p.observePrefix s' n) (p.next s)

theorem prefix_eq_approx (p : Producer E B X) (s : p.S) (n : Nat) :
    p.observePrefix s n = (p.meaningAt s).approx n := by
  induction n generalizing s with
  | zero => rfl
  | succ n ih =>
    change PF.map _ _ _ = PF.map _ (fun s' ↦ (p.meaningAt s').approx n) (p.next s)
    simp only [ih]

def ret (x : X) : Producer E B X := ⟨PUnit, ⟨⟩, fun _ ↦ .ret x⟩

def trigger (e : E.I) : Producer E B (E.O e) :=
  ⟨Option (E.O e), none, fun | none => .vis e some | some x => .ret x⟩

def branch (b : B.I) : Producer E B (B.O b) :=
  ⟨Option (B.O b), none, fun | none => .br b some | some x => .ret x⟩

def translate (h : (e : E.I) → (f : F.I) × (F.O f → E.O e)) (p : Producer E B X) :
    Producer F B X := ⟨p.S, p.initial, fun s ↦ match p.next s with
  | .ret x => .ret x
  | .stuck => .stuck
  | .guard s' => .guard s'
  | .step s' => .step s'
  | .vis e k => let ⟨f, back⟩ := h e; .vis f fun x ↦ k (back x)
  | .br b k => .br b k⟩

/-- Only the transition survives erasure; its identity is for the meaning proofs. -/
abbrev CachedNext (p : Producer E B X) := {f : p.S → CTreeF E B X p.S // f = p.next}

/-- A continuation or loop body that has been entered once and is still running. -/
structure Active (k : X → Producer E B Y) where
  arg : X
  next : CachedNext (k arg)
  state : (k arg).S

@[inline] def Active.start (k : X → Producer E B Y) (x : X) : Active k :=
  let p := k x
  ⟨x, ⟨p.next, rfl⟩, p.initial⟩

@[inline] def Active.bindHead {k : X → Producer E B Y} {A : Type u} :
    Active k → CTreeF E B Y (Sum A (Active k))
  | ⟨x, n, s⟩ => match n.val s with
    | .ret y => .ret y
    | .stuck => .stuck
    | .guard j => .guard (.inr ⟨x, n, j⟩)
    | .step j => .step (.inr ⟨x, n, j⟩)
    | .vis e l => .vis e fun a ↦ .inr ⟨x, n, l a⟩
    | .br b l => .br b fun a ↦ .inr ⟨x, n, l a⟩

def bind (p : Producer E B X) (k : X → Producer E B Y) : Producer E B Y where
  S := Sum p.S (Active k)
  initial := .inl p.initial
  next
    | .inl i => match p.next i with
      | .ret x => (Active.start k x).bindHead
      | .stuck => .stuck
      | .guard j => .guard (.inl j)
      | .step j => .step (.inl j)
      | .vis e l => .vis e fun x ↦ .inl (l x)
      | .br b l => .br b fun x ↦ .inl (l x)
    | .inr c => c.bindHead

def iter (body : X → Producer E B (Sum X Y)) (x : X) : Producer E B Y where
  S := Active body
  initial := Active.start body x
  next := fun ⟨x, n, s⟩ ↦ match n.val s with
    | .ret (.inl x') => .guard (Active.start body x')
    | .ret (.inr y) => .ret y
    | .stuck => .stuck
    | .guard j => .guard ⟨x, n, j⟩
    | .step j => .step ⟨x, n, j⟩
    | .vis e k => .vis e fun y ↦ ⟨x, n, k y⟩
    | .br b k => .br b fun y ↦ ⟨x, n, k y⟩

end Producer
end Vellvm.Tree
