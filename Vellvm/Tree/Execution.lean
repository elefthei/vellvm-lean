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

def bind (p : Producer E B X) (k : X → Producer E B Y) : Producer E B Y where
  S := Sum p.S (Σ x, (k x).S)
  initial := .inl p.initial
  next := fun s ↦
    let resume := fun (x : X) (s' : (k x).S) ↦ PF.map (CTreeF E B Y)
      (fun j ↦ Sum.inr (Sigma.mk x j)) ((k x).next s')
    match s with
    | .inl i => match p.next i with
      | .ret x => resume x (k x).initial
      | .stuck => .stuck
      | .guard j => .guard (.inl j)
      | .step j => .step (.inl j)
      | .vis e l => .vis e fun x ↦ .inl (l x)
      | .br b l => .br b fun x ↦ .inl (l x)
    | .inr ⟨x, j⟩ => resume x j

def iter (body : X → Producer E B (Sum X Y)) (x : X) : Producer E B Y where
  S := Σ x, (body x).S
  initial := ⟨x, (body x).initial⟩
  next := fun ⟨x, s⟩ ↦ match (body x).next s with
    | .ret (.inl x') => .guard ⟨x', (body x').initial⟩
    | .ret (.inr y) => .ret y
    | .stuck => .stuck
    | .guard j => .guard ⟨x, j⟩
    | .step j => .step ⟨x, j⟩
    | .vis e k => .vis e fun y ↦ ⟨x, k y⟩
    | .br b k => .br b fun y ↦ ⟨x, k y⟩

end Producer
end Vellvm.Tree
