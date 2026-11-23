module

public import Mathlib.Logic.Relation

@[expose] public section
namespace Vellvm.Utils.RelationsUtil

open Relation

/-- Heterogeneous product relation, with one premise for each projection. -/
abbrev prod_rel {A B C D : Type*} (r : A → C → Prop) (s : B → D → Prop)
    (x : A × B) (y : C × D) : Prop := r x.1 y.1 ∧ s x.2 y.2

scoped infixl:35 " × " => prod_rel

def TT {A : Type*} : A → A → Prop := fun _ _ ↦ True

variable {A : Type*} {R : A → A → Prop} {x y : A}

theorem clos_t_rt : TransGen R x y → ReflTransGen R x y := TransGen.to_reflTransGen

theorem clos_t_rt_inv (h : TransGen R x y) : ∃ z, R z y ∧ ReflTransGen R x z := by
  obtain ⟨z, hx, hy⟩ := TransGen.tail'_iff.mp h
  exact ⟨z, hy, hx⟩

theorem clos_rt_t_inv (h : ReflTransGen R x y) : x = y ∨ R x y ∨ TransGen R x y :=
  (reflTransGen_iff_eq_or_transGen.mp h).elim (fun e ↦ .inl e.symm) (fun t ↦ .inr (.inr t))

theorem clos_rt_inv (h : ReflTransGen R x y) : x = y ∨ ∃ z, R z y ∧ ReflTransGen R x z := by
  cases h with
  | refl => exact .inl rfl
  | tail hx hy => exact .inr ⟨_, hy, hx⟩

theorem clos_trans_measure (m : A → Nat) (hm : ∀ a b, R a b → m a < m b)
    (a b : A) (h : TransGen R a b) : m a < m b := by
  induction h with
  | single h => exact hm _ _ h
  | tail _ h ih => exact Nat.lt_trans ih (hm _ _ h)

theorem clos_trans_not_sym (m : A → Nat) (hm : ∀ a b, R a b → m a < m b)
    (a b : A) (h : TransGen R a b) : ¬ TransGen R b a := fun h' ↦
  Nat.lt_asymm (clos_trans_measure m hm a b h) (clos_trans_measure m hm b a h')

theorem clos_refl_trans_antisymmetric (m : A → Nat) (hm : ∀ a b, R a b → m a < m b)
    (a b : A) (hab : ReflTransGen R a b) (hba : ReflTransGen R b a) : a = b := by
  obtain h | ab := reflTransGen_iff_eq_or_transGen.mp hab
  · exact h.symm
  obtain h | ba := reflTransGen_iff_eq_or_transGen.mp hba
  · exact h
  exact False.elim (clos_trans_not_sym m hm a b ab ba)

end Vellvm.Utils.RelationsUtil
