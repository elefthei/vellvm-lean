module

@[expose] public section
namespace Vellvm.Utils.Tactics

inductive Box (T : Type u) where | box (t : T)
inductive hidden_cont (T : Type u) where | boxh_cont (t : T)
inductive visible_cont (T : Type u) where | boxv_cont (t : T)
export Box (box)
export hidden_cont (boxh_cont)
export visible_cont (boxv_cont)

theorem inj_pair2 (U : Type u) (P : U → Type v) (p : U) (x y : P p)
    (h : (⟨p, x⟩ : Sigma P) = ⟨p, y⟩) : x = y := by cases h; rfl

end Vellvm.Utils.Tactics
