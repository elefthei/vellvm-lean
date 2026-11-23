module

@[expose] public section
namespace Vellvm.Utils.Assoc

variable {A : Type u} {B : Type v} [BEq A]

theorem eq_dec_eq [LawfulBEq A] (a : A) : (a == a) = true := by simp

theorem eq_dec_neq [LawfulBEq A] (a b : A) (h : a ≠ b) : (a == b) = false := by simp [h]

def assoc (a : A) : List (A × B) → Option B
  | [] => none
  | (c, b) :: tl => if a == c then some b else assoc a tl

theorem assoc_hd [LawfulBEq A] (a : A) (b : B) (tl : List (A × B)) :
    assoc a ((a, b) :: tl) = some b := by simp [assoc]

theorem assoc_tl [LawfulBEq A] (a c : A) (b : B) (l : List (A × B)) (h : a ≠ c) :
    assoc a ((c, b) :: l) = assoc a l := by simp [assoc, h]

end Vellvm.Utils.Assoc
