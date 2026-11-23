module

public import Vellvm.Utils.IntMaps.Foundations

@[expose] public section
namespace Vellvm.Utils.IntMaps

open Vellvm.Numeric.Rocqlib (list_nth_z)

universe u

theorem add_all_index_add_comm {A : Type u} (l : List A) (i j : Int) (v : A) (m : IntMap A)
    (out : j < i ∨ j ≥ i + (l.length : Int)) :
    Equal (add_all_index l i (add j v m)) (add j v (add_all_index l i m)) := by
  induction l generalizing i with
  | nil => intro q; rfl
  | cons x xs ih =>
    simp only [List.length_cons] at out
    intro q
    by_cases h : q = i
    · subst q
      simp [add_all_index, lookup_insert, show i ≠ j by omega]
    · simpa [add_all_index, lookup_insert, h] using ih (i + 1) (by omega) q

theorem add_all_index_acc_eq {A : Type u} (vs : List A) (i : Int) (m : IntMap A) :
    Equal (add_all_index_acc vs i m) (add_all_index vs i m) := by
  induction vs generalizing i m with
  | nil => intro q; rfl
  | cons x xs ih =>
    intro q
    exact (ih (i + 1) (add i x m) q).trans
      (add_all_index_add_comm xs (i + 1) i x m (.inl (by omega)) q)

theorem lookup_all_index_cons {A : Type u} (k : Int) (n : Nat) (m : IntMap A) (d : A) :
    lookup_all_index k n.succ m d =
      (match lookup k m with | some v => v | none => d) :: lookup_all_index (k + 1) n m d := by
  rw [lookup_all_index, ListUtil.Zseq_succ, List.map_cons]
  cases lookup k m <;> rfl

theorem lookup_all_index_add_out_aux {A : Type u} (l : List Int) (k : Int) (n : Nat) (m : IntMap A)
    (key : Int) (x d : A) (seq : l = ListUtil.Zseq k n) (out : key < k ∨ key ≥ k + (n : Int)) :
    lookup_all_index k n (add key x m) d = lookup_all_index k n m d := by
  cases seq
  induction n generalizing k with
  | zero => rfl
  | succ n ih =>
    rw [lookup_all_index_cons, lookup_all_index_cons, lookup_insert,
      ite_eq_right (show k ≠ key by omega), ih (k + 1) (by omega)]

theorem lookup_all_index_add_out {A : Type u} (k : Int) (n : Nat) (m : IntMap A) (key : Int)
    (x d : A) (out : key < k ∨ key ≥ k + (n : Int)) :
    lookup_all_index k n (add key x m) d = lookup_all_index k n m d :=
  lookup_all_index_add_out_aux _ k n m key x d rfl out

theorem lookup_all_index_add {A : Type u} (k : Int) (size : Nat) (x : A) (m : IntMap A) (d : A) :
    lookup_all_index k size.succ (add k x m) d = x :: lookup_all_index (k + 1) size m d := by
  rw [lookup_all_index_cons, lookup_insert, ite_eq_left rfl,
    lookup_all_index_add_out _ _ _ _ _ _ (.inl (by omega))]

theorem pred_succ_of_nat (n : Nat) : (⟨n.succ, Nat.zero_lt_succ n⟩ : Positive).val.pred = n := rfl

theorem lookup_all_index_length {A : Type u} (len : Nat) (off : Int) (bytes : IntMap A) (d : A) :
    (lookup_all_index off len bytes d).length = len := by
  rw [lookup_all_index, List.length_map, ListUtil.Zseq_length]

theorem lookup_add_all_index_in {A : Type u} (l : List A) (k z : Int) (m : IntMap A) (v : A)
    (range : z ≤ k ∧ k ≤ z + (l.length : Int) - 1) (nth : list_nth_z l (k - z) = some v) :
    lookup k (add_all_index l z m) = some v := by
  induction l generalizing z with
  | nil => simp at range; omega
  | cons x xs ih =>
    simp only [List.length_cons] at range
    rw [add_all_index, lookup_insert]
    by_cases h : k = z
    · subst z
      simpa [list_nth_z] using nth
    · rw [ite_eq_right h]
      apply ih (z + 1) (by omega)
      let n := (k - (z + 1)).toNat
      have tail : k - (z + 1) = Int.ofNat n := by dsimp [n]; omega
      have head : k - z = Int.ofNat n.succ := by change k - z = Int.ofNat n + 1; omega
      rw [head] at nth
      rw [tail]
      simpa [list_nth_z] using nth

theorem lookup_add_all_index_out {A : Type u} (l : List A) (k z : Int) (m : IntMap A)
    (out : k < z ∨ k ≥ z + (l.length : Int)) : lookup k (add_all_index l z m) = lookup k m := by
  induction l generalizing z with
  | nil => rfl
  | cons x xs ih =>
    simp only [List.length_cons] at out
    rw [add_all_index, lookup_insert, ite_eq_right (show k ≠ z by omega), ih (z + 1) (by omega)]

def key_in_range_or_not_aux {A : Type u} (k z : Int) (l : List A) :
    PSum (PSum (z ≤ k ∧ k ≤ z + (l.length : Int) - 1) (k < z)) (k ≥ z + (l.length : Int)) :=
  if lo : k < z then .inl (.inr lo)
  else if hi : k ≥ z + (l.length : Int) then .inr hi
  else .inl (.inl (by omega))

def key_in_range_or_not {A : Type u} (k z : Int) (l : List A) :
    PSum (z ≤ k ∧ k ≤ z + (l.length : Int) - 1) (k < z ∨ k ≥ z + (l.length : Int)) :=
  match key_in_range_or_not_aux k z l with
  | .inl (.inl inside) => .inl inside
  | .inl (.inr before) => .inr (.inl before)
  | .inr after => .inr (.inr after)

theorem range_list_nth_z {A : Type u} (l : List A) (k : Int) (range : 0 ≤ k ∧ k < (l.length : Int)) :
    ∃ v, list_nth_z l k = some v := by
  cases k with
  | negSucc => omega
  | ofNat n =>
    have lt : n < l.length := Int.ofNat_lt.mp range.2
    exact ⟨l[n], List.getElem?_eq_getElem lt⟩

theorem in_range_is_in {A : Type u} (k z : Int) (l : List A)
    (range : z ≤ k ∧ k ≤ z + (l.length : Int) - 1) : ∃ v, list_nth_z l (k - z) = some v :=
  range_list_nth_z l (k - z) (by omega)

theorem add_all_index_twice {A : Type u} (l₁ l₂ : List A) (z : Int) (m : IntMap A)
    (lengths : (l₁.length : Int) = (l₂.length : Int)) :
    Equal (add_all_index l₂ z (add_all_index l₁ z m)) (add_all_index l₂ z m) := by
  intro k
  cases key_in_range_or_not k z l₂ with
  | inl inside =>
    obtain ⟨v, nth⟩ := in_range_is_in k z l₂ inside
    rw [lookup_add_all_index_in _ _ _ _ v inside nth, lookup_add_all_index_in _ _ _ _ v inside nth]
  | inr outside =>
    rw [lookup_add_all_index_out _ _ _ _ outside, lookup_add_all_index_out l₁ _ _ _ (lengths ▸ outside),
      lookup_add_all_index_out _ _ _ _ outside]

end Vellvm.Utils.IntMaps
