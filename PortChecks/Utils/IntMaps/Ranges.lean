import PortChecks.SourceType
import Vellvm.Utils.IntMaps.Ranges

open Vellvm Vellvm.Utils Vellvm.Utils.IntMaps Vellvm.Numeric.Rocqlib
universe u

#source_check "src/rocq/Utils/IntMaps.v|Vellvm.Utils.IntMaps|add_all_index_add_comm"
  add_all_index_add_comm : ∀ {A : Type u} (l : List A) (i j : Int) (v : A) (m : IntMap A),
    j < i ∨ j ≥ i + (l.length : Int) →
    Equal (add_all_index l i (add j v m)) (add j v (add_all_index l i m))

#source_check "src/rocq/Utils/IntMaps.v|Vellvm.Utils.IntMaps|add_all_index_acc_eq"
  add_all_index_acc_eq : ∀ {A : Type u} (vs : List A) (i : Int) (m : IntMap A),
    Equal (add_all_index_acc vs i m) (add_all_index vs i m)

#source_check "src/rocq/Utils/IntMaps.v|Vellvm.Utils.IntMaps|lookup_all_index_cons"
  lookup_all_index_cons : ∀ {A : Type u} (k : Int) (n : Nat) (m : IntMap A) (d : A),
    lookup_all_index k n.succ m d =
      (match lookup k m with | some v => v | none => d) :: lookup_all_index (k + 1) n m d

#source_check "src/rocq/Utils/IntMaps.v|Vellvm.Utils.IntMaps|lookup_all_index_add_out_aux"
  lookup_all_index_add_out_aux : ∀ {A : Type u} (l : List Int) (k : Int) (n : Nat) (m : IntMap A)
    (key : Int) (x d : A), l = ListUtil.Zseq k n → (key < k ∨ key ≥ k + (n : Int)) →
    lookup_all_index k n (add key x m) d = lookup_all_index k n m d

#source_check "src/rocq/Utils/IntMaps.v|Vellvm.Utils.IntMaps|lookup_all_index_add_out"
  lookup_all_index_add_out : ∀ {A : Type u} (k : Int) (n : Nat) (m : IntMap A) (key : Int)
    (x d : A), (key < k ∨ key ≥ k + (n : Int)) →
    lookup_all_index k n (add key x m) d = lookup_all_index k n m d

#source_check "src/rocq/Utils/IntMaps.v|Vellvm.Utils.IntMaps|lookup_all_index_add"
  lookup_all_index_add : ∀ {A : Type u} (k : Int) (size : Nat) (x : A) (m : IntMap A) (d : A),
    lookup_all_index k size.succ (add k x m) d = x :: lookup_all_index (k + 1) size m d

#source_check "src/rocq/Utils/IntMaps.v|Vellvm.Utils.IntMaps|pred_succ_of_nat"
  pred_succ_of_nat : ∀ n : Nat, (⟨n.succ, Nat.zero_lt_succ n⟩ : Positive).val.pred = n

#source_check "src/rocq/Utils/IntMaps.v|Vellvm.Utils.IntMaps|lookup_all_index_length"
  lookup_all_index_length : ∀ {A : Type u} (len : Nat) (off : Int) (bytes : IntMap A) (d : A),
    (lookup_all_index off len bytes d).length = len

#source_check "src/rocq/Utils/IntMaps.v|Vellvm.Utils.IntMaps|lookup_add_all_index_in"
  lookup_add_all_index_in : ∀ {A : Type u} (l : List A) (k z : Int) (m : IntMap A) (v : A),
    (z ≤ k ∧ k ≤ z + (l.length : Int) - 1) → list_nth_z l (k - z) = some v →
    lookup k (add_all_index l z m) = some v

#source_check "src/rocq/Utils/IntMaps.v|Vellvm.Utils.IntMaps|lookup_add_all_index_out"
  lookup_add_all_index_out : ∀ {A : Type u} (l : List A) (k z : Int) (m : IntMap A),
    (k < z ∨ k ≥ z + (l.length : Int)) → lookup k (add_all_index l z m) = lookup k m

#source_check "src/rocq/Utils/IntMaps.v|Vellvm.Utils.IntMaps|key_in_range_or_not_aux"
  key_in_range_or_not_aux : ∀ {A : Type u} (k z : Int) (l : List A),
    PSum (PSum (z ≤ k ∧ k ≤ z + (l.length : Int) - 1) (k < z)) (k ≥ z + (l.length : Int))

#source_check "src/rocq/Utils/IntMaps.v|Vellvm.Utils.IntMaps|key_in_range_or_not"
  key_in_range_or_not : ∀ {A : Type u} (k z : Int) (l : List A),
    PSum (z ≤ k ∧ k ≤ z + (l.length : Int) - 1) (k < z ∨ k ≥ z + (l.length : Int))

#source_check "src/rocq/Utils/IntMaps.v|Vellvm.Utils.IntMaps|range_list_nth_z"
  range_list_nth_z : ∀ {A : Type u} (l : List A) (k : Int),
    (0 ≤ k ∧ k < (l.length : Int)) → ∃ v, list_nth_z l k = some v

#source_check "src/rocq/Utils/IntMaps.v|Vellvm.Utils.IntMaps|in_range_is_in"
  in_range_is_in : ∀ {A : Type u} (k z : Int) (l : List A),
    (z ≤ k ∧ k ≤ z + (l.length : Int) - 1) → ∃ v, list_nth_z l (k - z) = some v

#source_check "src/rocq/Utils/IntMaps.v|Vellvm.Utils.IntMaps|add_all_index_twice"
  add_all_index_twice : ∀ {A : Type u} (l₁ l₂ : List A) (z : Int) (m : IntMap A),
    (l₁.length : Int) = (l₂.length : Int) →
    Equal (add_all_index l₂ z (add_all_index l₁ z m)) (add_all_index l₂ z m)
