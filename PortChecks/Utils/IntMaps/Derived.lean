import PortChecks.SourceType
import Vellvm.Utils.IntMaps.Foundations
import Vellvm.Utils.IntMaps.Traversal
import PortChecks.Utils.IntMaps.Ranges
import PortChecks.Utils.IntMaps.Refinement
import PortChecks.Utils.IntMaps.Filter

open Vellvm Vellvm.Utils.IntMaps
universe u v

#source_check "src/rocq/Utils/IntMaps.v|Vellvm.Utils.IntMaps|maximumBy_Z_le_def"
  maximumBy_Z_le_def : ∀ (d : Int) (l : List Int) (e : Int), decide (e ≤ d) = true →
    decide (e ≤ maximumBy (fun x y : Int ↦ decide (x ≤ y)) d l) = true

#source_check "src/rocq/Utils/IntMaps.v|Vellvm.Utils.IntMaps|maximumBy_Z_def"
  maximumBy_Z_def : ∀ (d : Int) (l : List Int),
    decide (d ≤ maximumBy (fun x y : Int ↦ decide (x ≤ y)) d l) = true

#source_check "src/rocq/Utils/IntMaps.v|Vellvm.Utils.IntMaps|maximumBy_Z_correct"
  maximumBy_Z_correct : ∀ (d : Int) (l : List Int) (a : Int), a ∈ l →
    decide (a ≤ maximumBy (fun x y : Int ↦ decide (x ≤ y)) d l) = true

#source_check "src/rocq/Utils/IntMaps.v|Vellvm.Utils.IntMaps|next_key_old_gt_0"
  next_key_old_gt_0 : ∀ {A : Type u} (m : IntMap A), 0 ≤ next_key_old m

#source_check "src/rocq/Utils/IntMaps.v|Vellvm.Utils.IntMaps|MapsTo_inj"
  MapsTo_inj : ∀ {A : Type u} (k : Int) (v w : A) (m : IntMap A),
    IM.MapsTo k v m → IM.MapsTo k w m → v = w

#source_check "src/rocq/Utils/IntMaps.v|Vellvm.Utils.IntMaps|member_lookup"
  member_lookup : ∀ {A : Type u} (k : Int) (m : IntMap A), member k m = true →
    ∃ v, lookup k m = some v

#source_check "src/rocq/Utils/IntMaps.v|Vellvm.Utils.IntMaps|lookup_member"
  lookup_member : ∀ {A : Type u} (k : Int) (v : A) (m : IntMap A),
    lookup k m = some v → member k m = true

#source_check "src/rocq/Utils/IntMaps.v|Vellvm.Utils.IntMaps|lookup_add_eq"
  lookup_add_eq : ∀ {A : Type u} (k : Int) (x : A) (m : IntMap A), lookup k (add k x m) = some x

#source_check "src/rocq/Utils/IntMaps.v|Vellvm.Utils.IntMaps|lookup_add_ineq"
  lookup_add_ineq : ∀ {A : Type u} (k k' : Int) (x : A) (m : IntMap A),
    k ≠ k' → lookup k (add k' x m) = lookup k m

#source_check "src/rocq/Utils/IntMaps.v|Vellvm.Utils.IntMaps|member_add_eq"
  member_add_eq : ∀ {A : Type u} (k : Int) (v : A) (m : IntMap A), member k (add k v m) = true

#source_check "src/rocq/Utils/IntMaps.v|Vellvm.Utils.IntMaps|member_add_ineq"
  member_add_ineq : ∀ {A : Type u} (k k' : Int) (v : A) (m : IntMap A), k ≠ k' →
    (member k (add k' v m) = true ↔ member k m = true)

#source_check "src/rocq/Utils/IntMaps.v|Vellvm.Utils.IntMaps|member_add_preserved"
  member_add_preserved : ∀ {A : Type u} (k k' : Int) (v : A) (m : IntMap A),
    member k m = true → member k (add k' v m) = true

#source_check "src/rocq/Utils/IntMaps.v|Vellvm.Utils.IntMaps|Equal_Equiv"
  Equal_Equiv : ∀ {A : Type u}, Equivalence (@Equal A)

#source_check "src/rocq/Utils/IntMaps.v|Vellvm.Utils.IntMaps|Equiv_Equiv"
  Equiv_Equiv : ∀ {A : Type u} {r : A → A → Prop} {_ : Equivalence r},
    Equivalence (Vellvm.Utils.IntMaps.Equiv r)

#source_check "src/rocq/Utils/IntMaps.v|Vellvm.Utils.IntMaps|Proper_lookup"
  Proper_lookup : ∀ {A : Type u} (k : Int) (m n : IntMap A),
    Equal m n → lookup k m = lookup k n

#source_check "src/rocq/Utils/IntMaps.v|Vellvm.Utils.IntMaps|Proper_add"
  Proper_add : ∀ {A : Type u} (k j : Int), k = j → ∀ x y : A, x = y → ∀ m n : IntMap A,
    Equal m n → Equal (add k x m) (add j y n)

#source_check "src/rocq/Utils/IntMaps.v|Vellvm.Utils.IntMaps|add_add"
  add_add : ∀ {A : Type u} (off : Int) (b₁ b₂ : A) (m : IM.t A),
    Equal (add off b₂ (add off b₁ m)) (add off b₂ m)

#source_check "src/rocq/Utils/IntMaps.v|Vellvm.Utils.IntMaps|Equiv_add_add"
  Equiv_add_add : ∀ {A : Type u} {r : A → A → Prop} {_ : ∀ a, r a a} (k : Int) (v₁ v₂ : A)
    (m : IM.t A), Vellvm.Utils.IntMaps.Equiv r (add k v₂ (add k v₁ m)) (add k v₂ m)

#source_check "src/rocq/Utils/IntMaps.v|Vellvm.Utils.IntMaps|add_add_ineq"
  add_add_ineq : ∀ {A : Type u} (k₁ k₂ : Int) (v₁ v₂ : A) (m : IM.t A), k₁ ≠ k₂ →
    Equal (add k₂ v₂ (add k₁ v₁ m)) (add k₁ v₁ (add k₂ v₂ m))

#source_check "src/rocq/Utils/IntMaps.v|Vellvm.Utils.IntMaps|Traversable_RawIntMap"
  Traversable_RawIntMap : Traversable IM.Raw.tree.{u}

#source_check "src/rocq/Utils/IntMaps.v|Vellvm.Utils.IntMaps|Traversable_IntMap"
  Traversable_IntMap : Traversable (fun A : Type u ↦ IntMap A)

#source_check "src/rocq/Utils/IntMaps.v|Vellvm.Utils.IntMaps|Foldable_IS"
  Foldable_IS : Foldable.{0,0,u} IS.t Int

#source_check "src/rocq/Utils/IntMaps.v|Vellvm.Utils.IntMaps|Foldable_IM_Raw"
  Foldable_IM_Raw : ∀ {A : Type u}, Foldable.{u,0,v} (IM.Raw.tree A) Int

-- The raw traversal sequences left/root/right; the certified-map fold sequences the new event first.
example :
    let m := add 3 () (add 1 () (add 2 () empty))
    let visit := fun (k : Int) (_ : Unit) ↦ (modify (· ++ [k]) : StateM (List Int) Unit)
    ((traverseWithKeyRaw visit m.this).run []).2 = [1, 2, 3] ∧
      ((traverseWithKey visit m).run []).2 = [3, 2, 1] := ⟨rfl, rfl⟩
