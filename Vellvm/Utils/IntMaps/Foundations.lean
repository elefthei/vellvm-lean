module

public import Vellvm.Utils.IntMaps.Operations

@[expose] public section
namespace Vellvm.Utils.IntMaps

abbrev leb (x y : Int) := decide (x ≤ y)

theorem maximumBy_Z_le_def (d : Int) (l : List Int) (e : Int) :
    leb e d = true → leb e (maximumBy leb d l) = true := by
  simp only [leb, decide_eq_true_eq]
  intro h
  induction l generalizing d with
  | nil => exact h
  | cons x xs ih =>
    change e ≤ maximumBy leb (if leb d x then x else d) xs
    apply ih
    split <;> simp_all [leb] <;> omega

theorem maximumBy_Z_def (d : Int) (l : List Int) : leb d (maximumBy leb d l) = true :=
  maximumBy_Z_le_def d l d (by simp [leb])

theorem maximumBy_Z_correct (d : Int) (l : List Int) (a : Int) (ha : a ∈ l) :
    leb a (maximumBy leb d l) = true := by
  induction l generalizing d with
  | nil => cases ha
  | cons x xs ih =>
    change leb a (maximumBy leb (if leb d x then x else d) xs) = true
    rcases List.mem_cons.mp ha with rfl | hm
    · apply maximumBy_Z_le_def
      split <;> simp_all [leb] <;> omega
    · exact ih _ hm

theorem next_key_old_gt_0 {A : Type u} (m : IntMap A) : 0 ≤ next_key_old m := by
  let keys := (IM.elements m).map Prod.fst
  have h : -1 ≤ maximumBy leb (-1) keys := of_decide_eq_true (maximumBy_Z_def (-1) keys)
  change 0 ≤ 1 + maximumBy leb (-1) keys
  omega

theorem MapsTo_inj {A : Type u} (k : Int) (v w : A) (m : IntMap A)
    (hv : IM.MapsTo k v m) (hw : IM.MapsTo k w m) : v = w :=
  Option.some.inj (((lookup_mapsTo k v m).mpr hv).symm.trans ((lookup_mapsTo k w m).mpr hw))

theorem member_lookup {A : Type u} (k : Int) (m : IntMap A) (h : member k m) :
    ∃ v, lookup k m = some v := Option.isSome_iff_exists.mp (member_isSome k m ▸ h)

theorem lookup_member {A : Type u} (k : Int) (v : A) (m : IntMap A) (h : lookup k m = some v) :
    member k m := by simp [h]

theorem lookup_add_eq {A : Type u} (k : Int) (x : A) (m : IntMap A) :
    lookup k (add k x m) = some x := by simp

theorem lookup_add_ineq {A : Type u} (k k' : Int) (x : A) (m : IntMap A) (h : k ≠ k') :
    lookup k (add k' x m) = lookup k m := by simp [h]

theorem member_add_eq {A : Type u} (k : Int) (v : A) (m : IntMap A) : member k (add k v m) := by simp

theorem member_add_ineq {A : Type u} (k k' : Int) (v : A) (m : IntMap A) (h : k ≠ k') :
    member k (add k' v m) ↔ member k m := by simp [h]

theorem member_add_preserved {A : Type u} (k k' : Int) (v : A) (m : IntMap A)
    (h : member k m) : member k (add k' v m) := by by_cases k = k' <;> simp_all

theorem Equal_Equiv {A : Type u} : Equivalence (@Equal A) :=
  ⟨fun _ _ ↦ rfl, fun h k ↦ (h k).symm, fun h j k ↦ (h k).trans (j k)⟩

theorem Equiv_Equiv {A : Type u} {r : A → A → Prop} {hr : Equivalence r} : Equivalence (Equiv r) := by
  constructor
  · intro m
    refine ⟨fun _ ↦ Iff.rfl, fun k x y hx hy ↦ ?_⟩
    obtain rfl := Option.some.inj (hx.symm.trans hy)
    exact hr.refl x
  · intro m n h
    exact ⟨fun k ↦ (h.1 k).symm, fun k x y hx hy ↦ hr.symm (h.2 k y x hy hx)⟩
  · intro m n p h₁ h₂
    refine ⟨fun k ↦ (h₁.1 k).trans (h₂.1 k), fun k x z hx hz ↦ ?_⟩
    obtain ⟨y, hy⟩ := member_lookup k n ((h₁.1 k).mp (lookup_member k x m hx))
    exact hr.trans (h₁.2 k x y hx hy) (h₂.2 k y z hy hz)

theorem Proper_lookup {A : Type u} (k : Int) (m n : IntMap A) (h : Equal m n) :
    lookup k m = lookup k n := h k

theorem Proper_add {A : Type u} (k j : Int) (hk : k = j) (x y : A) (hx : x = y)
    (m n : IntMap A) (h : Equal m n) : Equal (add k x m) (add j y n) := by
  intro q
  simp [hk, hx, h q]

theorem add_add {A : Type u} (off : Int) (b₁ b₂ : A) (m : IM.t A) :
    Equal (add off b₂ (add off b₁ m)) (add off b₂ m) := by intro q; by_cases q = off <;> simp [*]

theorem Equiv_add_add {A : Type u} {r : A → A → Prop} {hr : ∀ a, r a a}
    (k : Int) (v₁ v₂ : A) (m : IM.t A) : Equiv r (add k v₂ (add k v₁ m)) (add k v₂ m) := by
  have he := add_add k v₁ v₂ m
  constructor
  · intro q; rw [member_isSome, member_isSome, he q]
  · intro q x y hx hy
    rw [he q] at hx
    obtain rfl := Option.some.inj (hx.symm.trans hy)
    exact hr x

theorem add_add_ineq {A : Type u} (k₁ k₂ : Int) (v₁ v₂ : A) (m : IM.t A) (hn : k₁ ≠ k₂) :
    Equal (add k₂ v₂ (add k₁ v₁ m)) (add k₁ v₁ (add k₂ v₂ m)) := by
  intro q
  by_cases h : q = k₁ <;> simp_all

end Vellvm.Utils.IntMaps
