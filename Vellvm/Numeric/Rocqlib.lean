/-
The Compcert verified compiler
Xavier Leroy, INRIA Paris-Rocquencourt

Copyright Institut National de Recherche en Informatique et en Automatique.
All rights reserved. This file is distributed under the terms of the GNU Lesser
General Public License as published by the Free Software Foundation, either
version 2.1 of the License, or (at your option) any later version.
This file is also distributed under the terms of the INRIA Non-Commercial
License Agreement.
-/
module

public import Vellvm.Types
public import Mathlib.Data.Int.Basic
public import Mathlib.Data.List.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

@[expose] public section
namespace Vellvm.Numeric.Rocqlib

universe u v w

abbrev EqDecision (A : Type u) := ∀ x y : A, PSum (x = y) (x ≠ y)

def chooseSide {P Q : Prop} {A : Type u} (d : PSum P Q) (a b : A) : A :=
  match d with | .inl _ => a | .inr _ => b

def decideSum (P : Prop) [Decidable P] : PSum P (¬P) :=
  if h : P then .inl h else .inr h

def eqDecidable {A : Type u} (d : EqDecision A) : DecidableEq A := fun x y ↦
  match d x y with | .inl h => isTrue h | .inr h => isFalse h

def posOne : Positive := ⟨1, by decide⟩
def posSucc (x : Positive) : Positive := ⟨x.val + 1, by omega⟩
def posPred (x : Positive) : Positive := ⟨max 1 (x.val - 1), by omega⟩

theorem modusponens : ∀ (P Q : Prop), P → (P → Q) → Q := fun _ _ p f ↦ f p

def peq : EqDecision Positive := fun x y ↦ decideSum (x = y)

theorem peq_true : ∀ (A : Type u) (x : Positive) (a b : A), chooseSide (peq x x) a b = a := by intros; simp [peq, decideSum, chooseSide]

theorem peq_false : ∀ (A : Type u) (x y : Positive) (a b : A), x ≠ y → chooseSide (peq x y) a b = b := by intros; simp_all [peq, decideSum, chooseSide]

abbrev Plt (x y : Positive) : Prop := x.val < y.val

theorem Plt_ne : ∀ x y, Plt x y → x ≠ y := by rintro x _ h rfl; exact Nat.lt_irrefl _ h

theorem Plt_trans : ∀ x y z, Plt x y → Plt y z → Plt x z := fun _ _ _ ↦ Nat.lt_trans

theorem Plt_succ : ∀ x, Plt x (posSucc x) := fun x ↦ Nat.lt_succ_self x.val

theorem Plt_trans_succ : ∀ x y, Plt x y → Plt x (posSucc y) := fun x y h ↦ Plt_trans x y _ h (Plt_succ y)

theorem Plt_succ_inv : ∀ x y, Plt x (posSucc y) → Plt x y ∨ x = y := by
  intro x y h
  rcases Nat.lt_or_eq_of_le (Nat.le_of_lt_succ h) with h | h
  · exact Or.inl h
  · exact Or.inr (Subtype.ext h)

def plt (x y : Positive) := decideSum (Plt x y)

abbrev Ple (x y : Positive) : Prop := x.val ≤ y.val

theorem Ple_refl : ∀ x, Ple x x := fun x ↦ Nat.le_refl x.val

theorem Ple_trans : ∀ x y z, Ple x y → Ple y z → Ple x z := fun _ _ _ ↦ Nat.le_trans

theorem Plt_Ple : ∀ x y, Plt x y → Ple x y := fun _ _ ↦ Nat.le_of_lt

theorem Ple_succ : ∀ x, Ple x (posSucc x) := fun x ↦ Nat.le_succ x.val

theorem Plt_Ple_trans : ∀ x y z, Plt x y → Ple y z → Plt x z := fun _ _ _ ↦ Nat.lt_of_lt_of_le

theorem Plt_strict : ∀ x, ¬ Plt x x := fun x ↦ Nat.lt_irrefl x.val

theorem Plt_wf : WellFounded Plt := (measure (fun x : Positive ↦ x.val)).wf

theorem Ppred_Plt : ∀ x, x ≠ posOne → Plt (posPred x) x := by
  intro x h
  have hx : x.val ≠ 1 := fun e ↦ h (Subtype.ext e)
  change max 1 (x.val - 1) < x.val
  have := x.property
  omega

def positive_rec (A : Type u) (v : A) (f : Positive → A → A) (x : Positive) : A :=
  if h : x = posOne then v else f (posPred x) (positive_rec A v f (posPred x))
termination_by x.val
decreasing_by exact Ppred_Plt x h

theorem unroll_positive_rec : ∀ (A : Type u) (v : A) (f : Positive → A → A) (x : Positive),
    positive_rec A v f x = chooseSide (peq x posOne) v (f (posPred x) (positive_rec A v f (posPred
    x))) := by
  intro A v f x
  rw [positive_rec]
  by_cases h : x = posOne <;> simp [peq, decideSum, chooseSide, h]

theorem positive_rec_base : ∀ (A : Type u) (v : A) (f : Positive → A → A), positive_rec A v f posOne
    = v := by intros; rw [positive_rec]; simp

theorem positive_rec_succ : ∀ (A : Type u) (v : A) (f : Positive → A → A) (x : Positive),
    positive_rec A v f (posSucc x) = f x (positive_rec A v f x) := by
  intro A v f x
  have h : posSucc x ≠ posOne := by
    intro e
    have he := congrArg Subtype.val e
    change x.val + 1 = 1 at he
    have := x.property
    omega
  have pred : posPred (posSucc x) = x := by
    apply Subtype.ext
    change max 1 (x.val + 1 - 1) = x.val
    have := x.property
    omega
  rw [positive_rec, dif_neg h, pred]

theorem positive_Peano_ind : ∀ (P : Positive → Prop), P posOne → (∀ x, P x → P (posSucc x)) → ∀ x, P
    x := by
  rintro P base step ⟨n,h⟩
  cases n with
  | zero => omega
  | succ n =>
    induction n with
    | zero => exact base
    | succ n ih => exact step ⟨n+1, by omega⟩ (ih (by omega))

def zeq : EqDecision Int := fun x y ↦ decideSum (x = y)

theorem zeq_true : ∀ (A : Type u) (x : Int) (a b : A), chooseSide (zeq x x) a b = a := by intros; simp [zeq, decideSum, chooseSide]

theorem zeq_false : ∀ (A : Type u) (x y : Int) (a b : A), x ≠ y → chooseSide (zeq x y) a b = b := by intros; simp_all [zeq, decideSum, chooseSide]

def zlt (x y : Int) : PSum (x < y) (y ≤ x) :=
  if h : x < y then .inl h else .inr (by omega)

theorem zlt_true : ∀ (A : Type u) (x y : Int) (a b : A), x < y → chooseSide (zlt x y) a b = a := by intros; simp_all [zlt, chooseSide]

theorem zlt_false : ∀ (A : Type u) (x y : Int) (a b : A), x ≥ y → chooseSide (zlt x y) a b = b := by intros; simp_all [zlt, chooseSide, not_lt_of_ge]

def zle (x y : Int) : PSum (x ≤ y) (y < x) :=
  if h : x ≤ y then .inl h else .inr (by omega)

theorem zle_true : ∀ (A : Type u) (x y : Int) (a b : A), x ≤ y → chooseSide (zle x y) a b = a := by intros; simp_all [zle, chooseSide]

theorem zle_false : ∀ (A : Type u) (x y : Int) (a b : A), x > y → chooseSide (zle x y) a b = b := by intros; simp_all [zle, chooseSide, not_le_of_gt]

abbrev two_power_nat (n : Nat) : Int := Int.ofNat (2 ^ n)
abbrev two_power_pos (n : Positive) : Int := two_power_nat n.val

def two_p : Int → Int
  | .ofNat n => two_power_nat n
  | .negSucc _ => 0

theorem two_power_nat_O : two_power_nat 0 = 1 := rfl

theorem two_power_nat_pos : ∀ n, 0 < two_power_nat n :=
  fun _ ↦ Int.ofNat_lt.mpr (Nat.pow_pos (by decide))

theorem two_power_nat_two_p : ∀ (n : Nat), two_power_nat n = two_p (Int.ofNat n) := fun _ ↦ rfl

theorem two_power_pos_two_p : ∀ (x : Positive), two_power_pos x = two_p (Int.ofNat x.val) := fun _ ↦ rfl

theorem two_p_monotone : ∀ x y, 0 ≤ x ∧ x ≤ y → two_p x ≤ two_p y := by
  rintro (x | x) (y | y) h <;> try omega
  exact Int.ofNat_le.mpr (Nat.pow_le_pow_right (by decide) (Int.ofNat_le.mp h.2))

theorem two_p_monotone_strict : ∀ x y, 0 ≤ x ∧ x < y → two_p x < two_p y := by
  rintro (x | x) (y | y) h <;> try omega
  exact Int.ofNat_lt.mpr (Nat.pow_lt_pow_right (by decide) (Int.ofNat_lt.mp h.2))

theorem two_p_strict : ∀ x, x ≥ 0 → x < two_p x := by
  rintro (n | n) h
  · exact Int.ofNat_lt.mpr Nat.lt_two_pow_self
  · omega

theorem two_p_strict_2 : ∀ x, x ≥ 0 → 2 * x - 1 < two_p x := by
  rintro (n | n) h <;> try omega
  cases n with
  | zero => decide
  | succ n =>
    have hx := Nat.lt_two_pow_self (n := n)
    simp only [two_p, two_power_nat, Nat.pow_succ, Int.ofNat_eq_natCast, Int.natCast_mul,
      Int.natCast_succ]
    omega

theorem Zmin_spec : ∀ x y : Int, min x y = chooseSide (zlt x y) x y := by intro x y; unfold zlt; split <;> simp [chooseSide] <;> omega

theorem Zmax_spec : ∀ x y : Int, max x y = chooseSide (zlt y x) x y := by intro x y; unfold zlt; split <;> simp [chooseSide] <;> omega

theorem Zmax_bound_l : ∀ x y z : Int, x ≤ y → x ≤ max y z := by intros; omega

theorem Zmax_bound_r : ∀ x y z : Int, x ≤ z → x ≤ max y z := by intros; omega

theorem Zdiv_small : ∀ x y : Int, 0 ≤ x ∧ x < y → x.fdiv y = 0 := fun _ _ h ↦ Int.fdiv_eq_zero_of_lt h.1 h.2

theorem Zmod_small : ∀ x y : Int, 0 ≤ x ∧ x < y → x.fmod y = x := fun _ _ h ↦ Int.fmod_eq_of_lt h.1 h.2

theorem Zmod_unique : ∀ x y a b : Int, x = a * y + b → 0 ≤ b ∧ b < y → x.fmod y = b := by
  rintro _ y a b rfl h
  exact ((Int.fdiv_fmod_unique (q := a) (by omega : 0 < y)).2 ⟨by ring, h⟩).2

theorem Zdiv_unique : ∀ x y a b : Int, x = a * y + b → 0 ≤ b ∧ b < y → x.fdiv y = a := by
  rintro _ y a b rfl h
  exact ((Int.fdiv_fmod_unique (r := b) (by omega : 0 < y)).2 ⟨by ring, h⟩).1

theorem Zdiv_Zdiv : ∀ a b c : Int, 0 < b → 0 < c → (a.fdiv b).fdiv c = a.fdiv (b * c) := by
  intro a b c hb hc
  simp only [Int.fdiv_eq_ediv_of_nonneg _ hb.le, Int.fdiv_eq_ediv_of_nonneg _ hc.le,
    Int.fdiv_eq_ediv_of_nonneg _ (mul_nonneg hb.le hc.le), Int.ediv_ediv_of_nonneg hb.le]

theorem Zmult_le_compat_l_neg : ∀ n m p : Int, n ≥ m → p ≤ 0 → p * n ≤ p * m := fun _ _ _ h hp ↦ mul_le_mul_of_nonpos_left h hp

theorem Zdiv_interval_1 : ∀ lo hi a b : Int, lo ≤ 0 → 0 < hi → 0 < b → lo * b ≤ a ∧ a < hi * b → lo ≤
    a.fdiv b ∧ a.fdiv b < hi := by
  intro lo hi a b _ _ hb h
  rw [Int.fdiv_eq_ediv_of_nonneg _ hb.le]
  exact ⟨(Int.le_ediv_iff_mul_le hb).2 h.1, (Int.ediv_lt_iff_lt_mul hb).2 h.2⟩

theorem Zdiv_interval_2 : ∀ lo hi a b : Int, lo ≤ a ∧ a ≤ hi → lo ≤ 0 → 0 ≤ hi → 0 < b → lo ≤ a.fdiv
    b ∧ a.fdiv b ≤ hi := by
  intro lo hi a b h hlo hhi hb
  have hmul : lo * b ≤ lo * 1 := mul_le_mul_of_nonpos_left (by omega) hlo
  have hmul' : (hi+1) * 1 ≤ (hi+1) * b := mul_le_mul_of_nonneg_left (by omega) (by omega)
  have := Zdiv_interval_1 lo (hi+1) a b hlo (by omega) hb ⟨by omega, by omega⟩
  omega

theorem Zmod_recombine : ∀ x a b : Int, 0 < a → 0 < b → x.fmod (a * b) = (x.fdiv b).fmod a * b +
    x.fmod b := by
  intro x a b ha hb
  let q := x.fdiv b
  have eq₁ := Int.fdiv_mul_add_fmod x b
  have eq₂ := Int.fdiv_mul_add_fmod q a
  apply Zmod_unique _ _ (q.fdiv a)
  · calc x = q * b + x.fmod b := eq₁.symm
         _ = (q.fdiv a * a + q.fmod a) * b + x.fmod b := by rw [eq₂]
         _ = _ := by ring
  · have h₁ := Int.fmod_nonneg_of_pos x hb
    have h₂ := Int.fmod_nonneg_of_pos q ha
    have h₃ := Int.fmod_lt_of_pos x hb
    have h₄ := Int.fmod_lt_of_pos q ha
    have h₅ := mul_le_mul_of_nonneg_right (show q.fmod a + 1 ≤ a by omega) hb.le
    change 0 ≤ q.fmod a * b + x.fmod b ∧ q.fmod a * b + x.fmod b < a * b
    constructor
    · exact add_nonneg (mul_nonneg h₂ hb.le) h₁
    · nlinarith

theorem Zdivides_trans : ∀ x y z : Int, x ∣ y → y ∣ z → x ∣ z := fun _ _ _ ↦ dvd_trans

def Zdivide_dec (p q : Int) (_ : 0 < p) := decideSum (p ∣ q)

theorem Zdivide_interval : ∀ a b c : Int, 0 < c → 0 ≤ a ∧ a < b → c ∣ a → c ∣ b → 0 ≤ a ∧ a ≤ b - c := by
  rintro _ _ c hc h ⟨x, rfl⟩ ⟨y, rfl⟩
  have hxy : x < y := (mul_lt_mul_iff_right₀ hc).mp h.2
  have := mul_le_mul_of_nonneg_left (show x + 1 ≤ y by omega) hc.le
  exact ⟨h.1, by linarith⟩

abbrev nat_of_Z := Int.toNat

theorem nat_of_Z_of_nat : ∀ n, nat_of_Z (Int.ofNat n) = n := fun _ ↦ rfl

theorem nat_of_Z_max : ∀ z, Int.ofNat (nat_of_Z z) = max z 0 := Int.toNat_eq_max

theorem nat_of_Z_eq : ∀ z, z ≥ 0 → Int.ofNat (nat_of_Z z) = z := fun _ ↦ Int.toNat_of_nonneg

theorem nat_of_Z_neg : ∀ z, z ≤ 0 → nat_of_Z z = 0 := by intros; unfold nat_of_Z; omega

theorem nat_of_Z_plus : ∀ p q, p ≥ 0 → q ≥ 0 → nat_of_Z (p + q) = nat_of_Z p + nat_of_Z q := by intros; unfold nat_of_Z; omega

def align (x y : Int) : Int := (x + y - 1).fdiv y * y

theorem align_le : ∀ x y, 0 < y → x ≤ align x y := by
  intro x y hy
  have := Int.fdiv_mul_add_fmod (x+y-1) y
  have := Int.fmod_lt_of_pos (x+y-1) hy
  unfold align
  omega

theorem align_divides : ∀ x y, 0 < y → y ∣ align x y := fun x y _ ↦ ⟨_, Int.mul_comm _ _⟩

def option_eq {A : Type u} (d : EqDecision A) : EqDecision (Option A) :=
  letI : DecidableEq A := eqDecidable d
  fun x y ↦ decideSum (x = y)

inductive option_rel {A : Type u} {B : Type v} (R : A → B → Prop) : Option A → Option B → Prop
  | none : option_rel R none none
  | some (x y) : R x y → option_rel R (some x) (some y)

def option_rel_none {A : Type u} {B : Type v} (R : A → B → Prop) := option_rel.none (R := R)
def option_rel_some {A : Type u} {B : Type v} (R : A → B → Prop) (x y) := option_rel.some (R := R) x y

theorem option_rel_ind : ∀ {A : Type u} {B : Type v} {R : A → B → Prop} (P : Option A → Option B →
    Prop), P none none → (∀ x y, R x y → P (some x) (some y)) → ∀ {a b}, option_rel R a b → P a b := by
  intro A B R P hn hs x y h
  cases h with
  | none => exact hn
  | some x y h => exact hs x y h

theorem option_rel_sind : ∀ {A : Type u} {B : Type v} {R : A → B → Prop} (P : Option A → Option B →
    Prop), P none none → (∀ x y, R x y → P (some x) (some y)) → ∀ {a b}, option_rel R a b → P a b := @option_rel_ind

abbrev option_map {A : Type u} {B : Type v} := @Option.map A B

def sum_left_map {A : Type u} {B : Type v} {C : Type w} (f : A → B) : A ⊕ C → B ⊕ C := Sum.map f id

theorem nth_error_in : ∀ {A : Type u} (n : Nat) (l : List A) {x}, l[n]? = some x → x ∈ l := @fun _ _ _ _ ↦ List.mem_of_getElem?

theorem nth_error_nil : ∀ (A : Type u) (n : Nat), ([] : List A)[n]? = none := by intros; simp

def list_length_z_aux {A : Type u} (l : List A) (n : Int) : Int := n + l.length

theorem list_length_z_aux_shift : ∀ {A : Type u} (l : List A) (n m : Int), list_length_z_aux l n =
    list_length_z_aux l m + (n - m) := by intros; unfold list_length_z_aux; omega

def list_length_z {A : Type u} (l : List A) : Int := list_length_z_aux l 0

theorem list_length_z_cons : ∀ {A : Type u} (x : A) (l : List A), list_length_z (x :: l) =
    list_length_z l + 1 := by intros; simp [list_length_z, list_length_z_aux]

theorem list_length_z_pos : ∀ {A : Type u} (l : List A), list_length_z l ≥ 0 := by intros; simp [list_length_z, list_length_z_aux]

theorem list_length_z_map : ∀ {A : Type u} {B : Type v} (f : A → B) (l : List A), list_length_z
    (l.map f) = list_length_z l := by intros; simp [list_length_z, list_length_z_aux]

def list_nth_z {A : Type u} (l : List A) : Int → Option A
  | .ofNat n => l[n]?
  | .negSucc _ => none

theorem list_nth_z_in : ∀ {A : Type u} (l : List A) (n : Int) {x}, list_nth_z l n = some x → x ∈ l := by
  rintro A l (n | n) x h
  · exact List.mem_of_getElem? h
  · contradiction

theorem list_nth_z_map : ∀ {A : Type u} {B : Type v} (f : A → B) (l : List A) (n : Int), list_nth_z
    (l.map f) n = option_map f (list_nth_z l n) := by rintro A B f l (n | n) <;> simp [list_nth_z, option_map]

theorem list_nth_z_range : ∀ {A : Type u} (l : List A) (n : Int) {x}, list_nth_z l n = some x → 0 ≤ n
    ∧ n < list_length_z l := by
  rintro A l (n | n) x h
  · obtain ⟨hn, _⟩ := List.getElem?_eq_some_iff.mp h
    simp [list_length_z, list_length_z_aux]; omega
  · contradiction

theorem incl_cons_inv : ∀ {A : Type u} {a : A} {b c : List A}, a :: b ⊆ c → b ⊆ c := @fun _ _ _ _ h _ hx ↦ h (List.mem_cons_of_mem _ hx)

theorem incl_app_inv_l : ∀ {A : Type u} (l₁ l₂ : List A) {m : List A}, l₁ ++ l₂ ⊆ m → l₁ ⊆ m := @fun _ _ _ _ h _ hx ↦ h (List.mem_append_left _ hx)

theorem incl_app_inv_r : ∀ {A : Type u} (l₁ l₂ : List A) {m : List A}, l₁ ++ l₂ ⊆ m → l₂ ⊆ m := @fun _ _ _ _ h _ hx ↦ h (List.mem_append_right _ hx)

theorem incl_same_head : ∀ {A : Type u} {x : A} {l₁ l₂ : List A}, l₁ ⊆ l₂ → x :: l₁ ⊆ x :: l₂ := @fun _ _ _ _ h ↦ List.cons_subset_cons _ h

theorem list_map_exten : ∀ {A : Type u} {B : Type v} (f g : A → B) (l : List A), (∀ x ∈ l, f x = g x)
    → l.map g = l.map f := @fun _ _ _ _ _ h ↦ (List.map_congr_left h).symm

theorem list_map_compose : ∀ {A : Type u} {B : Type v} {C : Type w} (f : A → B) (g : B → C) (l : List
    A), (l.map f).map g = l.map (fun x ↦ g (f x)) := by intros; simp [Function.comp_def]

theorem list_map_identity : ∀ {A : Type u} (l : List A), l.map (fun x ↦ x) = l := by intros; simp

theorem list_map_nth : ∀ {A : Type u} {B : Type v} (f : A → B) (l : List A) (n : Nat), (l.map f)[n]?
    = option_map f l[n]? := @fun _ _ _ _ _ ↦ List.getElem?_map

theorem list_length_map : ∀ {A : Type u} {B : Type v} (f : A → B) (l : List A), (l.map f).length =
    l.length := by intros; simp

theorem list_in_map_inv : ∀ {A : Type u} {B : Type v} (f : A → B) (l : List A) (y : B), y ∈ l.map f →
    ∃ x, y = f x ∧ x ∈ l := by
  intro A B f l y h
  obtain ⟨x, hx, e⟩ := List.mem_map.mp h
  exact ⟨x, e.symm, hx⟩

theorem list_append_map : ∀ {A : Type u} {B : Type v} (f : A → B) (l₁ l₂ : List A), (l₁ ++ l₂).map f
    = l₁.map f ++ l₂.map f := by intros; simp

theorem list_append_map_inv : ∀ {A : Type u} {B : Type v} (f : A → B) (m₁ m₂ : List B) (l : List A),
    l.map f = m₁ ++ m₂ → ∃ l₁ l₂, l₁.map f = m₁ ∧ l₂.map f = m₂ ∧ l = l₁ ++ l₂ := by
  intro A B f m₁ m₂ l h
  refine ⟨l.take m₁.length, l.drop m₁.length, ?_, ?_, (List.take_append_drop _ _).symm⟩
  · simpa [List.map_take, h]
  · simpa [List.map_drop, h]

def list_fold_left {A : Type u} {B : Type v} (f : A → B → B) (acc : B) (l : List A) :=
  l.foldl (fun b a ↦ f a b) acc

def list_fold_right {A : Type u} {B : Type v} (f : A → B → B) (l : List A) (base : B) :=
  list_fold_left f base l.reverse

theorem list_fold_left_app : ∀ {A : Type u} {B : Type v} (f : A → B → B) (l₁ l₂ : List A) (acc : B),
    list_fold_left f acc (l₁ ++ l₂) = list_fold_left f (list_fold_left f acc l₁) l₂ := by intros; simp [list_fold_left]

theorem list_fold_right_eq : ∀ {A : Type u} {B : Type v} (f : A → B → B) (l : List A) (base : B),
    list_fold_right f l base = (match l with | [] => base | x :: xs => f x (list_fold_right f xs
    base)) := by
  intro A B f l base
  cases l <;> simp [list_fold_right, list_fold_left, List.foldl_reverse]

theorem list_fold_right_spec : ∀ {A : Type u} {B : Type v} (f : A → B → B) (l : List A) (base : B),
    list_fold_right f l base = l.foldr f base := by intros; simp [list_fold_right, list_fold_left, List.foldl_reverse]

theorem in_cns : ∀ {A : Type u} (x y : A) (l : List A), x ∈ y :: l ↔ y = x ∨ x ∈ l := by intros; simp [eq_comm]

theorem in_app : ∀ {A : Type u} (x : A) (l₁ l₂ : List A), x ∈ l₁ ++ l₂ ↔ x ∈ l₁ ∨ x ∈ l₂ := by intros; exact List.mem_append

theorem list_in_insert : ∀ {A : Type u} (x : A) (l₁ l₂ : List A) (y : A), x ∈ l₁ ++ l₂ → x ∈ l₁ ++ y
    :: l₂ := by intros; grind

def list_disjoint {A : Type u} (l m : List A) : Prop := ∀ x y, x ∈ l → y ∈ m → x ≠ y

theorem list_disjoint_cons_l : ∀ {A : Type u} {a : A} {l₁ l₂ : List A}, list_disjoint l₁ l₂ → a ∉ l₂
    → list_disjoint (a :: l₁) l₂ := by unfold list_disjoint; grind

theorem list_disjoint_cons_r : ∀ {A : Type u} {a : A} {l₁ l₂ : List A}, list_disjoint l₁ l₂ → a ∉ l₁
    → list_disjoint l₁ (a :: l₂) := by unfold list_disjoint; grind

theorem list_disjoint_cons_left : ∀ {A : Type u} {a : A} {l₁ l₂ : List A}, list_disjoint (a :: l₁) l₂
    → list_disjoint l₁ l₂ := @fun _ _ _ _ h x y hx hy ↦ h x y (List.mem_cons_of_mem _ hx) hy

theorem list_disjoint_cons_right : ∀ {A : Type u} {a : A} {l₁ l₂ : List A}, list_disjoint l₁ (a ::
    l₂) → list_disjoint l₁ l₂ := @fun _ _ _ _ h x y hx hy ↦ h x y hx (List.mem_cons_of_mem _ hy)

theorem list_disjoint_notin : ∀ {A : Type u} {l₁ l₂ : List A} (a : A), list_disjoint l₁ l₂ → a ∈ l₁ →
    a ∉ l₂ := @fun _ _ _ a h ha hb ↦ h a a ha hb rfl

theorem list_disjoint_sym : ∀ {A : Type u} {l₁ l₂ : List A}, list_disjoint l₁ l₂ → list_disjoint l₂
    l₁ := @fun _ _ _ h x y hx hy ↦ (h y x hy hx).symm

def list_disjoint_dec {A : Type u} (d : EqDecision A) (l m : List A) :
    PSum (list_disjoint l m) (¬list_disjoint l m) :=
  letI : DecidableEq A := eqDecidable d
  if h : ∀ x ∈ l, x ∉ m then .inl (fun x _ hx hy e ↦ h x hx (e.symm ▸ hy))
  else .inr (fun hd ↦ h (fun x hx ↦ list_disjoint_notin x hd hx))

def list_equiv {A : Type u} (l m : List A) : Prop := ∀ x, x ∈ l ↔ x ∈ m

abbrev list_norepet {A : Type u} (l : List A) := l.Nodup

theorem list_norepet_nil (A : Type u) : list_norepet ([] : List A) := List.nodup_nil
theorem list_norepet_cons {A : Type u} (x : A) {l} (h : x ∉ l) (hn : list_norepet l) :
    list_norepet (x :: l) := List.nodup_cons.mpr ⟨h, hn⟩

theorem list_norepet_ind : ∀ {A : Type u} (P : List A → Prop), P [] → (∀ x xs, x ∉ xs → list_norepet
    xs → P xs → P (x :: xs)) → ∀ {l}, list_norepet l → P l := by
  intro A P hn hc l h
  induction l with
  | nil => exact hn
  | cons x l ih =>
    obtain ⟨hx, hl⟩ := List.nodup_cons.mp h
    exact hc x l hx hl (ih hl)

theorem list_norepet_sind : ∀ {A : Type u} (P : List A → Prop), P [] → (∀ x xs, x ∉ xs → list_norepet
    xs → P xs → P (x :: xs)) → ∀ {l}, list_norepet l → P l := @list_norepet_ind

def list_norepet_dec {A : Type u} (d : EqDecision A) (l : List A) :
    PSum (list_norepet l) (¬list_norepet l) :=
  letI : DecidableEq A := eqDecidable d
  decideSum (list_norepet l)

theorem list_map_norepet : ∀ {A : Type u} {B : Type v} (f : A → B) {l : List A}, list_norepet l → (∀
    x y, x ∈ l → y ∈ l → x ≠ y → f x ≠ f y) → list_norepet (l.map f) := by
  intro A B f l hl h
  induction l with
  | nil => exact List.nodup_nil
  | cons x l ih =>
    obtain ⟨hx, ht⟩ := List.nodup_cons.mp hl
    apply List.nodup_cons.mpr
    constructor
    · intro hm
      obtain ⟨y, hy, e⟩ := List.mem_map.mp hm
      exact h y x (by simp [hy]) (by simp) (fun he ↦ hx (he ▸ hy)) e
    · exact ih ht (fun a b ha hb ↦ h a b (by simp [ha]) (by simp [hb]))

theorem list_norepet_app : ∀ {A : Type u} (l₁ l₂ : List A), list_norepet (l₁ ++ l₂) ↔ list_norepet l₁
    ∧ list_norepet l₂ ∧ list_disjoint l₁ l₂ := by
  intro A l m
  unfold list_norepet list_disjoint
  rw [List.nodup_append]
  grind

theorem list_norepet_append_commut : ∀ {A : Type u} (a b : List A), list_norepet (a ++ b) →
    list_norepet (b ++ a) := by
  intro A l m h
  obtain ⟨hl, hm, hd⟩ := (list_norepet_app l m).mp h
  exact (list_norepet_app m l).mpr ⟨hm, hl, list_disjoint_sym hd⟩

theorem list_norepet_append : ∀ {A : Type u} {l₁ l₂ : List A}, list_norepet l₁ → list_norepet l₂ →
    list_disjoint l₁ l₂ → list_norepet (l₁ ++ l₂) := @fun _ _ _ hl hm hd ↦ (list_norepet_app _ _).mpr ⟨hl, hm, hd⟩

theorem list_norepet_append_right : ∀ {A : Type u} (l₁ l₂ : List A), list_norepet (l₁ ++ l₂) →
    list_norepet l₂ := @fun _ l m h ↦ ((list_norepet_app l m).mp h).2.1

theorem list_norepet_append_left : ∀ {A : Type u} (l₁ l₂ : List A), list_norepet (l₁ ++ l₂) →
    list_norepet l₁ := @fun _ l m h ↦ ((list_norepet_app l m).mp h).1

inductive is_tail {A : Type u} : List A → List A → Prop
  | refl (l) : is_tail l l
  | cons (x : A) {l m} : is_tail l m → is_tail l (x :: m)

def is_tail_refl {A : Type u} (l : List A) := is_tail.refl l
def is_tail_cons {A : Type u} (x : A) {l m : List A} := @is_tail.cons A x l m

theorem is_tail_ind : ∀ {A : Type u} (P : List A → List A → Prop), (∀ c, P c c) → (∀ i c₁ c₂, is_tail
    c₁ c₂ → P c₁ c₂ → P c₁ (i :: c₂)) → ∀ {l m}, is_tail l m → P l m := by
  intro A P hr hc l m h
  induction h with
  | refl l => exact hr l
  | cons x h ih => exact hc x _ _ h ih

theorem is_tail_sind : ∀ {A : Type u} (P : List A → List A → Prop), (∀ c, P c c) → (∀ i c₁ c₂,
    is_tail c₁ c₂ → P c₁ c₂ → P c₁ (i :: c₂)) → ∀ {l m}, is_tail l m → P l m := @is_tail_ind

theorem is_tail_incl : ∀ {A : Type u} {l₁ l₂ : List A}, is_tail l₁ l₂ → l₁ ⊆ l₂ := by
  intro A l m h
  induction h with
  | refl => exact fun _ hx ↦ hx
  | cons _ _ ih => exact fun _ hx ↦ List.mem_cons_of_mem _ (ih hx)

theorem is_tail_trans : ∀ {A : Type u} {l₁ l₂ : List A}, is_tail l₁ l₂ → ∀ {l₃}, is_tail l₂ l₃ →
    is_tail l₁ l₃ := by
  intro A l m h n hn
  induction hn with
  | refl => exact h
  | cons x _ ih => exact .cons x (ih h)

theorem is_tail_in : ∀ {A : Type u} {i : A} {c₁ c₂ : List A}, is_tail (i :: c₁) c₂ → i ∈ c₂ := @fun _ _ _ _ h ↦ is_tail_incl h (by simp)

theorem is_tail_cons_left : ∀ {A : Type u} {i : A} {c₁ c₂ : List A}, is_tail (i :: c₁) c₂ → is_tail
    c₁ c₂ := @fun _ i _ _ h ↦ is_tail_trans (.cons i (.refl _)) h

abbrev list_forall2 {A : Type u} {B : Type v} := @List.Forall₂ A B

def list_forall2_nil {A : Type u} {B : Type v} (R : A → B → Prop) := List.Forall₂.nil (R := R)
def list_forall2_cons {A : Type u} {B : Type v} {R : A → B → Prop} (x : A) {l} (y : B) {m} :=
  @List.Forall₂.cons A B R x y l m

theorem list_forall2_ind : ∀ {A : Type u} {B : Type v} {R : A → B → Prop} (P : List A → List B →
    Prop), P [] [] → (∀ a l b m, R a b → list_forall2 R l m → P l m → P (a :: l) (b :: m)) → ∀ {l m},
    list_forall2 R l m → P l m := by
  intro A B R P hn hc l m h
  induction h with
  | nil => exact hn
  | cons hxy ht ih => exact hc _ _ _ _ hxy ht ih

theorem list_forall2_sind : ∀ {A : Type u} {B : Type v} {R : A → B → Prop} (P : List A → List B →
    Prop), P [] [] → (∀ a l b m, R a b → list_forall2 R l m → P l m → P (a :: l) (b :: m)) → ∀ {l m},
    list_forall2 R l m → P l m := @list_forall2_ind

theorem list_forall2_app : ∀ {A : Type u} {B : Type v} {R : A → B → Prop} {a₂ : List A} {b₂ : List B}
    {a₁ : List A} {b₁ : List B}, list_forall2 R a₁ b₁ → list_forall2 R a₂ b₂ → list_forall2 R (a₁ ++
    a₂) (b₁ ++ b₂) := by
  intro A B R l₂ m₂ l₁ m₁ h₁ h₂
  induction h₁ with
  | nil => exact h₂
  | cons h _ ih => exact .cons h ih

theorem list_forall2_length : ∀ {A : Type u} {B : Type v} {R : A → B → Prop} {l m}, list_forall2 R l
    m → l.length = m.length := by
  intro A B R l m h
  induction h <;> simp_all

theorem list_forall2_in_left : ∀ {A : Type u} {B : Type v} {R : A → B → Prop} (x : A) {l m},
    list_forall2 R l m → x ∈ l → ∃ y, y ∈ m ∧ R x y := by
  intro A B R x l m h
  induction h with
  | nil => simp
  | cons hxy ht ih =>
    intro hx
    rcases List.mem_cons.mp hx with rfl | h
    · exact ⟨_, by simp, hxy⟩
    · obtain ⟨y, hy, hy'⟩ := ih h
      exact ⟨y, List.mem_cons_of_mem _ hy, hy'⟩

theorem list_forall2_in_right : ∀ {A : Type u} {B : Type v} {R : A → B → Prop} (y : B) {l m},
    list_forall2 R l m → y ∈ m → ∃ x, x ∈ l ∧ R x y := by
  intro A B R y l m h
  induction h with
  | nil => simp
  | cons hxy ht ih =>
    intro hy
    rcases List.mem_cons.mp hy with rfl | h
    · exact ⟨_, by simp, hxy⟩
    · obtain ⟨x, hx, hx'⟩ := ih h
      exact ⟨x, List.mem_cons_of_mem _ hx, hx'⟩

theorem list_forall2_imply : ∀ {A : Type u} {B : Type v} {R : A → B → Prop} {l m}, list_forall2 R l m
    → ∀ S : A → B → Prop, (∀ x y, x ∈ l → y ∈ m → R x y → S x y) → list_forall2 S l m := by
  intro A B R l m h S
  induction h with
  | nil => exact fun _ ↦ .nil
  | cons hxy ht ih =>
    intro hs
    exact .cons (hs _ _ (by simp) (by simp) hxy)
      (ih (fun x y hx hy ↦ hs x y (List.mem_cons_of_mem _ hx) (List.mem_cons_of_mem _ hy)))

abbrev list_drop {A : Type u} := @List.drop A

theorem list_drop_incl : ∀ {A : Type u} (x : A) (n : Nat) (l : List A),
    x ∈ list_drop n l → x ∈ l := fun _ n l hx ↦ (List.drop_sublist n l).subset hx

theorem list_drop_norepet : ∀ {A : Type u} (n : Nat) {l : List A}, list_norepet l → list_norepet
    (list_drop n l) := @fun _ n l ↦ List.Nodup.sublist (List.drop_sublist n l)

theorem list_map_drop : ∀ {A : Type u} {B : Type v} (f : A → B) (n : Nat) (l : List A), list_drop n
    (l.map f) = (list_drop n l).map f := by intros; simp [list_drop, List.map_drop]

abbrev list_repeat {A : Type u} := @List.replicate A

theorem length_list_repeat : ∀ {A : Type u} (n : Nat) (x : A), (list_repeat n x).length = n := by intros; simp [list_repeat]

theorem in_list_repeat : ∀ {A : Type u} (n : Nat) (x y : A), y ∈ list_repeat n x → y = x := @fun _ _ _ _ h ↦ (List.mem_replicate.mp h).2

def proj_sumbool {P Q : Prop} (a : PSum P Q) := chooseSide a true false

theorem proj_sumbool_true : ∀ {P Q : Prop} (d : PSum P Q), proj_sumbool d = true → P := by rintro P Q (hp | hq) h; exact hp; contradiction

theorem proj_sumbool_is_true : ∀ {P : Prop} (d : PSum P (¬P)), P → proj_sumbool d = true := by rintro P (hp | hn) h; rfl; contradiction

theorem pred_dec_true : ∀ {P : Prop} (d : PSum P (¬P)) {A : Type u} (a b : A), P → chooseSide d a b =
    a := by rintro P (hp | hn) A a b h; rfl; contradiction

theorem pred_dec_false : ∀ {P : Prop} (d : PSum P (¬P)) {A : Type u} (a b : A), ¬P → chooseSide d a b
    = b := by rintro P (hp | hn) A a b h; contradiction; rfl

theorem dec_eq_true : ∀ {A : Type u} (d : EqDecision A) {B : Type v} (x : A) (a b : B), chooseSide (d
    x x) a b = a := @fun _ d _ x a b ↦ pred_dec_true (d x x) a b rfl

theorem dec_eq_false : ∀ {A : Type u} (d : EqDecision A) {B : Type v} {x y : A} (a b : B), x ≠ y →
    chooseSide (d x y) a b = b := @fun _ d _ x y a b ↦ pred_dec_false (d x y) a b

theorem dec_eq_sym : ∀ {A : Type u} (d : EqDecision A) {B : Type v} (x y : A) (a b : B), chooseSide
    (d x y) a b = chooseSide (d y x) a b := by
  intro A d B x y a b
  by_cases h : x = y
  · subst y; rfl
  · rw [dec_eq_false d a b h, dec_eq_false d a b (Ne.symm h)]

abbrev lex_ord {A : Type u} {B : Type v} := @Prod.Lex A B

def lex_ord_left {A : Type u} {B : Type v} (r : A → A → Prop) (s : B → B → Prop)
    (a : A) (b : B) (c : A) (d : B) (h : r a c) : lex_ord r s (a,b) (c,d) := .left b d h

def lex_ord_right {A : Type u} {B : Type v} (r : A → A → Prop) (s : B → B → Prop)
    (a : A) (b d : B) (h : s b d) : lex_ord r s (a,b) (a,d) := .right a h

theorem lex_ord_ind : ∀ {A : Type u} {B : Type v} {r : A → A → Prop} {s : B → B → Prop} (P : A × B →
    A × B → Prop), (∀ a b c d, r a c → P (a,b) (c,d)) → (∀ a b d, s b d → P (a,b) (a,d)) → ∀ {x y},
    lex_ord r s x y → P x y := by
  intro A B r s P hl hr x y h
  cases h with
  | left b d h => exact hl _ b _ d h
  | right a h => exact hr a _ _ h

theorem lex_ord_sind : ∀ {A : Type u} {B : Type v} {r : A → A → Prop} {s : B → B → Prop} (P : A × B →
    A × B → Prop), (∀ a b c d, r a c → P (a,b) (c,d)) → (∀ a b d, s b d → P (a,b) (a,d)) → ∀ {x y},
    lex_ord r s x y → P x y := @lex_ord_ind

theorem wf_lex_ord : ∀ {A : Type u} {B : Type v} {r : A → A → Prop} {s : B → B → Prop}, WellFounded r
    → WellFounded s → WellFounded (lex_ord r s) := @fun _ _ _ _ wr ws ↦ ⟨fun (a,b) ↦ Prod.lexAccessible (wr.apply a) ws.apply b⟩

theorem transitive_lex_ord : ∀ {A : Type u} {B : Type v} {r : A → A → Prop} {s : B → B → Prop}, (∀ x
    y z, r x y → r y z → r x z) → (∀ x y z, s x y → s y z → s x z) → ∀ x y z, lex_ord r s x y →
    lex_ord r s y z → lex_ord r s x z := by
  intro A B r s tr ts x y z h₁ h₂
  cases h₁ <;> cases h₂
  · exact .left _ _ (tr _ _ _ (by assumption) (by assumption))
  · exact .left _ _ (by assumption)
  · exact .left _ _ (by assumption)
  · exact .right _ (ts _ _ _ (by assumption) (by assumption))

inductive nlist (A : Type u) : Type u
  | nbase (x : A)
  | ncons (x : A) (l : nlist A)

abbrev nbase {A : Type u} := @nlist.nbase A
abbrev ncons {A : Type u} := @nlist.ncons A

scoped infixr:65 " :.: " => ncons
scoped notation "[" x " .; " y "]" => ncons x (nbase y)

theorem nlist_ind : ∀ {A : Type u} (P : nlist A → Prop), (∀ a, P (nbase a)) → (∀ a l, P l → P (ncons
    a l)) → ∀ l, P l := @fun _ _ hn hc ↦ nlist.rec hn hc

def nlist_rec {A : Type u} (P : nlist A → Type) (base : ∀ a, P (nbase a))
    (step : ∀ a l, P l → P (ncons a l)) : ∀ l, P l
  | .nbase a => base a
  | .ncons a l => step a l (nlist_rec P base step l)

def nlist_rect {A : Type u} (P : nlist A → Type v) (base : ∀ a, P (nbase a))
    (step : ∀ a l, P l → P (ncons a l)) : ∀ l, P l
  | .nbase a => base a
  | .ncons a l => step a l (nlist_rect P base step l)

theorem nlist_sind : ∀ {A : Type u} (P : nlist A → Prop), (∀ a, P (nbase a)) → (∀ a l, P l → P (ncons
    a l)) → ∀ l, P l := @nlist_ind

def nfirst {A : Type u} : nlist A → A
  | .nbase x | .ncons x _ => x

def nlast {A : Type u} : nlist A → A
  | .nbase x => x
  | .ncons _ xs => nlast xs

def nIn {A : Type u} (x : A) : nlist A → Prop
  | .nbase y => y = x
  | .ncons y ys => y = x ∨ nIn x ys

def nmap {A : Type u} {B : Type v} (f : A → B) : nlist A → nlist B
  | .nbase x => .nbase (f x)
  | .ncons x xs => .ncons (f x) (nmap f xs)

def nfoldl {A : Type u} {B : Type v} (f : A → B → A) : nlist B → A → A
  | .nbase x, acc => f acc x
  | .ncons x xs, acc => nfoldl f xs (f acc x)

def nlen {A : Type u} : nlist A → Nat
  | .nbase _ => 1
  | .ncons _ l => 1 + nlen l

def nnth_error {A : Type u} : nlist A → Nat → Option A
  | l, 0 => some (nfirst l)
  | .nbase _, _+1 => none
  | .ncons _ l, i+1 => nnth_error l i

def nexists {A : Type u} (f : A → Bool) (l : nlist A) := nfoldl (fun acc b ↦ f b || acc) l false

def nall {A : Type u} (f : A → Bool) (l : nlist A) := nfoldl (fun acc b ↦ f b && acc) l true

/-- The source replaces, rather than composes, the continuation at each `ncons`. -/
def napp {A : Type u} (l m : nlist A) : nlist A := loop id l where
  loop (k : nlist A → nlist A) : nlist A → nlist A
    | .nbase x => k (.ncons x m)
    | .ncons x xs => loop (.ncons x) xs

scoped infixr:65 " +.+ " => napp

def nrev {A : Type u} : nlist A → nlist A
  | .nbase x => .nbase x
  | .ncons x xs => go (.nbase x) xs
where
  go (acc : nlist A) : nlist A → nlist A
    | .nbase x => .ncons x acc
    | .ncons x xs => go (.ncons x acc) xs

theorem first_never_fails_nlists : ∀ {A : Type u} (l : nlist A), ∃ x, nfirst l = x := @fun _ l ↦ ⟨nfirst l, rfl⟩

theorem last_never_fails_nlists : ∀ {A : Type u} (l : nlist A), ∃ x, nlast l = x := @fun _ l ↦ ⟨nlast l, rfl⟩

inductive nlist_forall2 {A : Type u} {B : Type v} (R : A → B → Prop) : nlist A → nlist B → Prop
  | base (x y) : R x y → nlist_forall2 R (nbase x) (nbase y)
  | cons (x l y m) : R x y → nlist_forall2 R l m → nlist_forall2 R (ncons x l) (ncons y m)

def nbase_forall2 {A : Type u} {B : Type v} (R : A → B → Prop) := @nlist_forall2.base A B R
def ncons_forall2 {A : Type u} {B : Type v} {R : A → B → Prop} (x : A) {l} (y : B) {m} :=
  nlist_forall2.cons (R := R) x l y m

theorem nlist_forall2_ind : ∀ {A : Type u} {B : Type v} {R : A → B → Prop} (P : nlist A → nlist B →
    Prop), (∀ a b, R a b → P (nbase a) (nbase b)) → (∀ a l b m, R a b → nlist_forall2 R l m → P l m →
    P (ncons a l) (ncons b m)) → ∀ {l m}, nlist_forall2 R l m → P l m := by
  intro A B R P hb hc l m h
  induction h with
  | base x y h => exact hb x y h
  | cons x l y m h ht ih => exact hc x l y m h ht ih

theorem nlist_forall2_sind : ∀ {A : Type u} {B : Type v} {R : A → B → Prop} (P : nlist A → nlist B →
    Prop), (∀ a b, R a b → P (nbase a) (nbase b)) → (∀ a l b m, R a b → nlist_forall2 R l m → P l m →
    P (ncons a l) (ncons b m)) → ∀ {l m}, nlist_forall2 R l m → P l m := @nlist_forall2_ind

theorem nlist_forall2_imply : ∀ {A : Type u} {B : Type v} {R : A → B → Prop} {l m}, nlist_forall2 R l
    m → ∀ S : A → B → Prop, (∀ x y, nIn x l → nIn y m → R x y → S x y) → nlist_forall2 S l m := by
  intro A B R l m h S
  induction h with
  | base x y h => exact fun hs ↦ .base x y (hs x y rfl rfl h)
  | cons x l y m h ht ih =>
    intro hs
    exact .cons x l y m (hs x y (Or.inl rfl) (Or.inl rfl) h)
      (ih (fun a b ha hb ↦ hs a b (Or.inr ha) (Or.inr hb)))

end Vellvm.Numeric.Rocqlib
