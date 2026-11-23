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
import PortChecks.SourceType
import Vellvm.Numeric.Rocqlib

open Vellvm Vellvm.Numeric.Rocqlib
universe u v w

#source_check "src/rocq/Numeric/Rocqlib.v|Vellvm.Numeric.Rocqlib|modusponens"
  modusponens : ∀ (P Q : Prop), P → (P → Q) → Q

#source_check "src/rocq/Numeric/Rocqlib.v|Vellvm.Numeric.Rocqlib|peq_true"
  peq_true : ∀ (A : Type u) (x : Positive) (a b : A), chooseSide (peq x x) a b = a

#source_check "src/rocq/Numeric/Rocqlib.v|Vellvm.Numeric.Rocqlib|peq_false"
  peq_false : ∀ (A : Type u) (x y : Positive) (a b : A), x ≠ y → chooseSide (peq x y) a b = b

#source_check "src/rocq/Numeric/Rocqlib.v|Vellvm.Numeric.Rocqlib|Plt_ne"
  Plt_ne : ∀ x y, Plt x y → x ≠ y

#source_check "src/rocq/Numeric/Rocqlib.v|Vellvm.Numeric.Rocqlib|Plt_trans"
  Plt_trans : ∀ x y z, Plt x y → Plt y z → Plt x z

#source_check "src/rocq/Numeric/Rocqlib.v|Vellvm.Numeric.Rocqlib|Plt_succ"
  Plt_succ : ∀ x, Plt x (posSucc x)

#source_check "src/rocq/Numeric/Rocqlib.v|Vellvm.Numeric.Rocqlib|Plt_trans_succ"
  Plt_trans_succ : ∀ x y, Plt x y → Plt x (posSucc y)

#source_check "src/rocq/Numeric/Rocqlib.v|Vellvm.Numeric.Rocqlib|Plt_succ_inv"
  Plt_succ_inv : ∀ x y, Plt x (posSucc y) → Plt x y ∨ x = y

#source_check "src/rocq/Numeric/Rocqlib.v|Vellvm.Numeric.Rocqlib|Ple_refl"
  Ple_refl : ∀ x, Ple x x

#source_check "src/rocq/Numeric/Rocqlib.v|Vellvm.Numeric.Rocqlib|Ple_trans"
  Ple_trans : ∀ x y z, Ple x y → Ple y z → Ple x z

#source_check "src/rocq/Numeric/Rocqlib.v|Vellvm.Numeric.Rocqlib|Plt_Ple"
  Plt_Ple : ∀ x y, Plt x y → Ple x y

#source_check "src/rocq/Numeric/Rocqlib.v|Vellvm.Numeric.Rocqlib|Ple_succ"
  Ple_succ : ∀ x, Ple x (posSucc x)

#source_check "src/rocq/Numeric/Rocqlib.v|Vellvm.Numeric.Rocqlib|Plt_Ple_trans"
  Plt_Ple_trans : ∀ x y z, Plt x y → Ple y z → Plt x z

#source_check "src/rocq/Numeric/Rocqlib.v|Vellvm.Numeric.Rocqlib|Plt_strict"
  Plt_strict : ∀ x, ¬ Plt x x

#source_check "src/rocq/Numeric/Rocqlib.v|Vellvm.Numeric.Rocqlib|Plt_wf"
  Plt_wf : WellFounded Plt

#source_check "src/rocq/Numeric/Rocqlib.v|Vellvm.Numeric.Rocqlib|Ppred_Plt"
  Ppred_Plt : ∀ x, x ≠ posOne → Plt (posPred x) x

#source_check "src/rocq/Numeric/Rocqlib.v|Vellvm.Numeric.Rocqlib|unroll_positive_rec"
  unroll_positive_rec : ∀ (A : Type u) (v : A) (f : Positive → A → A) (x : Positive), positive_rec A
    v f x = chooseSide (peq x posOne) v (f (posPred x) (positive_rec A v f (posPred x)))

#source_check "src/rocq/Numeric/Rocqlib.v|Vellvm.Numeric.Rocqlib|positive_rec_base"
  positive_rec_base : ∀ (A : Type u) (v : A) (f : Positive → A → A), positive_rec A v f posOne = v

#source_check "src/rocq/Numeric/Rocqlib.v|Vellvm.Numeric.Rocqlib|positive_rec_succ"
  positive_rec_succ : ∀ (A : Type u) (v : A) (f : Positive → A → A) (x : Positive), positive_rec A v
    f (posSucc x) = f x (positive_rec A v f x)

#source_check "src/rocq/Numeric/Rocqlib.v|Vellvm.Numeric.Rocqlib|positive_Peano_ind"
  positive_Peano_ind : ∀ (P : Positive → Prop), P posOne → (∀ x, P x → P (posSucc x)) → ∀ x, P x

#source_check "src/rocq/Numeric/Rocqlib.v|Vellvm.Numeric.Rocqlib|zeq_true"
  zeq_true : ∀ (A : Type u) (x : Int) (a b : A), chooseSide (zeq x x) a b = a

#source_check "src/rocq/Numeric/Rocqlib.v|Vellvm.Numeric.Rocqlib|zeq_false"
  zeq_false : ∀ (A : Type u) (x y : Int) (a b : A), x ≠ y → chooseSide (zeq x y) a b = b

#source_check "src/rocq/Numeric/Rocqlib.v|Vellvm.Numeric.Rocqlib|zlt_true"
  zlt_true : ∀ (A : Type u) (x y : Int) (a b : A), x < y → chooseSide (zlt x y) a b = a

#source_check "src/rocq/Numeric/Rocqlib.v|Vellvm.Numeric.Rocqlib|zlt_false"
  zlt_false : ∀ (A : Type u) (x y : Int) (a b : A), x ≥ y → chooseSide (zlt x y) a b = b

#source_check "src/rocq/Numeric/Rocqlib.v|Vellvm.Numeric.Rocqlib|zle_true"
  zle_true : ∀ (A : Type u) (x y : Int) (a b : A), x ≤ y → chooseSide (zle x y) a b = a

#source_check "src/rocq/Numeric/Rocqlib.v|Vellvm.Numeric.Rocqlib|zle_false"
  zle_false : ∀ (A : Type u) (x y : Int) (a b : A), x > y → chooseSide (zle x y) a b = b

#source_check "src/rocq/Numeric/Rocqlib.v|Vellvm.Numeric.Rocqlib|two_power_nat_O"
  two_power_nat_O : two_power_nat 0 = 1

#source_check "src/rocq/Numeric/Rocqlib.v|Vellvm.Numeric.Rocqlib|two_power_nat_pos"
  two_power_nat_pos : ∀ n, 0 < two_power_nat n

#source_check "src/rocq/Numeric/Rocqlib.v|Vellvm.Numeric.Rocqlib|two_power_nat_two_p"
  two_power_nat_two_p : ∀ (n : Nat), two_power_nat n = two_p (Int.ofNat n)

#source_check "src/rocq/Numeric/Rocqlib.v|Vellvm.Numeric.Rocqlib|two_power_pos_two_p"
  two_power_pos_two_p : ∀ (x : Positive), two_power_pos x = two_p (Int.ofNat x.val)

#source_check "src/rocq/Numeric/Rocqlib.v|Vellvm.Numeric.Rocqlib|two_p_monotone"
  two_p_monotone : ∀ x y, 0 ≤ x ∧ x ≤ y → two_p x ≤ two_p y

#source_check "src/rocq/Numeric/Rocqlib.v|Vellvm.Numeric.Rocqlib|two_p_monotone_strict"
  two_p_monotone_strict : ∀ x y, 0 ≤ x ∧ x < y → two_p x < two_p y

#source_check "src/rocq/Numeric/Rocqlib.v|Vellvm.Numeric.Rocqlib|two_p_strict"
  two_p_strict : ∀ x, x ≥ 0 → x < two_p x

#source_check "src/rocq/Numeric/Rocqlib.v|Vellvm.Numeric.Rocqlib|two_p_strict_2"
  two_p_strict_2 : ∀ x, x ≥ 0 → 2 * x - 1 < two_p x

#source_check "src/rocq/Numeric/Rocqlib.v|Vellvm.Numeric.Rocqlib|Zmin_spec"
  Zmin_spec : ∀ x y : Int, min x y = chooseSide (zlt x y) x y

#source_check "src/rocq/Numeric/Rocqlib.v|Vellvm.Numeric.Rocqlib|Zmax_spec"
  Zmax_spec : ∀ x y : Int, max x y = chooseSide (zlt y x) x y

#source_check "src/rocq/Numeric/Rocqlib.v|Vellvm.Numeric.Rocqlib|Zmax_bound_l"
  Zmax_bound_l : ∀ x y z : Int, x ≤ y → x ≤ max y z

#source_check "src/rocq/Numeric/Rocqlib.v|Vellvm.Numeric.Rocqlib|Zmax_bound_r"
  Zmax_bound_r : ∀ x y z : Int, x ≤ z → x ≤ max y z

#source_check "src/rocq/Numeric/Rocqlib.v|Vellvm.Numeric.Rocqlib|Zdiv_small"
  Zdiv_small : ∀ x y : Int, 0 ≤ x ∧ x < y → x.fdiv y = 0

#source_check "src/rocq/Numeric/Rocqlib.v|Vellvm.Numeric.Rocqlib|Zmod_small"
  Zmod_small : ∀ x y : Int, 0 ≤ x ∧ x < y → x.fmod y = x

#source_check "src/rocq/Numeric/Rocqlib.v|Vellvm.Numeric.Rocqlib|Zmod_unique"
  Zmod_unique : ∀ x y a b : Int, x = a * y + b → 0 ≤ b ∧ b < y → x.fmod y = b

#source_check "src/rocq/Numeric/Rocqlib.v|Vellvm.Numeric.Rocqlib|Zdiv_unique"
  Zdiv_unique : ∀ x y a b : Int, x = a * y + b → 0 ≤ b ∧ b < y → x.fdiv y = a

#source_check "src/rocq/Numeric/Rocqlib.v|Vellvm.Numeric.Rocqlib|Zdiv_Zdiv"
  Zdiv_Zdiv : ∀ a b c : Int, 0 < b → 0 < c → (a.fdiv b).fdiv c = a.fdiv (b * c)

#source_check "src/rocq/Numeric/Rocqlib.v|Vellvm.Numeric.Rocqlib|Zmult_le_compat_l_neg"
  Zmult_le_compat_l_neg : ∀ n m p : Int, n ≥ m → p ≤ 0 → p * n ≤ p * m

#source_check "src/rocq/Numeric/Rocqlib.v|Vellvm.Numeric.Rocqlib|Zdiv_interval_1"
  Zdiv_interval_1 : ∀ lo hi a b : Int, lo ≤ 0 → 0 < hi → 0 < b → lo * b ≤ a ∧ a < hi * b → lo ≤
    a.fdiv b ∧ a.fdiv b < hi

#source_check "src/rocq/Numeric/Rocqlib.v|Vellvm.Numeric.Rocqlib|Zdiv_interval_2"
  Zdiv_interval_2 : ∀ lo hi a b : Int, lo ≤ a ∧ a ≤ hi → lo ≤ 0 → 0 ≤ hi → 0 < b → lo ≤ a.fdiv b ∧
    a.fdiv b ≤ hi

#source_check "src/rocq/Numeric/Rocqlib.v|Vellvm.Numeric.Rocqlib|Zmod_recombine"
  Zmod_recombine : ∀ x a b : Int, 0 < a → 0 < b → x.fmod (a * b) = (x.fdiv b).fmod a * b + x.fmod b

#source_check "src/rocq/Numeric/Rocqlib.v|Vellvm.Numeric.Rocqlib|Zdivides_trans"
  Zdivides_trans : ∀ x y z : Int, x ∣ y → y ∣ z → x ∣ z

#source_check "src/rocq/Numeric/Rocqlib.v|Vellvm.Numeric.Rocqlib|Zdivide_interval"
  Zdivide_interval : ∀ a b c : Int, 0 < c → 0 ≤ a ∧ a < b → c ∣ a → c ∣ b → 0 ≤ a ∧ a ≤ b - c

#source_check "src/rocq/Numeric/Rocqlib.v|Vellvm.Numeric.Rocqlib|nat_of_Z_of_nat"
  nat_of_Z_of_nat : ∀ n, nat_of_Z (Int.ofNat n) = n

#source_check "src/rocq/Numeric/Rocqlib.v|Vellvm.Numeric.Rocqlib|nat_of_Z_max"
  nat_of_Z_max : ∀ z, Int.ofNat (nat_of_Z z) = max z 0

#source_check "src/rocq/Numeric/Rocqlib.v|Vellvm.Numeric.Rocqlib|nat_of_Z_eq"
  nat_of_Z_eq : ∀ z, z ≥ 0 → Int.ofNat (nat_of_Z z) = z

#source_check "src/rocq/Numeric/Rocqlib.v|Vellvm.Numeric.Rocqlib|nat_of_Z_neg"
  nat_of_Z_neg : ∀ z, z ≤ 0 → nat_of_Z z = 0

#source_check "src/rocq/Numeric/Rocqlib.v|Vellvm.Numeric.Rocqlib|nat_of_Z_plus"
  nat_of_Z_plus : ∀ p q, p ≥ 0 → q ≥ 0 → nat_of_Z (p + q) = nat_of_Z p + nat_of_Z q

#source_check "src/rocq/Numeric/Rocqlib.v|Vellvm.Numeric.Rocqlib|align_le"
  align_le : ∀ x y, 0 < y → x ≤ align x y

#source_check "src/rocq/Numeric/Rocqlib.v|Vellvm.Numeric.Rocqlib|align_divides"
  align_divides : ∀ x y, 0 < y → y ∣ align x y

#source_check "src/rocq/Numeric/Rocqlib.v|Vellvm.Numeric.Rocqlib|option_rel_ind"
  option_rel_ind : ∀ {A : Type u} {B : Type v} {R : A → B → Prop} (P : Option A → Option B → Prop),
    P none none → (∀ x y, R x y → P (some x) (some y)) → ∀ {a b}, option_rel R a b → P a b

#source_check "src/rocq/Numeric/Rocqlib.v|Vellvm.Numeric.Rocqlib|option_rel_sind"
  option_rel_sind : ∀ {A : Type u} {B : Type v} {R : A → B → Prop} (P : Option A → Option B → Prop),
    P none none → (∀ x y, R x y → P (some x) (some y)) → ∀ {a b}, option_rel R a b → P a b

#source_check "src/rocq/Numeric/Rocqlib.v|Vellvm.Numeric.Rocqlib|nth_error_in"
  nth_error_in : ∀ {A : Type u} (n : Nat) (l : List A) {x}, l[n]? = some x → x ∈ l

#source_check "src/rocq/Numeric/Rocqlib.v|Vellvm.Numeric.Rocqlib|nth_error_nil"
  nth_error_nil : ∀ (A : Type u) (n : Nat), ([] : List A)[n]? = none

#source_check "src/rocq/Numeric/Rocqlib.v|Vellvm.Numeric.Rocqlib|list_length_z_aux_shift"
  list_length_z_aux_shift : ∀ {A : Type u} (l : List A) (n m : Int), list_length_z_aux l n =
    list_length_z_aux l m + (n - m)

#source_check "src/rocq/Numeric/Rocqlib.v|Vellvm.Numeric.Rocqlib|list_length_z_cons"
  list_length_z_cons : ∀ {A : Type u} (x : A) (l : List A), list_length_z (x :: l) = list_length_z l
    + 1

#source_check "src/rocq/Numeric/Rocqlib.v|Vellvm.Numeric.Rocqlib|list_length_z_pos"
  list_length_z_pos : ∀ {A : Type u} (l : List A), list_length_z l ≥ 0

#source_check "src/rocq/Numeric/Rocqlib.v|Vellvm.Numeric.Rocqlib|list_length_z_map"
  list_length_z_map : ∀ {A : Type u} {B : Type v} (f : A → B) (l : List A), list_length_z (l.map f)
    = list_length_z l

#source_check "src/rocq/Numeric/Rocqlib.v|Vellvm.Numeric.Rocqlib|list_nth_z_in"
  list_nth_z_in : ∀ {A : Type u} (l : List A) (n : Int) {x}, list_nth_z l n = some x → x ∈ l

#source_check "src/rocq/Numeric/Rocqlib.v|Vellvm.Numeric.Rocqlib|list_nth_z_map"
  list_nth_z_map : ∀ {A : Type u} {B : Type v} (f : A → B) (l : List A) (n : Int), list_nth_z (l.map
    f) n = option_map f (list_nth_z l n)

#source_check "src/rocq/Numeric/Rocqlib.v|Vellvm.Numeric.Rocqlib|list_nth_z_range"
  list_nth_z_range : ∀ {A : Type u} (l : List A) (n : Int) {x}, list_nth_z l n = some x → 0 ≤ n ∧ n
    < list_length_z l

#source_check "src/rocq/Numeric/Rocqlib.v|Vellvm.Numeric.Rocqlib|incl_cons_inv"
  incl_cons_inv : ∀ {A : Type u} {a : A} {b c : List A}, a :: b ⊆ c → b ⊆ c

#source_check "src/rocq/Numeric/Rocqlib.v|Vellvm.Numeric.Rocqlib|incl_app_inv_l"
  incl_app_inv_l : ∀ {A : Type u} (l₁ l₂ : List A) {m : List A}, l₁ ++ l₂ ⊆ m → l₁ ⊆ m

#source_check "src/rocq/Numeric/Rocqlib.v|Vellvm.Numeric.Rocqlib|incl_app_inv_r"
  incl_app_inv_r : ∀ {A : Type u} (l₁ l₂ : List A) {m : List A}, l₁ ++ l₂ ⊆ m → l₂ ⊆ m

#source_check "src/rocq/Numeric/Rocqlib.v|Vellvm.Numeric.Rocqlib|incl_same_head"
  incl_same_head : ∀ {A : Type u} {x : A} {l₁ l₂ : List A}, l₁ ⊆ l₂ → x :: l₁ ⊆ x :: l₂

#source_check "src/rocq/Numeric/Rocqlib.v|Vellvm.Numeric.Rocqlib|list_map_exten"
  list_map_exten : ∀ {A : Type u} {B : Type v} (f g : A → B) (l : List A), (∀ x ∈ l, f x = g x) →
    l.map g = l.map f

#source_check "src/rocq/Numeric/Rocqlib.v|Vellvm.Numeric.Rocqlib|list_map_compose"
  list_map_compose : ∀ {A : Type u} {B : Type v} {C : Type w} (f : A → B) (g : B → C) (l : List A),
    (l.map f).map g = l.map (fun x ↦ g (f x))

#source_check "src/rocq/Numeric/Rocqlib.v|Vellvm.Numeric.Rocqlib|list_map_identity"
  list_map_identity : ∀ {A : Type u} (l : List A), l.map (fun x ↦ x) = l

#source_check "src/rocq/Numeric/Rocqlib.v|Vellvm.Numeric.Rocqlib|list_map_nth"
  list_map_nth : ∀ {A : Type u} {B : Type v} (f : A → B) (l : List A) (n : Nat), (l.map f)[n]? =
    option_map f l[n]?

#source_check "src/rocq/Numeric/Rocqlib.v|Vellvm.Numeric.Rocqlib|list_length_map"
  list_length_map : ∀ {A : Type u} {B : Type v} (f : A → B) (l : List A), (l.map f).length =
    l.length

#source_check "src/rocq/Numeric/Rocqlib.v|Vellvm.Numeric.Rocqlib|list_in_map_inv"
  list_in_map_inv : ∀ {A : Type u} {B : Type v} (f : A → B) (l : List A) (y : B), y ∈ l.map f → ∃ x,
    y = f x ∧ x ∈ l

#source_check "src/rocq/Numeric/Rocqlib.v|Vellvm.Numeric.Rocqlib|list_append_map"
  list_append_map : ∀ {A : Type u} {B : Type v} (f : A → B) (l₁ l₂ : List A), (l₁ ++ l₂).map f =
    l₁.map f ++ l₂.map f

#source_check "src/rocq/Numeric/Rocqlib.v|Vellvm.Numeric.Rocqlib|list_append_map_inv"
  list_append_map_inv : ∀ {A : Type u} {B : Type v} (f : A → B) (m₁ m₂ : List B) (l : List A), l.map
    f = m₁ ++ m₂ → ∃ l₁ l₂, l₁.map f = m₁ ∧ l₂.map f = m₂ ∧ l = l₁ ++ l₂

#source_check "src/rocq/Numeric/Rocqlib.v|Vellvm.Numeric.Rocqlib|list_fold_left_app"
  list_fold_left_app : ∀ {A : Type u} {B : Type v} (f : A → B → B) (l₁ l₂ : List A) (acc : B),
    list_fold_left f acc (l₁ ++ l₂) = list_fold_left f (list_fold_left f acc l₁) l₂

#source_check "src/rocq/Numeric/Rocqlib.v|Vellvm.Numeric.Rocqlib|list_fold_right_eq"
  list_fold_right_eq : ∀ {A : Type u} {B : Type v} (f : A → B → B) (l : List A) (base : B),
    list_fold_right f l base = (match l with | [] => base | x :: xs => f x (list_fold_right f xs
    base))

#source_check "src/rocq/Numeric/Rocqlib.v|Vellvm.Numeric.Rocqlib|list_fold_right_spec"
  list_fold_right_spec : ∀ {A : Type u} {B : Type v} (f : A → B → B) (l : List A) (base : B),
    list_fold_right f l base = l.foldr f base

#source_check "src/rocq/Numeric/Rocqlib.v|Vellvm.Numeric.Rocqlib|in_cns"
  in_cns : ∀ {A : Type u} (x y : A) (l : List A), x ∈ y :: l ↔ y = x ∨ x ∈ l

#source_check "src/rocq/Numeric/Rocqlib.v|Vellvm.Numeric.Rocqlib|in_app"
  in_app : ∀ {A : Type u} (x : A) (l₁ l₂ : List A), x ∈ l₁ ++ l₂ ↔ x ∈ l₁ ∨ x ∈ l₂

#source_check "src/rocq/Numeric/Rocqlib.v|Vellvm.Numeric.Rocqlib|list_in_insert"
  list_in_insert : ∀ {A : Type u} (x : A) (l₁ l₂ : List A) (y : A), x ∈ l₁ ++ l₂ → x ∈ l₁ ++ y :: l₂

#source_check "src/rocq/Numeric/Rocqlib.v|Vellvm.Numeric.Rocqlib|list_disjoint_cons_l"
  list_disjoint_cons_l : ∀ {A : Type u} {a : A} {l₁ l₂ : List A}, list_disjoint l₁ l₂ → a ∉ l₂ →
    list_disjoint (a :: l₁) l₂

#source_check "src/rocq/Numeric/Rocqlib.v|Vellvm.Numeric.Rocqlib|list_disjoint_cons_r"
  list_disjoint_cons_r : ∀ {A : Type u} {a : A} {l₁ l₂ : List A}, list_disjoint l₁ l₂ → a ∉ l₁ →
    list_disjoint l₁ (a :: l₂)

#source_check "src/rocq/Numeric/Rocqlib.v|Vellvm.Numeric.Rocqlib|list_disjoint_cons_left"
  list_disjoint_cons_left : ∀ {A : Type u} {a : A} {l₁ l₂ : List A}, list_disjoint (a :: l₁) l₂ →
    list_disjoint l₁ l₂

#source_check "src/rocq/Numeric/Rocqlib.v|Vellvm.Numeric.Rocqlib|list_disjoint_cons_right"
  list_disjoint_cons_right : ∀ {A : Type u} {a : A} {l₁ l₂ : List A}, list_disjoint l₁ (a :: l₂) →
    list_disjoint l₁ l₂

#source_check "src/rocq/Numeric/Rocqlib.v|Vellvm.Numeric.Rocqlib|list_disjoint_notin"
  list_disjoint_notin : ∀ {A : Type u} {l₁ l₂ : List A} (a : A), list_disjoint l₁ l₂ → a ∈ l₁ → a ∉
    l₂

#source_check "src/rocq/Numeric/Rocqlib.v|Vellvm.Numeric.Rocqlib|list_disjoint_sym"
  list_disjoint_sym : ∀ {A : Type u} {l₁ l₂ : List A}, list_disjoint l₁ l₂ → list_disjoint l₂ l₁

#source_check "src/rocq/Numeric/Rocqlib.v|Vellvm.Numeric.Rocqlib|list_norepet_ind"
  list_norepet_ind : ∀ {A : Type u} (P : List A → Prop), P [] → (∀ x xs, x ∉ xs → list_norepet xs →
    P xs → P (x :: xs)) → ∀ {l}, list_norepet l → P l

#source_check "src/rocq/Numeric/Rocqlib.v|Vellvm.Numeric.Rocqlib|list_norepet_sind"
  list_norepet_sind : ∀ {A : Type u} (P : List A → Prop), P [] → (∀ x xs, x ∉ xs → list_norepet xs →
    P xs → P (x :: xs)) → ∀ {l}, list_norepet l → P l

#source_check "src/rocq/Numeric/Rocqlib.v|Vellvm.Numeric.Rocqlib|list_map_norepet"
  list_map_norepet : ∀ {A : Type u} {B : Type v} (f : A → B) {l : List A}, list_norepet l → (∀ x y,
    x ∈ l → y ∈ l → x ≠ y → f x ≠ f y) → list_norepet (l.map f)

#source_check "src/rocq/Numeric/Rocqlib.v|Vellvm.Numeric.Rocqlib|list_norepet_append_commut"
  list_norepet_append_commut : ∀ {A : Type u} (a b : List A), list_norepet (a ++ b) → list_norepet
    (b ++ a)

#source_check "src/rocq/Numeric/Rocqlib.v|Vellvm.Numeric.Rocqlib|list_norepet_app"
  list_norepet_app : ∀ {A : Type u} (l₁ l₂ : List A), list_norepet (l₁ ++ l₂) ↔ list_norepet l₁ ∧
    list_norepet l₂ ∧ list_disjoint l₁ l₂

#source_check "src/rocq/Numeric/Rocqlib.v|Vellvm.Numeric.Rocqlib|list_norepet_append"
  list_norepet_append : ∀ {A : Type u} {l₁ l₂ : List A}, list_norepet l₁ → list_norepet l₂ →
    list_disjoint l₁ l₂ → list_norepet (l₁ ++ l₂)

#source_check "src/rocq/Numeric/Rocqlib.v|Vellvm.Numeric.Rocqlib|list_norepet_append_right"
  list_norepet_append_right : ∀ {A : Type u} (l₁ l₂ : List A), list_norepet (l₁ ++ l₂) →
    list_norepet l₂

#source_check "src/rocq/Numeric/Rocqlib.v|Vellvm.Numeric.Rocqlib|list_norepet_append_left"
  list_norepet_append_left : ∀ {A : Type u} (l₁ l₂ : List A), list_norepet (l₁ ++ l₂) → list_norepet
    l₁

#source_check "src/rocq/Numeric/Rocqlib.v|Vellvm.Numeric.Rocqlib|is_tail_ind"
  is_tail_ind : ∀ {A : Type u} (P : List A → List A → Prop), (∀ c, P c c) → (∀ i c₁ c₂, is_tail c₁
    c₂ → P c₁ c₂ → P c₁ (i :: c₂)) → ∀ {l m}, is_tail l m → P l m

#source_check "src/rocq/Numeric/Rocqlib.v|Vellvm.Numeric.Rocqlib|is_tail_sind"
  is_tail_sind : ∀ {A : Type u} (P : List A → List A → Prop), (∀ c, P c c) → (∀ i c₁ c₂, is_tail c₁
    c₂ → P c₁ c₂ → P c₁ (i :: c₂)) → ∀ {l m}, is_tail l m → P l m

#source_check "src/rocq/Numeric/Rocqlib.v|Vellvm.Numeric.Rocqlib|is_tail_in"
  is_tail_in : ∀ {A : Type u} {i : A} {c₁ c₂ : List A}, is_tail (i :: c₁) c₂ → i ∈ c₂

#source_check "src/rocq/Numeric/Rocqlib.v|Vellvm.Numeric.Rocqlib|is_tail_cons_left"
  is_tail_cons_left : ∀ {A : Type u} {i : A} {c₁ c₂ : List A}, is_tail (i :: c₁) c₂ → is_tail c₁ c₂

#source_check "src/rocq/Numeric/Rocqlib.v|Vellvm.Numeric.Rocqlib|is_tail_incl"
  is_tail_incl : ∀ {A : Type u} {l₁ l₂ : List A}, is_tail l₁ l₂ → l₁ ⊆ l₂

#source_check "src/rocq/Numeric/Rocqlib.v|Vellvm.Numeric.Rocqlib|is_tail_trans"
  is_tail_trans : ∀ {A : Type u} {l₁ l₂ : List A}, is_tail l₁ l₂ → ∀ {l₃}, is_tail l₂ l₃ → is_tail
    l₁ l₃

#source_check "src/rocq/Numeric/Rocqlib.v|Vellvm.Numeric.Rocqlib|list_forall2_ind"
  list_forall2_ind : ∀ {A : Type u} {B : Type v} {R : A → B → Prop} (P : List A → List B → Prop), P
    [] [] → (∀ a l b m, R a b → list_forall2 R l m → P l m → P (a :: l) (b :: m)) → ∀ {l m},
    list_forall2 R l m → P l m

#source_check "src/rocq/Numeric/Rocqlib.v|Vellvm.Numeric.Rocqlib|list_forall2_sind"
  list_forall2_sind : ∀ {A : Type u} {B : Type v} {R : A → B → Prop} (P : List A → List B → Prop), P
    [] [] → (∀ a l b m, R a b → list_forall2 R l m → P l m → P (a :: l) (b :: m)) → ∀ {l m},
    list_forall2 R l m → P l m

#source_check "src/rocq/Numeric/Rocqlib.v|Vellvm.Numeric.Rocqlib|list_forall2_app"
  list_forall2_app : ∀ {A : Type u} {B : Type v} {R : A → B → Prop} {a₂ : List A} {b₂ : List B} {a₁
    : List A} {b₁ : List B}, list_forall2 R a₁ b₁ → list_forall2 R a₂ b₂ → list_forall2 R (a₁ ++ a₂)
    (b₁ ++ b₂)

#source_check "src/rocq/Numeric/Rocqlib.v|Vellvm.Numeric.Rocqlib|list_forall2_length"
  list_forall2_length : ∀ {A : Type u} {B : Type v} {R : A → B → Prop} {l m}, list_forall2 R l m →
    l.length = m.length

#source_check "src/rocq/Numeric/Rocqlib.v|Vellvm.Numeric.Rocqlib|list_forall2_in_left"
  list_forall2_in_left : ∀ {A : Type u} {B : Type v} {R : A → B → Prop} (x : A) {l m}, list_forall2
    R l m → x ∈ l → ∃ y, y ∈ m ∧ R x y

#source_check "src/rocq/Numeric/Rocqlib.v|Vellvm.Numeric.Rocqlib|list_forall2_in_right"
  list_forall2_in_right : ∀ {A : Type u} {B : Type v} {R : A → B → Prop} (y : B) {l m}, list_forall2
    R l m → y ∈ m → ∃ x, x ∈ l ∧ R x y

#source_check "src/rocq/Numeric/Rocqlib.v|Vellvm.Numeric.Rocqlib|list_forall2_imply"
  list_forall2_imply : ∀ {A : Type u} {B : Type v} {R : A → B → Prop} {l m}, list_forall2 R l m → ∀
    S : A → B → Prop, (∀ x y, x ∈ l → y ∈ m → R x y → S x y) → list_forall2 S l m

#source_check "src/rocq/Numeric/Rocqlib.v|Vellvm.Numeric.Rocqlib|list_drop_incl"
  list_drop_incl : ∀ {A : Type u} (x : A) (n : Nat) (l : List A), x ∈ list_drop n l → x ∈ l

#source_check "src/rocq/Numeric/Rocqlib.v|Vellvm.Numeric.Rocqlib|list_drop_norepet"
  list_drop_norepet : ∀ {A : Type u} (n : Nat) {l : List A}, list_norepet l → list_norepet
    (list_drop n l)

#source_check "src/rocq/Numeric/Rocqlib.v|Vellvm.Numeric.Rocqlib|list_map_drop"
  list_map_drop : ∀ {A : Type u} {B : Type v} (f : A → B) (n : Nat) (l : List A), list_drop n (l.map
    f) = (list_drop n l).map f

#source_check "src/rocq/Numeric/Rocqlib.v|Vellvm.Numeric.Rocqlib|length_list_repeat"
  length_list_repeat : ∀ {A : Type u} (n : Nat) (x : A), (list_repeat n x).length = n

#source_check "src/rocq/Numeric/Rocqlib.v|Vellvm.Numeric.Rocqlib|in_list_repeat"
  in_list_repeat : ∀ {A : Type u} (n : Nat) (x y : A), y ∈ list_repeat n x → y = x

#source_check "src/rocq/Numeric/Rocqlib.v|Vellvm.Numeric.Rocqlib|proj_sumbool_true"
  proj_sumbool_true : ∀ {P Q : Prop} (d : PSum P Q), proj_sumbool d = true → P

#source_check "src/rocq/Numeric/Rocqlib.v|Vellvm.Numeric.Rocqlib|proj_sumbool_is_true"
  proj_sumbool_is_true : ∀ {P : Prop} (d : PSum P (¬P)), P → proj_sumbool d = true

#source_check "src/rocq/Numeric/Rocqlib.v|Vellvm.Numeric.Rocqlib|dec_eq_true"
  dec_eq_true : ∀ {A : Type u} (d : EqDecision A) {B : Type v} (x : A) (a b : B), chooseSide (d x x)
    a b = a

#source_check "src/rocq/Numeric/Rocqlib.v|Vellvm.Numeric.Rocqlib|dec_eq_false"
  dec_eq_false : ∀ {A : Type u} (d : EqDecision A) {B : Type v} {x y : A} (a b : B), x ≠ y →
    chooseSide (d x y) a b = b

#source_check "src/rocq/Numeric/Rocqlib.v|Vellvm.Numeric.Rocqlib|dec_eq_sym"
  dec_eq_sym : ∀ {A : Type u} (d : EqDecision A) {B : Type v} (x y : A) (a b : B), chooseSide (d x
    y) a b = chooseSide (d y x) a b

#source_check "src/rocq/Numeric/Rocqlib.v|Vellvm.Numeric.Rocqlib|pred_dec_true"
  pred_dec_true : ∀ {P : Prop} (d : PSum P (¬P)) {A : Type u} (a b : A), P → chooseSide d a b = a

#source_check "src/rocq/Numeric/Rocqlib.v|Vellvm.Numeric.Rocqlib|pred_dec_false"
  pred_dec_false : ∀ {P : Prop} (d : PSum P (¬P)) {A : Type u} (a b : A), ¬P → chooseSide d a b = b

#source_check "src/rocq/Numeric/Rocqlib.v|Vellvm.Numeric.Rocqlib|lex_ord_ind"
  lex_ord_ind : ∀ {A : Type u} {B : Type v} {r : A → A → Prop} {s : B → B → Prop} (P : A × B → A × B
    → Prop), (∀ a b c d, r a c → P (a,b) (c,d)) → (∀ a b d, s b d → P (a,b) (a,d)) → ∀ {x y},
    lex_ord r s x y → P x y

#source_check "src/rocq/Numeric/Rocqlib.v|Vellvm.Numeric.Rocqlib|lex_ord_sind"
  lex_ord_sind : ∀ {A : Type u} {B : Type v} {r : A → A → Prop} {s : B → B → Prop} (P : A × B → A ×
    B → Prop), (∀ a b c d, r a c → P (a,b) (c,d)) → (∀ a b d, s b d → P (a,b) (a,d)) → ∀ {x y},
    lex_ord r s x y → P x y

#source_check "src/rocq/Numeric/Rocqlib.v|Vellvm.Numeric.Rocqlib|wf_lex_ord"
  wf_lex_ord : ∀ {A : Type u} {B : Type v} {r : A → A → Prop} {s : B → B → Prop}, WellFounded r →
    WellFounded s → WellFounded (lex_ord r s)

#source_check "src/rocq/Numeric/Rocqlib.v|Vellvm.Numeric.Rocqlib|transitive_lex_ord"
  transitive_lex_ord : ∀ {A : Type u} {B : Type v} {r : A → A → Prop} {s : B → B → Prop}, (∀ x y z,
    r x y → r y z → r x z) → (∀ x y z, s x y → s y z → s x z) → ∀ x y z, lex_ord r s x y → lex_ord r
    s y z → lex_ord r s x z

#source_check "src/rocq/Numeric/Rocqlib.v|Vellvm.Numeric.Rocqlib|nlist_ind"
  nlist_ind : ∀ {A : Type u} (P : nlist A → Prop), (∀ a, P (nbase a)) → (∀ a l, P l → P (ncons a l))
    → ∀ l, P l

#source_check "src/rocq/Numeric/Rocqlib.v|Vellvm.Numeric.Rocqlib|nlist_sind"
  nlist_sind : ∀ {A : Type u} (P : nlist A → Prop), (∀ a, P (nbase a)) → (∀ a l, P l → P (ncons a
    l)) → ∀ l, P l

#source_check "src/rocq/Numeric/Rocqlib.v|Vellvm.Numeric.Rocqlib|first_never_fails_nlists"
  first_never_fails_nlists : ∀ {A : Type u} (l : nlist A), ∃ x, nfirst l = x

#source_check "src/rocq/Numeric/Rocqlib.v|Vellvm.Numeric.Rocqlib|last_never_fails_nlists"
  last_never_fails_nlists : ∀ {A : Type u} (l : nlist A), ∃ x, nlast l = x

#source_check "src/rocq/Numeric/Rocqlib.v|Vellvm.Numeric.Rocqlib|nlist_forall2_ind"
  nlist_forall2_ind : ∀ {A : Type u} {B : Type v} {R : A → B → Prop} (P : nlist A → nlist B → Prop),
    (∀ a b, R a b → P (nbase a) (nbase b)) → (∀ a l b m, R a b → nlist_forall2 R l m → P l m → P
    (ncons a l) (ncons b m)) → ∀ {l m}, nlist_forall2 R l m → P l m

#source_check "src/rocq/Numeric/Rocqlib.v|Vellvm.Numeric.Rocqlib|nlist_forall2_sind"
  nlist_forall2_sind : ∀ {A : Type u} {B : Type v} {R : A → B → Prop} (P : nlist A → nlist B →
    Prop), (∀ a b, R a b → P (nbase a) (nbase b)) → (∀ a l b m, R a b → nlist_forall2 R l m → P l m
    → P (ncons a l) (ncons b m)) → ∀ {l m}, nlist_forall2 R l m → P l m

#source_check "src/rocq/Numeric/Rocqlib.v|Vellvm.Numeric.Rocqlib|nlist_forall2_imply"
  nlist_forall2_imply : ∀ {A : Type u} {B : Type v} {R : A → B → Prop} {l m}, nlist_forall2 R l m →
    ∀ S : A → B → Prop, (∀ x y, nIn x l → nIn y m → R x y → S x y) → nlist_forall2 S l m

#source_check "src/rocq/Numeric/Rocqlib.v|Vellvm.Numeric.Rocqlib|list_disjoint_dec"
  list_disjoint_dec : ∀ {A : Type u}, EqDecision A → ∀ l m : List A,
    PSum (list_disjoint l m) (¬list_disjoint l m)

#source_check "src/rocq/Numeric/Rocqlib.v|Vellvm.Numeric.Rocqlib|list_norepet_dec"
  list_norepet_dec : ∀ {A : Type u}, EqDecision A → ∀ l : List A,
    PSum (list_norepet l) (¬list_norepet l)
