module

public import Mathlib.Data.List.Forall2
public import Vellvm.Numeric.Rocqlib
public import Vellvm.Utils.RelationsUtil
public import Vellvm.Tree.Relations

@[expose] public section
namespace Vellvm.Utils.ListUtil
open Vellvm.Numeric.Rocqlib
open Vellvm.Utils.RelationsUtil (prod_rel)
open Vellvm.Tree
universe u v w z

namespace N
def length_h {A : Type u} : List A → Nat → Nat
  | [], n => n
  | _ :: xs, n => length_h xs (n+1)

def length {A : Type u} (xs : List A) : Nat := length_h xs 0

def rev_loop_acc {A : Type u} (f : Nat → A) : Nat → Nat → List A → List A
  | 0, _, acc => acc
  | n+1, i, acc => rev_loop_acc f n (1+i) (f i :: acc)
end N

theorem rev_loop_acc_succ {A : Type u} (f : Nat → A) (n : Nat) :
    N.rev_loop_acc f (n+1) = fun i acc ↦ N.rev_loop_acc f n (1+i) (f i :: acc) := rfl

theorem repeat_app_cons {A : Type u} (x : A) (k : Nat) (acc : List A) :
    List.replicate k x ++ x :: acc = x :: (List.replicate k x ++ acc) := by
  induction k <;> simp [List.replicate_succ, *]

theorem rev_loop_acc_const {A : Type u} (x : A) (n i : Nat) (acc : List A) :
    N.rev_loop_acc (fun _ ↦ x) n i acc = List.replicate n x ++ acc := by
  induction n generalizing i acc with
  | zero => rfl
  | succ n ih => simpa [rev_loop_acc_succ, ih, List.replicate_succ] using repeat_app_cons x n acc

theorem rev_loop_acc_length {A : Type u} (f : Nat → A) (n i : Nat) (acc : List A) :
    (N.rev_loop_acc f n i acc).length = n + acc.length := by
  induction n generalizing i acc with
  | zero => simp [N.rev_loop_acc]
  | succ n ih => simp [rev_loop_acc_succ, ih]; omega

def concat_acc_go {A : Type u} : List (List A) → List A → List A
  | [], acc => acc
  | xs :: ls, acc => concat_acc_go ls (xs.reverseAux acc)

def concat_acc {A : Type u} (ls : List (List A)) := (concat_acc_go ls []).reverse

def map_acc_go {A : Type u} {B : Type v} (f : A → B) : List A → List B → List B
  | [], acc => acc.reverse
  | x :: xs, acc => map_acc_go f xs (f x :: acc)

def map_acc {A : Type u} {B : Type v} (f : A → B) (xs : List A) := map_acc_go f xs []

theorem concat_acc_go_eq {A : Type u} (ls : List (List A)) (acc : List A) :
    concat_acc_go ls acc = ls.flatten.reverseAux acc := by
  induction ls generalizing acc <;> simp [concat_acc_go, *, List.reverseAux_eq, List.append_assoc]

theorem concat_acc_eq {A : Type u} (ls : List (List A)) :
    concat_acc ls = ls.flatten := by
  simp [concat_acc, concat_acc_go_eq, List.reverseAux_eq]

theorem map_acc_go_eq {A : Type u} {B : Type v} (f : A → B) (l : List A) (acc : List B) :
    map_acc_go f l acc = acc.reverseAux (l.map f) := by
  induction l generalizing acc <;> simp [map_acc_go, *, List.reverseAux_eq, List.append_assoc]

theorem map_acc_eq {A : Type u} {B : Type v} (f : A → B) (l : List A) :
    map_acc f l = l.map f := map_acc_go_eq f l []

def In_cons_dec {A : Type u} (a x : A) (xs : List A) :
    EqDecision A → a ∈ x :: xs → PSum (a = x) (a ∈ xs) := by
  intro dec h
  cases dec a x with
  | inl e => exact .inl e
  | inr ne => exact .inr ((List.mem_cons.mp h).resolve_left ne)

theorem fold_right_forall {A : Type u} (P : A → Prop) (l : List A) :
    l.foldr (fun x b ↦ P x ∧ b) True ↔ List.Forall P l := by
  induction l <;> simp [List.Forall, *]

theorem list_cons_app {A : Type u} (x : A) (l : List A) :
    x :: l = [x] ++ l := rfl

def map_In {A : Type u} {B : Type v} (l : List A) (f : ∀ x ∈ l, B) := l.attach.map fun x ↦ f x.val x.property

theorem not_in_app_l {A : Type u} (l₁ l₂ : List A) (x : A) :
    x ∉ l₁ ++ l₂ → x ∉ l₁ := by
  intro h hx; exact h (List.mem_append_left _ hx)

theorem not_in_app_r {A : Type u} (l₁ l₂ : List A) (x : A) :
    x ∉ l₁ ++ l₂ → x ∉ l₂ := by
  simp

theorem find_none_app {A : Type u} (l₁ l₂ : List A) (p : A → Bool) :
    l₁.find? p = none → (l₁ ++ l₂).find? p = l₂.find? p := by
  intro h; simp [List.find?_append, h]

theorem find_some_app {A : Type u} (l₁ l₂ : List A) (a : A) (p : A → Bool) :
    l₁.find? p = some a → (l₁ ++ l₂).find? p = some a := by
  intro h; simp [List.find?_append, h]

def maximumByOpt {A : Type u} (leq : A → A → Bool) : List A → Option A
  | [] => none
  | x :: xs => some (xs.foldl (fun a b ↦ if leq a b then b else a) x)

def rev_tail_rec {A : Type u} (xs : List A) := xs.foldl (fun acc x ↦ x :: acc) []

theorem list_sum_map {A : Type u} (f : A → Nat) (x : A) (xs : List A) :
    x ∈ xs → f x ≤ (xs.map f).sum := by
  intro hx
  induction xs with
  | nil => cases hx
  | cons a xs ih =>
    rcases List.mem_cons.mp hx with rfl | hx
    · simp
    · have := ih hx; simp; omega

theorem forall_repeat_true (A : Type u) (f : A → Prop) (n : Nat) (x : A) :
    f x → List.Forall f (List.replicate n x) := by
  intro h; rw [List.forall_iff_forall_mem]; grind

def Zseq (off : Int) : Nat → List Int
  | 0 => []
  | n+1 => off :: Zseq (off+1) n

def Nseq (off : Nat) : Nat → List Nat
  | 0 => []
  | n+1 => off :: Nseq (off+1) n

theorem Zseq_succ (off : Int) (n : Nat) :
    Zseq off (n+1) = off :: Zseq (off+1) n := rfl

theorem Zseq_length (len : Nat) (off : Int) :
    (Zseq off len).length = len := by
  induction len generalizing off <;> simp [Zseq, *]

def nat_double_acc (n acc : Nat) := acc + 2*n
def nat_double (n : Nat) := nat_double_acc n 0

/-- Both native Lean representations already carry the natural number, without a Peano conversion. -/
def pos_to_nat_safe (p : Positive) := p.val
def N_to_nat_safe (n : Nat) := n

theorem nat_double_acc_eq (n acc : Nat) :
    nat_double_acc n acc = acc + 2*n := rfl

theorem nat_double_eq (n : Nat) :
    nat_double n = 2*n := by
  simp [nat_double, nat_double_acc]

theorem pos_to_nat_safe_eq (p : Positive) :
    pos_to_nat_safe p = p.val := rfl

theorem N_to_nat_safe_eq (n : Nat) :
    N_to_nat_safe n = n := rfl

def seq_map_acc_go {A : Type u} (f : Nat → A) (acc : List A) (cur : Nat) : Nat → List A
  | 0 => acc.reverse
  | n+1 => seq_map_acc_go f (f cur :: acc) (cur+1) n

def seq_map_acc {A : Type u} (f : Nat → A) (start len : Nat) := seq_map_acc_go f [] start len

def repeat_acc_go {A : Type u} (x : A) (acc : List A) : Nat → List A
  | 0 => acc.reverse
  | n+1 => repeat_acc_go x (x :: acc) n

def repeat_acc {A : Type u} (x : A) (n : Nat) := repeat_acc_go x [] n

theorem seq_map_acc_go_eq {A : Type u} (f : Nat → A) (len : Nat) (acc : List A) (cur : Nat) :
    seq_map_acc_go f acc cur len = acc.reverseAux ((Nseq cur len).map f) := by
  induction len generalizing cur acc <;> simp [seq_map_acc_go, Nseq, *, List.reverseAux_eq, List.append_assoc]

theorem seq_map_acc_eq {A : Type u} (f : Nat → A) (start len : Nat) :
    seq_map_acc f start len = (Nseq start len).map f := seq_map_acc_go_eq f len [] start

theorem repeat_acc_go_eq {A : Type u} (x : A) (n : Nat) (acc : List A) :
    repeat_acc_go x acc n = acc.reverseAux (List.replicate n x) := by
  induction n generalizing acc <;> simp [repeat_acc_go, *, List.replicate_succ, List.reverseAux_eq, List.append_assoc]

theorem repeat_acc_eq {A : Type u} (x : A) (n : Nat) :
    repeat_acc x n = List.replicate n x := repeat_acc_go_eq x n []

abbrev drop {A : Type u} := @List.drop A
abbrev take {A : Type u} := @List.take A
abbrev repeatN {A : Type u} := @List.replicate A

theorem repeat_snoc {A : Type u} (x : A) (k : Nat) :
    List.replicate k x ++ [x] = x :: List.replicate k x := by
  simpa using repeat_app_cons x k []

theorem rev_repeat {A : Type u} (x : A) (k : Nat) :
    (List.replicate k x).reverse = List.replicate k x := by
  simp

theorem take_nil {A : Type u} (l : List A) :
    take 0 l = [] := by
  simp [take]

theorem drop_nil {A : Type u} (l : List A) :
    drop 0 l = l := by
  simp [drop]

theorem take_length_le {A : Type u} (l : List A) (n : Nat) :
    (take n l).length ≤ n := by
  simpa only [take, List.length_take] using Nat.min_le_left n l.length

theorem take_length_exact {A : Type u} (l : List A) (n : Nat) :
    n ≤ l.length → (take n l).length = n := by
  intro h; simp [take, Nat.min_eq_left h]

theorem take_all {A : Type u} (l : List A) (n : Nat) :
    l.length ≤ n → take n l = l := List.take_of_length_le

theorem drop_all {A : Type u} (l : List A) (n : Nat) :
    l.length ≤ n → drop n l = [] := by
  simp [drop]

theorem take_app_le {A : Type u} (l r : List A) (n : Nat) :
    n ≤ l.length → take n (l ++ r) = take n l := List.take_append_of_le_length

theorem drop_app_le {A : Type u} (l r : List A) (n : Nat) :
    n ≤ l.length → drop n (l ++ r) = drop n l ++ r := List.drop_append_of_le_length

theorem take_app_exact {A : Type u} (l r : List A) (n : Nat) :
    l.length = n → take n (l ++ r) = l := by
  rintro rfl; simp [take]

theorem drop_app_exact {A : Type u} (l r : List A) (n : Nat) :
    l.length = n → drop n (l ++ r) = r := by
  rintro rfl; simp [drop]

theorem rev_loop_acc_app {A : Type u} (f : Nat → A) (n i : Nat) (acc : List A) :
    N.rev_loop_acc f n i acc = ((Nseq i n).map f).reverse ++ acc := by
  induction n generalizing i acc with
  | zero => rfl
  | succ n ih => simp [rev_loop_acc_succ, Nseq, ih, Nat.add_comm 1 i, List.append_assoc]

theorem Nseq_length (len start : Nat) :
    (Nseq start len).length = len := by
  induction len generalizing start <;> simp [Nseq, *]

theorem In_Nseq (k s i : Nat) :
    i ∈ Nseq s k → s ≤ i ∧ i < s+k := by
  induction k generalizing s with
  | zero => simp [Nseq]
  | succ k ih =>
    intro h; rcases List.mem_cons.mp h with rfl | h
    · omega
    · have := ih (s+1) h; omega

theorem Nseq_snoc (n s : Nat) :
    Nseq s (n+1) = Nseq s n ++ [s+n] := by
  induction n generalizing s with
  | zero => simp [Nseq]
  | succ n ih => simpa only [Nseq, List.cons_append, List.cons.injEq, true_and] using congrArg (s :: ·) ((ih (s+1)).trans (by rw [show s+1+n = s+(n+1) by omega]))

theorem map_const_Nseq {A : Type u} (x : A) (k s : Nat) :
    (Nseq s k).map (fun _ ↦ x) = List.replicate k x := by
  induction k generalizing s <;> simp [Nseq, List.replicate_succ, *]

theorem take_drop_app {A : Type u} (n : Nat) (l : List A) :
    take n l ++ drop n l = l := by
  simp [take, drop]

theorem drop_drop {A : Type u} (m n : Nat) (l : List A) :
    drop m (drop n l) = drop (n+m) l := by
  simp [drop, Nat.add_comm]

theorem length_drop_N {A : Type u} (l : List A) (n : Nat) :
    (drop n l).length = l.length - n := by
  simp [drop]

theorem take_take_le {A : Type u} (l : List A) (m k : Nat) :
    m ≤ k → take m (take k l) = take m l := by
  intro h; simp [take, List.take_take, Nat.min_eq_left h, Nat.min_eq_right h]

theorem drop_take {A : Type u} (l : List A) (n i : Nat) :
    drop i (take n l) = take (n-i) (drop i l) := by
  simp [drop, take, List.drop_take]

theorem In_take_N {A : Type u} (n : Nat) (l : List A) (x : A) :
    x ∈ take n l → x ∈ l := by
  exact List.mem_of_mem_take

theorem Forall_take_N {A : Type u} (P : A → Prop) (n : Nat) (l : List A) :
    List.Forall P l → List.Forall P (take n l) := by
  simp only [List.forall_iff_forall_mem]; intro h x hx; exact h x (In_take_N n l x hx)

theorem forallb_take_pres {A : Type u} (f : A → Bool) (l : List A) (n : Nat) :
    l.all f = true → (take n l).all f = true := by
  simp only [List.all_eq_true]; intro h x hx; exact h x (In_take_N n l x hx)

theorem In_drop_N {A : Type u} (n : Nat) (l : List A) (x : A) :
    x ∈ drop n l → x ∈ l := by
  exact List.mem_of_mem_drop

theorem Forall_drop_N {A : Type u} (P : A → Prop) (n : Nat) (l : List A) :
    List.Forall P l → List.Forall P (drop n l) := by
  simp only [List.forall_iff_forall_mem]; intro h x hx; exact h x (In_drop_N n l x hx)

theorem forallb_drop_pres {A : Type u} (f : A → Bool) (l : List A) (n : Nat) :
    l.all f = true → (drop n l).all f = true := by
  simp only [List.all_eq_true]; intro h x hx; exact h x (In_drop_N n l x hx)

theorem drop_length_le {A : Type u} (l : List A) (n : Nat) :
    (drop n l).length ≤ l.length := by
  simp [drop]

theorem drop_length_lt {A : Type u} (l : List A) (n : Nat) :
    1 ≤ n → l ≠ [] → (drop n l).length < l.length := by
  intro hn hl; cases l <;> simp_all [drop] <;> omega

theorem existsb_concat_map {A : Type u} {B : Type v} (f : B → Bool) (g : A → List B) (l : List A) (x : A) :
    (l.map g).flatten.any f = false → x ∈ l → (g x).any f = false := by
  simp only [List.any_eq_false]
  intro h hx y hy
  exact h y (List.mem_flatten.mpr ⟨_, List.mem_map.mpr ⟨_, hx, rfl⟩, hy⟩)

theorem forallb_concat_map {A : Type u} {B : Type v} (f : B → Bool) (g : A → List B) (l : List A) (x : A) :
    (l.map g).flatten.all f = true → x ∈ l → (g x).all f = true := by
  simp only [List.all_eq_true]
  intro h hx y hy
  exact h y (List.mem_flatten.mpr ⟨_, List.mem_map.mpr ⟨_, hx, rfl⟩, hy⟩)

def split_every_pos {A : Type u} (n : Positive) (xs : List A) : List (List A) :=
  match xs with
  | [] => []
  | x :: tl => take n.val (x :: tl) :: split_every_pos n (drop n.val (x :: tl))
termination_by xs.length
decreasing_by exact drop_length_lt _ _ n.property (List.cons_ne_nil _ _)

def split_every_nil {A : Type u} : Nat → List A → List (List A)
  | 0, _ => []
  | n+1, xs => split_every_pos ⟨n+1, by omega⟩ xs

theorem split_every_pos_equation {A : Type u} (n : Positive) (xs : List A) :
    split_every_pos n xs = match xs with
      | [] => []
      | _ :: _ => take n.val xs :: split_every_pos n (drop n.val xs) := by
  cases xs <;> rw [split_every_pos]

theorem split_every_pos_tcc {A : Type u} (n : Positive) (xs : List A) (a : A) (l : List A) :
    xs = a :: l → (drop n.val (a :: l)).length < (a :: l).length := by
  intro _; exact drop_length_lt _ _ n.property (List.cons_ne_nil _ _)

inductive R_split_every_pos (A : Type u) (n : Positive) : List A → List (List A) → Type u where
  | R_split_every_pos_0 (xs : List A) (e : xs = []) : R_split_every_pos A n [] []
  | R_split_every_pos_1 (xs : List A) (x : A) (tl : List A) (e : xs = x :: tl) (res : List (List A))
      (h : R_split_every_pos A n (drop n.val xs) res) :
      R_split_every_pos A n (x :: tl) (take n.val xs :: res)

export R_split_every_pos (R_split_every_pos_0 R_split_every_pos_1)

def R_split_every_pos_rect : ∀ (A : Type u) (n : Positive) (P : ∀ xs ys, R_split_every_pos A n xs ys → Type v),
    (∀ (xs : List A) (e : xs = []), P [] [] (@R_split_every_pos_0 A n xs e)) →
    (∀ (xs : List A) (x : A) (tl : List A) (e : xs = x :: tl) (res : List (List A)) (h : R_split_every_pos A n (drop n.val xs) res),
      P (drop n.val xs) res h → P (x :: tl) (take n.val xs :: res) (@R_split_every_pos_1 A n xs x tl e res h)) →
    ∀ xs ys (h : R_split_every_pos A n xs ys), P xs ys h
  | _, _, _, hn, _, _, _, .R_split_every_pos_0 xs e => hn xs e
  | A, n, P, hn, hc, _, _, .R_split_every_pos_1 xs x tl e res h =>
    hc xs x tl e res h (R_split_every_pos_rect A n P hn hc _ _ h)

def R_split_every_pos_rec : ∀ (A : Type u) (n : Positive) (P : ∀ xs ys, R_split_every_pos A n xs ys → Type),
    (∀ (xs : List A) (e : xs = []), P [] [] (@R_split_every_pos_0 A n xs e)) →
    (∀ (xs : List A) (x : A) (tl : List A) (e : xs = x :: tl) (res : List (List A)) (h : R_split_every_pos A n (drop n.val xs) res),
      P (drop n.val xs) res h → P (x :: tl) (take n.val xs :: res) (@R_split_every_pos_1 A n xs x tl e res h)) →
    ∀ xs ys (h : R_split_every_pos A n xs ys), P xs ys h :=
  R_split_every_pos_rect

theorem R_split_every_pos_ind : ∀ (A : Type u) (n : Positive) (P : ∀ xs ys, R_split_every_pos A n xs ys → Prop),
    (∀ (xs : List A) (e : xs = []), P [] [] (@R_split_every_pos_0 A n xs e)) →
    (∀ (xs : List A) (x : A) (tl : List A) (e : xs = x :: tl) (res : List (List A)) (h : R_split_every_pos A n (drop n.val xs) res),
      P (drop n.val xs) res h → P (x :: tl) (take n.val xs :: res) (@R_split_every_pos_1 A n xs x tl e res h)) →
    ∀ xs ys (h : R_split_every_pos A n xs ys), P xs ys h :=
  fun _ _ _ hn hc _ _ h ↦ R_split_every_pos.rec hn hc h

theorem R_split_every_pos_sind : ∀ (A : Type u) (n : Positive) (P : ∀ xs ys, R_split_every_pos A n xs ys → Prop),
    (∀ (xs : List A) (e : xs = []), P [] [] (@R_split_every_pos_0 A n xs e)) →
    (∀ (xs : List A) (x : A) (tl : List A) (e : xs = x :: tl) (res : List (List A)) (h : R_split_every_pos A n (drop n.val xs) res),
      P (drop n.val xs) res h → P (x :: tl) (take n.val xs :: res) (@R_split_every_pos_1 A n xs x tl e res h)) →
    ∀ xs ys (h : R_split_every_pos A n xs ys), P xs ys h :=
  fun _ _ _ hn hc _ _ h ↦ R_split_every_pos.rec hn hc h

theorem R_split_every_pos_complete {A : Type u} (n : Positive) (xs : List A) (res : List (List A)) :
    R_split_every_pos A n xs res → res = split_every_pos n xs := by
  intro h; induction h with
  | R_split_every_pos_0 => rw [split_every_pos]
  | R_split_every_pos_1 xs x tl e res h ih => subst xs; rw [split_every_pos, ih]

def R_split_every_pos_correct {A : Type u} (n : Positive) (xs : List A) (res : List (List A))
    (he : res = split_every_pos n xs) : R_split_every_pos A n xs res := by
  subst res
  cases xs with
  | nil => rw [split_every_pos]; exact .R_split_every_pos_0 [] rfl
  | cons x tl =>
    rw [split_every_pos]
    exact .R_split_every_pos_1 (x :: tl) x tl rfl _ (R_split_every_pos_correct n _ _ rfl)
termination_by xs.length
decreasing_by subst xs; exact drop_length_lt _ _ n.property (List.cons_ne_nil _ _)

def splitRec {A : Type u} (n : Positive) (P : List A → List (List A) → Sort v)
    (hn : ∀ (xs : List A), xs = [] → P [] [])
    (hc : ∀ (xs : List A) (x : A) (tl : List A), xs = x :: tl →
      P (drop n.val xs) (split_every_pos n (drop n.val xs)) →
      P (x :: tl) (take n.val xs :: split_every_pos n (drop n.val xs))) (xs : List A) :
    P xs (split_every_pos n xs) := by
  cases xs with
  | nil => rw [split_every_pos]; exact hn [] rfl
  | cons x tl =>
    rw [split_every_pos]
    exact hc (x :: tl) x tl rfl (splitRec n P hn hc _)
termination_by xs.length
decreasing_by exact drop_length_lt _ _ n.property (List.cons_ne_nil _ _)

def split_every_pos_rect : ∀ {A : Type u} (n : Positive) (P : List A → List (List A) → Type v),
    (∀ (xs : List A), xs = [] → P [] []) →
    (∀ (xs : List A) (x : A) (tl : List A), xs = x :: tl → P (drop n.val xs) (split_every_pos n (drop n.val xs)) →
      P (x :: tl) (take n.val xs :: split_every_pos n (drop n.val xs))) → ∀ xs, P xs (split_every_pos n xs) := @splitRec

def split_every_pos_rec : ∀ {A : Type u} (n : Positive) (P : List A → List (List A) → Type),
    (∀ (xs : List A), xs = [] → P [] []) →
    (∀ (xs : List A) (x : A) (tl : List A), xs = x :: tl → P (drop n.val xs) (split_every_pos n (drop n.val xs)) →
      P (x :: tl) (take n.val xs :: split_every_pos n (drop n.val xs))) → ∀ xs, P xs (split_every_pos n xs) := @splitRec

theorem split_every_pos_ind : ∀ {A : Type u} (n : Positive) (P : List A → List (List A) → Prop),
    (∀ (xs : List A), xs = [] → P [] []) →
    (∀ (xs : List A) (x : A) (tl : List A), xs = x :: tl → P (drop n.val xs) (split_every_pos n (drop n.val xs)) →
      P (x :: tl) (take n.val xs :: split_every_pos n (drop n.val xs))) → ∀ xs, P xs (split_every_pos n xs) := @splitRec

def split_every_pos_F (rec : (A : Type u) → Positive → List A → List (List A)) {A : Type u}
    (n : Positive) (xs : List A) := match xs with
  | [] => []
  | _ :: _ => take n.val xs :: rec A n (drop n.val xs)

def split_every_pos_terminate {A : Type u} (n : Positive) (xs : List A) :
    {v : List (List A) // ∃ p : Nat, ∀ k, p < k →
      ∀ d : (T : Type u) → Positive → List T → List (List T),
        k.repeat (fun r T ↦ @split_every_pos_F r T) d A n xs = v} := by
  refine ⟨split_every_pos n xs, xs.length, ?_⟩
  intro k
  induction k generalizing xs with
  | zero => omega
  | succ k ih =>
    intro h d
    rw [Nat.repeat.eq_2, split_every_pos_equation]
    cases xs with
    | nil => rfl
    | cons x tl =>
      change take n.val (x :: tl) :: _ = take n.val (x :: tl) :: _
      congr 1
      apply ih
      have := drop_length_lt (x :: tl) n.val n.property (List.cons_ne_nil _ _)
      omega

abbrev zipWith {A : Type u} {B : Type v} {C : Type w} := @List.zipWith A B C
abbrev zip {A : Type u} {B : Type v} := @List.zip A B

theorem take_repeat_cons {A : Type u} (x : A) (n k : Nat) :
    0 < n → 0 < k → ∃ r, take n (List.replicate k x) = x :: r := by
  cases n <;> cases k <;> simp [take, List.replicate_succ]

theorem In_rev_loop_acc {A : Type u} (f : Nat → A) (n i : Nat) (acc : List A) (b : A) :
    b ∈ N.rev_loop_acc f n i acc → b ∈ acc ∨ ∃ j, b = f j := by
  rw [rev_loop_acc_app]
  intro h
  rcases List.mem_append.mp h with h | h
  · obtain ⟨j, _, hj⟩ := List.mem_map.mp (List.mem_reverse.mp h)
    exact .inr ⟨j, hj.symm⟩
  · exact .inl h

theorem map_Nseq_shift {A : Type u} (f : Nat → A) (n a s : Nat) :
    (Nseq a n).map (fun i ↦ f (s+i)) = (Nseq (s+a) n).map f := by
  induction n generalizing a s <;> simp [Nseq, *, Nat.add_assoc]

theorem map_Nseq_nth {A : Type u} (l : List A) (d : A) (s : Nat) :
    (Nseq s l.length).map (fun i ↦ l.getD (i-s) d) = l := by
  induction l generalizing s with
  | nil => rfl
  | cons x xs ih =>
    simp only [List.length_cons, Nseq, List.map_cons, Nat.sub_self, List.getD_cons_zero, List.cons.injEq, true_and]
    calc
      _ = (Nseq (s+1) xs.length).map (fun i ↦ xs.getD (i-(s+1)) d) := by
        apply List.map_congr_left; intro i hi
        have := In_Nseq xs.length (s+1) i hi
        rw [show i-s = (i-(s+1))+1 by omega, List.getD_cons_succ]
      _ = xs := ih _

theorem fold_left_add_right {A : Type u} (f : A → Nat) (l : List A) (a : Nat) :
    l.foldl (fun acc dt ↦ acc + f dt) a = a + l.foldr (fun dt acc ↦ f dt + acc) 0 := by
  induction l generalizing a <;> simp [*, Nat.add_assoc]

theorem length_take {A : Type u} {B : Type v} (l : List A) (l' : List B) (n : Nat) :
    l.length = l'.length → (take n l).length = (take n l').length := by
  intro h; simp [take, h]

theorem length_drop {A : Type u} {B : Type v} (l : List A) (l' : List B) (n : Nat) :
    l.length = l'.length → (drop n l).length = (drop n l').length := by
  intro h; simp [drop, h]

def zip_acc_go {A : Type u} {B : Type v} (acc : List (A × B)) : List A → List B → List (A × B)
  | x :: xs, y :: ys => zip_acc_go ((x,y) :: acc) xs ys
  | _, _ => acc.reverse

def zip_acc {A : Type u} {B : Type v} (xs : List A) (ys : List B) := zip_acc_go [] xs ys

theorem zip_acc_go_eq {A : Type u} {B : Type v} (xs : List A) (ys : List B) (acc : List (A × B)) :
    zip_acc_go acc xs ys = acc.reverseAux (zip xs ys) := by
  induction xs generalizing ys acc with
  | nil => cases ys <;> rfl
  | cons x xs ih => cases ys <;> simp [zip_acc_go, zip, ih, List.reverseAux_eq, List.append_assoc]

theorem zip_acc_eq {A : Type u} {B : Type v} (xs : List A) (ys : List B) :
    zip_acc xs ys = zip xs ys := zip_acc_go_eq xs ys []

def zip3 {A : Type u} {B : Type v} {C : Type w} : List A → List B → List C → List ((A × B) × C)
  | x :: xs, y :: ys, z :: zs => ((x,y),z) :: zip3 xs ys zs
  | _, _, _ => []

abbrev find_option {A : Type u} {B : Type v} := @List.findSome? A B
abbrev filter_option {A : Type u} {B : Type v} := @List.filterMap A B

def map_option {A : Type u} {B : Type v} (f : A → Option B) : List A → Option (List B)
  | [] => some []
  | x :: xs => do return (← f x) :: (← map_option f xs)

def FORALL {A : Type u} (P : A → Prop) (l : List A) := l.foldr (fun x b ↦ P x ∧ b) True

theorem FORALL_forall {A : Type u} (P : A → Prop) (l : List A) :
    FORALL P l ↔ List.Forall P l := fold_right_forall P l

def FORALL_dec {A : Type u} (P : A → Prop) (l : List A) :
    (∀ x ∈ l, PSum (P x) (¬ P x)) → PSum (FORALL P l) (¬ FORALL P l) := by
  induction l with
  | nil => exact fun _ ↦ .inl trivial
  | cons a l ih =>
    intro h
    cases h a (by simp) with
    | inr na => exact .inr (fun h ↦ na h.1)
    | inl ha =>
      cases ih (fun x hx ↦ h x (List.mem_cons_of_mem _ hx)) with
      | inr nt => exact .inr (fun h ↦ nt h.2)
      | inl ht => exact .inl ⟨ha, ht⟩

scoped infix:60 " ⊍ " => list_disjoint

theorem list_disjoint_nil_l {A : Type u} (l : List A) :
    list_disjoint [] l := by
  unfold list_disjoint; grind

theorem list_disjoint_nil_r {A : Type u} (l : List A) :
    list_disjoint l [] := by
  unfold list_disjoint; grind

theorem list_disjoint_cons_l_iff (A : Type u) (a : A) (l₁ l₂ : List A) :
    list_disjoint (a :: l₁) l₂ ↔ list_disjoint l₁ l₂ ∧ a ∉ l₂ := by
  unfold list_disjoint; grind

theorem list_disjoint_singleton_left {A : Type u} (l : List A) (x : A) :
    list_disjoint [x] l ↔ x ∉ l := by
  unfold list_disjoint; grind

theorem list_disjoint_singleton_right {A : Type u} (l : List A) (x : A) :
    list_disjoint l [x] ↔ x ∉ l := by
  unfold list_disjoint; grind

theorem list_disjoint_app_l {A : Type u} (l₁ l₂ l₃ : List A) :
    list_disjoint (l₁ ++ l₂) l₃ ↔ list_disjoint l₁ l₃ ∧ list_disjoint l₂ l₃ := by
  unfold list_disjoint; grind

theorem list_disjoint_app_r {A : Type u} (l₁ l₂ l₃ : List A) :
    list_disjoint l₁ (l₂ ++ l₃) ↔ list_disjoint l₁ l₂ ∧ list_disjoint l₁ l₃ := by
  unfold list_disjoint; grind

theorem list_disjoint_singletons {A : Type u} (x y : A) :
    list_disjoint [x] [y] ↔ x ≠ y := by
  simp [list_disjoint]

theorem Forall_disjoint {A : Type u} (l₁ l₂ : List A) (P Q : A → Prop) :
    List.Forall P l₁ → List.Forall Q l₂ → (∀ x, P x → ¬ Q x) → list_disjoint l₁ l₂ := by
  simp only [List.forall_iff_forall_mem, list_disjoint]; grind

theorem Forall2_repeat {A : Type u} {B : Type v} (R : A → B → Prop) (a : A) (b : B) (n : Nat) :
    R a b → List.Forall₂ R (List.replicate n a) (List.replicate n b) := by
  intro h; induction n <;> simp [List.replicate_succ, *]

theorem Forall2_diag {A : Type u} (P : A → A → Prop) (l : List A) :
    List.Forall₂ P l l ↔ List.Forall (fun a ↦ P a a) l := by
  simp [List.forall_iff_forall_mem]

theorem Forall2_combine {A : Type u} {B : Type v} {C : Type w} {D : Type z} (RA : A → B → Prop) (RB : C → D → Prop) (l₁ : List A) (l₂ : List B) (k₁ : List C) (k₂ : List D) :
    List.Forall₂ RA l₁ l₂ → List.Forall₂ RB k₁ k₂ → List.Forall₂ (prod_rel RA RB) (l₁.zip k₁) (l₂.zip k₂) := by
  intro hl; induction hl generalizing k₁ k₂ with
  | nil => simp
  | cons hab _ ih =>
    intro hk; cases hk with
    | nil => simp
    | cons hcd ht => exact .cons ⟨hab, hcd⟩ (ih _ _ ht)

theorem Forall2_length_N_h {A : Type u} {B : Type v} (R : A → B → Prop) (l₁ : List A) (l₂ : List B) (acc : Nat) :
    List.Forall₂ R l₁ l₂ → N.length_h l₁ acc = N.length_h l₂ acc := by
  intro h; induction h generalizing acc <;> simp [N.length_h, *]

theorem Forall2_length_N {A : Type u} {B : Type v} (R : A → B → Prop) (l₁ : List A) (l₂ : List B) :
    List.Forall₂ R l₁ l₂ → N.length l₁ = N.length l₂ := Forall2_length_N_h R l₁ l₂ 0

theorem Forall2_map2 {A : Type u} {B : Type v} {C : Type w} (R : B → C → Prop) (f : A → B) (g : A → C) (l : List A) :
    (∀ x ∈ l, R (f x) (g x)) → List.Forall₂ R (l.map f) (l.map g) := by
  simp

theorem Forall2_take {A : Type u} {B : Type v} (R : A → B → Prop) (l₁ : List A) (l₂ : List B) :
    List.Forall₂ R l₁ l₂ → ∀ n, List.Forall₂ R (take n l₁) (take n l₂) := fun h n ↦ List.forall₂_take n h

theorem Forall2_drop {A : Type u} {B : Type v} (R : A → B → Prop) (l₁ : List A) (l₂ : List B) :
    List.Forall₂ R l₁ l₂ → ∀ n, List.Forall₂ R (drop n l₁) (drop n l₂) := fun h n ↦ List.forall₂_drop n h

theorem Forall2_repeatN {A : Type u} {B : Type v} (R : A → B → Prop) (a : A) (b : B) :
    R a b → ∀ n, List.Forall₂ R (repeatN n a) (repeatN n b) := fun h n ↦ Forall2_repeat R a b n h

theorem Forall2_eq {A : Type u} (l₁ l₂ : List A) :
    List.Forall₂ Eq l₁ l₂ → l₁ = l₂ := by
  simp

theorem eq_Forall2 {A : Type u} (l : List A) :
    List.Forall₂ Eq l l := by
  simp

theorem Forall2_filter {A : Type u} {B : Type v} (R : A → B → Prop) (p : A → Bool) (q : B → Bool) :
    (∀ a b, R a b → p a = q b) → ∀ (l₁ : List A) (l₂ : List B), List.Forall₂ R l₁ l₂ → List.Forall₂ R (l₁.filter p) (l₂.filter q) := by
  intro hp l r h
  induction h with
  | nil => exact .nil
  | @cons a b l r hab _ ih => cases he : q b <;> simp [List.filter_cons, hp a b hab, he, ih, hab]

theorem Forall2_concat {A : Type u} {B : Type v} (R : A → B → Prop) (ls₁ : List (List A)) (ls₂ : List (List B)) :
    List.Forall₂ (List.Forall₂ R) ls₁ ls₂ → List.Forall₂ R ls₁.flatten ls₂.flatten := by
  intro h; induction h with
  | nil => exact .nil
  | cons hr _ ih =>
    induction hr with
    | nil => exact ih
    | cons h _ tail => exact .cons h tail

theorem Forall2_zip {A : Type u} {B : Type v} {C : Type w} {D : Type z} (RA : A → B → Prop) (RB : C → D → Prop) (l₁ : List A) (l₂ : List B) :
    List.Forall₂ RA l₁ l₂ → ∀ (k₁ : List C) (k₂ : List D), List.Forall₂ RB k₁ k₂ → List.Forall₂ (prod_rel RA RB) (zip l₁ k₁) (zip l₂ k₂) := fun hl k₁ k₂ hk ↦ Forall2_combine RA RB l₁ l₂ k₁ k₂ hl hk

theorem Forall2_split_every_pos {A : Type u} {B : Type v} (R : A → B → Prop) (n : Positive) (k : Nat) (l₁ : List A) (l₂ : List B) :
    l₁.length ≤ k → List.Forall₂ R l₁ l₂ → List.Forall₂ (List.Forall₂ R) (split_every_pos n l₁) (split_every_pos n l₂) := by
  induction k generalizing l₁ l₂ with
  | zero =>
    intro len h; have : l₁ = [] := by simpa using len
    subst l₁; cases h; simp [split_every_pos_equation n []]
  | succ k ih =>
    intro len h; cases h with
    | nil => simp [split_every_pos_equation n []]
    | @cons a b l r hab hr =>
      rw [split_every_pos_equation n (a :: l), split_every_pos_equation n (b :: r)]
      exact .cons (Forall2_take R _ _ (.cons hab hr) _) (ih _ _ (by
        have := drop_length_lt (a :: l) n.val n.property (List.cons_ne_nil _ _); omega)
        (Forall2_drop R _ _ (.cons hab hr) _))

theorem Forall2_split_every_nil {A : Type u} {B : Type v} (R : A → B → Prop) (n : Nat) (l₁ : List A) (l₂ : List B) :
    List.Forall₂ R l₁ l₂ → List.Forall₂ (List.Forall₂ R) (split_every_nil n l₁) (split_every_nil n l₂) := by
  intro h; cases n with
  | zero => exact .nil
  | succ n => exact Forall2_split_every_pos R _ _ _ _ (Nat.le_refl _) h

theorem Forall2_nth_error {A : Type u} {B : Type v} (R : A → B → Prop) (l₁ : List A) (l₂ : List B) :
    List.Forall₂ R l₁ l₂ → ∀ n : Nat, match l₁[n]?, l₂[n]? with
      | some a, some b => R a b
      | none, none => True
      | _, _ => False := by
  intro h; induction h with
  | nil => intro n; simp
  | cons hab _ ih => intro n; cases n with
    | zero => exact hab
    | succ n => exact ih n

theorem Forall2_map_rel {A : Type u} {B : Type v} {C : Type w} {D : Type z} (RA : A → B → Prop) (RB : C → D → Prop) (f : A → C) (g : B → D) :
    (∀ a b, RA a b → RB (f a) (g b)) → ∀ (l₁ : List A) (l₂ : List B), List.Forall₂ RA l₁ l₂ → List.Forall₂ RB (l₁.map f) (l₂.map g) := by
  intro hr l r h; simpa only [List.forall₂_map_left_iff, List.forall₂_map_right_iff] using h.imp hr

theorem Forall2_rev_append {A : Type u} {B : Type v} (R : A → B → Prop) (l₁ : List A) (l₂ : List B) :
    List.Forall₂ R l₁ l₂ → ∀ (m₁ : List A) (m₂ : List B), List.Forall₂ R m₁ m₂ → List.Forall₂ R (l₁.reverseAux m₁) (l₂.reverseAux m₂) := by
  intro h; induction h with
  | nil => exact fun _ _ h ↦ h
  | cons hab _ ih => exact fun _ _ h ↦ ih _ _ (.cons hab h)

theorem Forall2_nth_Nseq {A : Type u} {B : Type v} (R : A → B → Prop) (f : Nat → B) (d : A) (l : List A) (s : Nat) :
    (∀ i, i < l.length → R (l.getD i d) (f (s+i))) → List.Forall₂ R l ((Nseq s l.length).map f) := by
  induction l generalizing s with
  | nil => exact fun _ ↦ .nil
  | cons x xs ih =>
    intro h
    refine .cons (by simpa using h 0 (by simp)) (ih (s+1) ?_)
    intro i hi; simpa [Nat.add_assoc, Nat.add_comm 1 i] using h (i+1) (by simpa using hi)

theorem Forall2_rev_loop_acc {A : Type u} {B : Type v} (R : A → B → Prop) (f : Nat → A) (g : Nat → B) :
    (∀ i, R (f i) (g i)) → ∀ (n i : Nat) (xs : List A) (ys : List B), List.Forall₂ R xs ys → List.Forall₂ R (N.rev_loop_acc f n i xs) (N.rev_loop_acc g n i ys) := by
  intro hr n; induction n with
  | zero => exact fun _ _ _ h ↦ h
  | succ n ih => exact fun i _ _ h ↦ ih _ _ _ (.cons (hr i) h)

section
variable {m : Type u → Type v} [Monad m]

def monad_fold_right {A : Type w} {B : Type u} (f : B → A → m B) : List A → B → m B
  | [], b => pure b
  | x :: xs, b => monad_fold_right f xs b >>= fun r ↦ f r x

def monad_app_fst {m : Type (max u w) → Type v} [Monad m]
    {A : Type z} {B : Type w} {C : Type (max u w)} (f : A → m C) (p : A × B) : m (C × B) := do
  return (← f p.1, p.2)

def monad_app_snd {m : Type (max u w) → Type v} [Monad m]
    {A : Type w} {B : Type z} {C : Type (max u w)} (f : B → m C) (p : A × B) : m (A × C) := do
  return (p.1, ← f p.2)

def map_monad {A : Type w} {B : Type u} (f : A → m B) : List A → m (List B)
  | [] => pure []
  | x :: xs => f x >>= fun b ↦ map_monad f xs >>= fun bs ↦ pure (b :: bs)

def loop_monad {A : Type w} {B : Type u} (f : A → m B) : List A → m PUnit
  | [] => pure ⟨⟩
  | x :: xs => f x >>= fun _ ↦ loop_monad f xs

def map_monad_acc {A : Type w} {B : Type u} (f : A → m B) (xs : List A) : m (List B) := go [] xs
where
  go acc : List A → m (List B)
    | [] => pure acc.reverse
    | x :: xs => f x >>= fun b ↦ go (b :: acc) xs

def seq_map_monad_acc_go {A : Type u} (f : Nat → m A) (acc : List A) (cur : Nat) : Nat → m (List A)
  | 0 => pure acc.reverse
  | n+1 => f cur >>= fun x ↦ seq_map_monad_acc_go f (x :: acc) (cur+1) n

def seq_map_monad_acc {A : Type u} (f : Nat → m A) (start len : Nat) := seq_map_monad_acc_go f [] start len

def sequence {A : Type u} (ms : List (m A)) : m (List A) := map_monad id ms

def foldM {A : Type w} {B : Type u} (f : B → A → m B) (acc : B) : List A → m B
  | [] => pure acc
  | x :: xs => f acc x >>= fun b ↦ foldM f b xs

def repeatM {A : Type u} (n : Nat) (ma : m A) := sequence (List.replicate n ma)

def vec_loop {A : Type w} {B : Type z} {C : Type u} (f : A → B → m C) (elts : List (A × B)) : m (List C) :=
  monad_fold_right (fun acc p ↦ f p.1 p.2 >>= fun val ↦ pure (val :: acc)) elts []

end

def repeatMN {A : Type u} {m : Type u → Type v} [Monad m] (n : Nat) (ma : m A) := sequence (repeatN n ma)

theorem sequence_cons {m : Type u → Type v} [Monad m] {A : Type u} (ma : m A) (mas : List (m A)) :
    sequence (ma :: mas) = (ma >>= fun x ↦ sequence mas >>= fun xs ↦ pure (x :: xs)) := rfl

section Trees
open CTree Coinduction
variable {E B : ITree.Effect.{u}} {X Y U V : Type u} {b₁ b₂ : Bool}

private def bindHead (k : X → CTree E B U) : Head E B X → Head E B U
  | .ret x => (k x).unfold
  | .stuck => .stuck
  | .guard t => .guard (t >>= k)
  | .step t => .step (t >>= k)
  | .vis e h => .vis e (fun a ↦ h a >>= k)
  | .br c h => .br c (fun a ↦ h a >>= k)

private theorem unfoldBind (t : CTree E B X) (k : X → CTree E B U) :
    (t >>= k).unfold = bindHead k t.unfold := by
  rw [bind_def]; cases t.unfold <;> simp [bindHead]

/-- Congruence retains both choices of guard-stripping flag, even through a finite skip. -/
theorem eqit_bind {RR : X → Y → Prop} {RS : U → V → Prop}
    {k : X → CTree E B U} {l : Y → CTree E B V}
    (hk : ∀ x y, RR x y → eqit RS b₁ b₂ (k x) (l y)) :
    ∀ (t : CTree E B X) (s : CTree E B Y), eqit RR b₁ b₂ t s → eqit RS b₁ b₂ (t >>= k) (s >>= l) := by
  coinduction R hR ih
  intro t s h
  change Layer _ R (t >>= k).unfold (s >>= l).unfold
  rw [unfoldBind, unfoldBind]
  have hl := related_iff.mp h
  generalize t.unfold = a at hl ⊢
  generalize s.unfold = b at hl ⊢
  induction hl with
  | ret h => exact (related_iff.mp (hk _ _ h)).mono (gfp_le_chain hR)
  | stuck => exact .stuck
  | step h => exact .step (ih _ _ h)
  | guard h => exact .guard (ih _ _ h)
  | vis he hl => exact .vis he fun a b hab ↦ ih _ _ (hl a b hab)
  | br hl => exact .br fun a ↦ ih _ _ (hl a)
  | skipL flag _ hi => exact .skipL flag (by rw [unfoldBind]; exact hi)
  | skipR flag _ hi => exact .skipR flag (by rw [unfoldBind]; exact hi)
  | cutL h => exact False.elim h
  | cutR h => exact False.elim h

private theorem eqitPure {RR : X → Y → Prop} {x y} (h : RR x y) :
    eqit (E := E) (B := B) RR b₁ b₂ (pure x) (pure y) := by
  apply related_iff.mpr
  rw [unfold_pure, unfold_pure]; exact .ret h
end Trees

theorem eqit_map_monad {E B : ITree.Effect.{u}} {X Y : Type u} {A : Type v} {C : Type w} {b₁ b₂ : Bool} (RR : X → Y → Prop) (f : A → CTree.CTree E B X) (g : C → CTree.CTree E B Y) (l : List A) (r : List C) :
    List.Forall₂ (fun a b ↦ eqit RR b₁ b₂ (f a) (g b)) l r → eqit (List.Forall₂ RR) b₁ b₂ (map_monad f l) (map_monad g r) := by
  intro h; induction h with
  | nil => exact eqitPure List.Forall₂.nil
  | cons h _ ih =>
    exact eqit_bind (fun _ _ hr ↦ eqit_bind (fun _ _ ht ↦ eqitPure (.cons hr ht)) _ _ ih) _ _ h

theorem eqit_map_monad' {E B : ITree.Effect.{u}} {X : Type u} {A : Type v} {b₁ b₂ : Bool} (f g : A → CTree.CTree E B X) (l r : List A) :
    List.Forall₂ (fun a b ↦ eqit Eq b₁ b₂ (f a) (g b)) l r → eqit Eq b₁ b₂ (map_monad f l) (map_monad g r) := by
  intro h; simpa only [List.forall₂_eq_eq_eq] using eqit_map_monad Eq f g l r h

end Vellvm.Utils.ListUtil

