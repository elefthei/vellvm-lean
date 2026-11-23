import PortChecks.SourceType
import Vellvm.Utils.ListUtil

open Vellvm Vellvm.Utils.ListUtil Vellvm.Numeric.Rocqlib Vellvm.Tree
open Vellvm.Utils.RelationsUtil (prod_rel)
universe u v w z

#source_check "src/rocq/Utils/ListUtil.v|Vellvm.Utils.ListUtil|rev_loop_acc_succ"
  rev_loop_acc_succ : ∀ {A : Type u} (f : Nat → A) (n : Nat), N.rev_loop_acc f (n+1) = fun i acc ↦ N.rev_loop_acc f n (1+i) (f i :: acc)

#source_check "src/rocq/Utils/ListUtil.v|Vellvm.Utils.ListUtil|repeat_app_cons"
  repeat_app_cons : ∀ {A : Type u} (x : A) (k : Nat) (acc : List A), List.replicate k x ++ x :: acc = x :: (List.replicate k x ++ acc)

#source_check "src/rocq/Utils/ListUtil.v|Vellvm.Utils.ListUtil|rev_loop_acc_const"
  rev_loop_acc_const : ∀ {A : Type u} (x : A) (n i : Nat) (acc : List A), N.rev_loop_acc (fun _ ↦ x) n i acc = List.replicate n x ++ acc

#source_check "src/rocq/Utils/ListUtil.v|Vellvm.Utils.ListUtil|rev_loop_acc_length"
  rev_loop_acc_length : ∀ {A : Type u} (f : Nat → A) (n i : Nat) (acc : List A), (N.rev_loop_acc f n i acc).length = n + acc.length

#source_check "src/rocq/Utils/ListUtil.v|Vellvm.Utils.ListUtil|concat_acc_go_eq"
  concat_acc_go_eq : ∀ {A : Type u} (ls : List (List A)) (acc : List A), concat_acc_go ls acc = ls.flatten.reverseAux acc

#source_check "src/rocq/Utils/ListUtil.v|Vellvm.Utils.ListUtil|concat_acc_eq"
  concat_acc_eq : ∀ {A : Type u} (ls : List (List A)), concat_acc ls = ls.flatten

#source_check "src/rocq/Utils/ListUtil.v|Vellvm.Utils.ListUtil|map_acc_go_eq"
  map_acc_go_eq : ∀ {A : Type u} {B : Type v} (f : A → B) (l : List A) (acc : List B), map_acc_go f l acc = acc.reverseAux (l.map f)

#source_check "src/rocq/Utils/ListUtil.v|Vellvm.Utils.ListUtil|map_acc_eq"
  map_acc_eq : ∀ {A : Type u} {B : Type v} (f : A → B) (l : List A), map_acc f l = l.map f

#source_check "src/rocq/Utils/ListUtil.v|Vellvm.Utils.ListUtil|In_cons_dec"
  In_cons_dec : ∀ {A : Type u} (a x : A) (xs : List A), EqDecision A → a ∈ x :: xs → PSum (a = x) (a ∈ xs)

#source_check "src/rocq/Utils/ListUtil.v|Vellvm.Utils.ListUtil|fold_right_forall"
  fold_right_forall : ∀ {A : Type u} (P : A → Prop) (l : List A), l.foldr (fun x b ↦ P x ∧ b) True ↔ List.Forall P l

#source_check "src/rocq/Utils/ListUtil.v|Vellvm.Utils.ListUtil|list_cons_app"
  list_cons_app : ∀ {A : Type u} (x : A) (l : List A), x :: l = [x] ++ l

#source_check "src/rocq/Utils/ListUtil.v|Vellvm.Utils.ListUtil|not_in_app_l"
  not_in_app_l : ∀ {A : Type u} (l₁ l₂ : List A) (x : A), x ∉ l₁ ++ l₂ → x ∉ l₁

#source_check "src/rocq/Utils/ListUtil.v|Vellvm.Utils.ListUtil|not_in_app_r"
  not_in_app_r : ∀ {A : Type u} (l₁ l₂ : List A) (x : A), x ∉ l₁ ++ l₂ → x ∉ l₂

#source_check "src/rocq/Utils/ListUtil.v|Vellvm.Utils.ListUtil|find_none_app"
  find_none_app : ∀ {A : Type u} (l₁ l₂ : List A) (p : A → Bool), l₁.find? p = none → (l₁ ++ l₂).find? p = l₂.find? p

#source_check "src/rocq/Utils/ListUtil.v|Vellvm.Utils.ListUtil|find_some_app"
  find_some_app : ∀ {A : Type u} (l₁ l₂ : List A) (a : A) (p : A → Bool), l₁.find? p = some a → (l₁ ++ l₂).find? p = some a

#source_check "src/rocq/Utils/ListUtil.v|Vellvm.Utils.ListUtil|list_sum_map"
  list_sum_map : ∀ {A : Type u} (f : A → Nat) (x : A) (xs : List A), x ∈ xs → f x ≤ (xs.map f).sum

#source_check "src/rocq/Utils/ListUtil.v|Vellvm.Utils.ListUtil|forall_repeat_true"
  forall_repeat_true : ∀ (A : Type u) (f : A → Prop) (n : Nat) (x : A), f x → List.Forall f (List.replicate n x)

#source_check "src/rocq/Utils/ListUtil.v|Vellvm.Utils.ListUtil|Zseq_succ"
  Zseq_succ : ∀ (off : Int) (n : Nat), Zseq off (n+1) = off :: Zseq (off+1) n

#source_check "src/rocq/Utils/ListUtil.v|Vellvm.Utils.ListUtil|Zseq_length"
  Zseq_length : ∀ (len : Nat) (off : Int), (Zseq off len).length = len

#source_check "src/rocq/Utils/ListUtil.v|Vellvm.Utils.ListUtil|nat_double_acc_eq"
  nat_double_acc_eq : ∀ (n acc : Nat), nat_double_acc n acc = acc + 2*n

#source_check "src/rocq/Utils/ListUtil.v|Vellvm.Utils.ListUtil|nat_double_eq"
  nat_double_eq : ∀ (n : Nat), nat_double n = 2*n

#source_check "src/rocq/Utils/ListUtil.v|Vellvm.Utils.ListUtil|pos_to_nat_safe_eq"
  pos_to_nat_safe_eq : ∀ (p : Positive), pos_to_nat_safe p = p.val

#source_check "src/rocq/Utils/ListUtil.v|Vellvm.Utils.ListUtil|N_to_nat_safe_eq"
  N_to_nat_safe_eq : ∀ (n : Nat), N_to_nat_safe n = n

#source_check "src/rocq/Utils/ListUtil.v|Vellvm.Utils.ListUtil|seq_map_acc_go_eq"
  seq_map_acc_go_eq : ∀ {A : Type u} (f : Nat → A) (len : Nat) (acc : List A) (cur : Nat), seq_map_acc_go f acc cur len = acc.reverseAux ((Nseq cur len).map f)

#source_check "src/rocq/Utils/ListUtil.v|Vellvm.Utils.ListUtil|seq_map_acc_eq"
  seq_map_acc_eq : ∀ {A : Type u} (f : Nat → A) (start len : Nat), seq_map_acc f start len = (Nseq start len).map f

#source_check "src/rocq/Utils/ListUtil.v|Vellvm.Utils.ListUtil|repeat_acc_go_eq"
  repeat_acc_go_eq : ∀ {A : Type u} (x : A) (n : Nat) (acc : List A), repeat_acc_go x acc n = acc.reverseAux (List.replicate n x)

#source_check "src/rocq/Utils/ListUtil.v|Vellvm.Utils.ListUtil|repeat_acc_eq"
  repeat_acc_eq : ∀ {A : Type u} (x : A) (n : Nat), repeat_acc x n = List.replicate n x

#source_check "src/rocq/Utils/ListUtil.v|Vellvm.Utils.ListUtil|repeat_snoc"
  repeat_snoc : ∀ {A : Type u} (x : A) (k : Nat), List.replicate k x ++ [x] = x :: List.replicate k x

#source_check "src/rocq/Utils/ListUtil.v|Vellvm.Utils.ListUtil|rev_repeat"
  rev_repeat : ∀ {A : Type u} (x : A) (k : Nat), (List.replicate k x).reverse = List.replicate k x

#source_check "src/rocq/Utils/ListUtil.v|Vellvm.Utils.ListUtil|take_nil"
  take_nil : ∀ {A : Type u} (l : List A), take 0 l = []

#source_check "src/rocq/Utils/ListUtil.v|Vellvm.Utils.ListUtil|drop_nil"
  drop_nil : ∀ {A : Type u} (l : List A), drop 0 l = l

#source_check "src/rocq/Utils/ListUtil.v|Vellvm.Utils.ListUtil|take_length_le"
  take_length_le : ∀ {A : Type u} (l : List A) (n : Nat), (take n l).length ≤ n

#source_check "src/rocq/Utils/ListUtil.v|Vellvm.Utils.ListUtil|take_length_exact"
  take_length_exact : ∀ {A : Type u} (l : List A) (n : Nat), n ≤ l.length → (take n l).length = n

#source_check "src/rocq/Utils/ListUtil.v|Vellvm.Utils.ListUtil|take_all"
  take_all : ∀ {A : Type u} (l : List A) (n : Nat), l.length ≤ n → take n l = l

#source_check "src/rocq/Utils/ListUtil.v|Vellvm.Utils.ListUtil|drop_all"
  drop_all : ∀ {A : Type u} (l : List A) (n : Nat), l.length ≤ n → drop n l = []

#source_check "src/rocq/Utils/ListUtil.v|Vellvm.Utils.ListUtil|take_app_le"
  take_app_le : ∀ {A : Type u} (l r : List A) (n : Nat), n ≤ l.length → take n (l ++ r) = take n l

#source_check "src/rocq/Utils/ListUtil.v|Vellvm.Utils.ListUtil|drop_app_le"
  drop_app_le : ∀ {A : Type u} (l r : List A) (n : Nat), n ≤ l.length → drop n (l ++ r) = drop n l ++ r

#source_check "src/rocq/Utils/ListUtil.v|Vellvm.Utils.ListUtil|take_app_exact"
  take_app_exact : ∀ {A : Type u} (l r : List A) (n : Nat), l.length = n → take n (l ++ r) = l

#source_check "src/rocq/Utils/ListUtil.v|Vellvm.Utils.ListUtil|drop_app_exact"
  drop_app_exact : ∀ {A : Type u} (l r : List A) (n : Nat), l.length = n → drop n (l ++ r) = r

#source_check "src/rocq/Utils/ListUtil.v|Vellvm.Utils.ListUtil|rev_loop_acc_app"
  rev_loop_acc_app : ∀ {A : Type u} (f : Nat → A) (n i : Nat) (acc : List A), N.rev_loop_acc f n i acc = ((Nseq i n).map f).reverse ++ acc

#source_check "src/rocq/Utils/ListUtil.v|Vellvm.Utils.ListUtil|Nseq_length"
  Nseq_length : ∀ (len start : Nat), (Nseq start len).length = len

#source_check "src/rocq/Utils/ListUtil.v|Vellvm.Utils.ListUtil|In_Nseq"
  In_Nseq : ∀ (k s i : Nat), i ∈ Nseq s k → s ≤ i ∧ i < s+k

#source_check "src/rocq/Utils/ListUtil.v|Vellvm.Utils.ListUtil|Nseq_snoc"
  Nseq_snoc : ∀ (n s : Nat), Nseq s (n+1) = Nseq s n ++ [s+n]

#source_check "src/rocq/Utils/ListUtil.v|Vellvm.Utils.ListUtil|map_const_Nseq"
  map_const_Nseq : ∀ {A : Type u} (x : A) (k s : Nat), (Nseq s k).map (fun _ ↦ x) = List.replicate k x

#source_check "src/rocq/Utils/ListUtil.v|Vellvm.Utils.ListUtil|take_drop_app"
  take_drop_app : ∀ {A : Type u} (n : Nat) (l : List A), take n l ++ drop n l = l

#source_check "src/rocq/Utils/ListUtil.v|Vellvm.Utils.ListUtil|drop_drop"
  drop_drop : ∀ {A : Type u} (m n : Nat) (l : List A), drop m (drop n l) = drop (n+m) l

#source_check "src/rocq/Utils/ListUtil.v|Vellvm.Utils.ListUtil|length_drop_N"
  length_drop_N : ∀ {A : Type u} (l : List A) (n : Nat), (drop n l).length = l.length - n

#source_check "src/rocq/Utils/ListUtil.v|Vellvm.Utils.ListUtil|take_take_le"
  take_take_le : ∀ {A : Type u} (l : List A) (m k : Nat), m ≤ k → take m (take k l) = take m l

#source_check "src/rocq/Utils/ListUtil.v|Vellvm.Utils.ListUtil|drop_take"
  drop_take : ∀ {A : Type u} (l : List A) (n i : Nat), drop i (take n l) = take (n-i) (drop i l)

#source_check "src/rocq/Utils/ListUtil.v|Vellvm.Utils.ListUtil|forallb_take_pres"
  forallb_take_pres : ∀ {A : Type u} (f : A → Bool) (l : List A) (n : Nat), l.all f = true → (take n l).all f = true

#source_check "src/rocq/Utils/ListUtil.v|Vellvm.Utils.ListUtil|forallb_drop_pres"
  forallb_drop_pres : ∀ {A : Type u} (f : A → Bool) (l : List A) (n : Nat), l.all f = true → (drop n l).all f = true

#source_check "src/rocq/Utils/ListUtil.v|Vellvm.Utils.ListUtil|drop_length_le"
  drop_length_le : ∀ {A : Type u} (l : List A) (n : Nat), (drop n l).length ≤ l.length

#source_check "src/rocq/Utils/ListUtil.v|Vellvm.Utils.ListUtil|drop_length_lt"
  drop_length_lt : ∀ {A : Type u} (l : List A) (n : Nat), 1 ≤ n → l ≠ [] → (drop n l).length < l.length

#source_check "src/rocq/Utils/ListUtil.v|Vellvm.Utils.ListUtil|existsb_concat_map"
  existsb_concat_map : ∀ {A : Type u} {B : Type v} (f : B → Bool) (g : A → List B) (l : List A) (x : A), (l.map g).flatten.any f = false → x ∈ l → (g x).any f = false

#source_check "src/rocq/Utils/ListUtil.v|Vellvm.Utils.ListUtil|forallb_concat_map"
  forallb_concat_map : ∀ {A : Type u} {B : Type v} (f : B → Bool) (g : A → List B) (l : List A) (x : A), (l.map g).flatten.all f = true → x ∈ l → (g x).all f = true

#source_check "src/rocq/Utils/ListUtil.v|Vellvm.Utils.ListUtil|R_split_every_pos_complete"
  R_split_every_pos_complete : ∀ {A : Type u} (n : Positive) (xs : List A) (res : List (List A)), R_split_every_pos A n xs res → res = split_every_pos n xs

#source_check "src/rocq/Utils/ListUtil.v|Vellvm.Utils.ListUtil|R_split_every_pos_ind"
  R_split_every_pos_ind : ∀ (A : Type u) (n : Positive) (P : ∀ xs ys, R_split_every_pos A n xs ys → Prop),
    (∀ (xs : List A) (e : xs = []), P [] [] (@R_split_every_pos_0 A n xs e)) →
    (∀ (xs : List A) (x : A) (tl : List A) (e : xs = x :: tl) (res : List (List A)) (h : R_split_every_pos A n (drop n.val xs) res),
      P (drop n.val xs) res h → P (x :: tl) (take n.val xs :: res) (@R_split_every_pos_1 A n xs x tl e res h)) →
    ∀ xs ys (h : R_split_every_pos A n xs ys), P xs ys h

#source_check "src/rocq/Utils/ListUtil.v|Vellvm.Utils.ListUtil|R_split_every_pos_sind"
  R_split_every_pos_sind : ∀ (A : Type u) (n : Positive) (P : ∀ xs ys, R_split_every_pos A n xs ys → Prop),
    (∀ (xs : List A) (e : xs = []), P [] [] (@R_split_every_pos_0 A n xs e)) →
    (∀ (xs : List A) (x : A) (tl : List A) (e : xs = x :: tl) (res : List (List A)) (h : R_split_every_pos A n (drop n.val xs) res),
      P (drop n.val xs) res h → P (x :: tl) (take n.val xs :: res) (@R_split_every_pos_1 A n xs x tl e res h)) →
    ∀ xs ys (h : R_split_every_pos A n xs ys), P xs ys h

#source_check "src/rocq/Utils/ListUtil.v|Vellvm.Utils.ListUtil|split_every_pos_equation"
  split_every_pos_equation : ∀ {A : Type u} (n : Positive) (xs : List A), split_every_pos n xs = match xs with
      | [] => []
      | _ :: _ => take n.val xs :: split_every_pos n (drop n.val xs)

#source_check "src/rocq/Utils/ListUtil.v|Vellvm.Utils.ListUtil|split_every_pos_ind"
  split_every_pos_ind : ∀ {A : Type u} (n : Positive) (P : List A → List (List A) → Prop),
    (∀ (xs : List A), xs = [] → P [] []) →
    (∀ (xs : List A) (x : A) (tl : List A), xs = x :: tl → P (drop n.val xs) (split_every_pos n (drop n.val xs)) →
      P (x :: tl) (take n.val xs :: split_every_pos n (drop n.val xs))) → ∀ xs, P xs (split_every_pos n xs)

#source_check "src/rocq/Utils/ListUtil.v|Vellvm.Utils.ListUtil|split_every_pos_tcc"
  split_every_pos_tcc : ∀ {A : Type u} (n : Positive) (xs : List A) (a : A) (l : List A), xs = a :: l → (drop n.val (a :: l)).length < (a :: l).length

#source_check "src/rocq/Utils/ListUtil.v|Vellvm.Utils.ListUtil|In_take_N"
  In_take_N : ∀ {A : Type u} (n : Nat) (l : List A) (x : A), x ∈ take n l → x ∈ l

#source_check "src/rocq/Utils/ListUtil.v|Vellvm.Utils.ListUtil|In_drop_N"
  In_drop_N : ∀ {A : Type u} (n : Nat) (l : List A) (x : A), x ∈ drop n l → x ∈ l

#source_check "src/rocq/Utils/ListUtil.v|Vellvm.Utils.ListUtil|Forall_take_N"
  Forall_take_N : ∀ {A : Type u} (P : A → Prop) (n : Nat) (l : List A), List.Forall P l → List.Forall P (take n l)

#source_check "src/rocq/Utils/ListUtil.v|Vellvm.Utils.ListUtil|Forall_drop_N"
  Forall_drop_N : ∀ {A : Type u} (P : A → Prop) (n : Nat) (l : List A), List.Forall P l → List.Forall P (drop n l)

#source_check "src/rocq/Utils/ListUtil.v|Vellvm.Utils.ListUtil|take_repeat_cons"
  take_repeat_cons : ∀ {A : Type u} (x : A) (n k : Nat), 0 < n → 0 < k → ∃ r, take n (List.replicate k x) = x :: r

#source_check "src/rocq/Utils/ListUtil.v|Vellvm.Utils.ListUtil|In_rev_loop_acc"
  In_rev_loop_acc : ∀ {A : Type u} (f : Nat → A) (n i : Nat) (acc : List A) (b : A), b ∈ N.rev_loop_acc f n i acc → b ∈ acc ∨ ∃ j, b = f j

#source_check "src/rocq/Utils/ListUtil.v|Vellvm.Utils.ListUtil|map_Nseq_shift"
  map_Nseq_shift : ∀ {A : Type u} (f : Nat → A) (n a s : Nat), (Nseq a n).map (fun i ↦ f (s+i)) = (Nseq (s+a) n).map f

#source_check "src/rocq/Utils/ListUtil.v|Vellvm.Utils.ListUtil|map_Nseq_nth"
  map_Nseq_nth : ∀ {A : Type u} (l : List A) (d : A) (s : Nat), (Nseq s l.length).map (fun i ↦ l.getD (i-s) d) = l

#source_check "src/rocq/Utils/ListUtil.v|Vellvm.Utils.ListUtil|fold_left_add_right"
  fold_left_add_right : ∀ {A : Type u} (f : A → Nat) (l : List A) (a : Nat), l.foldl (fun acc dt ↦ acc + f dt) a = a + l.foldr (fun dt acc ↦ f dt + acc) 0

#source_check "src/rocq/Utils/ListUtil.v|Vellvm.Utils.ListUtil|length_take"
  length_take : ∀ {A : Type u} {B : Type v} (l : List A) (l' : List B) (n : Nat), l.length = l'.length → (take n l).length = (take n l').length

#source_check "src/rocq/Utils/ListUtil.v|Vellvm.Utils.ListUtil|length_drop"
  length_drop : ∀ {A : Type u} {B : Type v} (l : List A) (l' : List B) (n : Nat), l.length = l'.length → (drop n l).length = (drop n l').length

#source_check "src/rocq/Utils/ListUtil.v|Vellvm.Utils.ListUtil|zip_acc_go_eq"
  zip_acc_go_eq : ∀ {A : Type u} {B : Type v} (xs : List A) (ys : List B) (acc : List (A × B)), zip_acc_go acc xs ys = acc.reverseAux (zip xs ys)

#source_check "src/rocq/Utils/ListUtil.v|Vellvm.Utils.ListUtil|zip_acc_eq"
  zip_acc_eq : ∀ {A : Type u} {B : Type v} (xs : List A) (ys : List B), zip_acc xs ys = zip xs ys

#source_check "src/rocq/Utils/ListUtil.v|Vellvm.Utils.ListUtil|FORALL_forall"
  FORALL_forall : ∀ {A : Type u} (P : A → Prop) (l : List A), FORALL P l ↔ List.Forall P l

#source_check "src/rocq/Utils/ListUtil.v|Vellvm.Utils.ListUtil|FORALL_dec"
  FORALL_dec : ∀ {A : Type u} (P : A → Prop) (l : List A), (∀ x ∈ l, PSum (P x) (¬ P x)) → PSum (FORALL P l) (¬ FORALL P l)

#source_check "src/rocq/Utils/ListUtil.v|Vellvm.Utils.ListUtil|list_disjoint_nil_l"
  list_disjoint_nil_l : ∀ {A : Type u} (l : List A), list_disjoint [] l

#source_check "src/rocq/Utils/ListUtil.v|Vellvm.Utils.ListUtil|list_disjoint_nil_r"
  list_disjoint_nil_r : ∀ {A : Type u} (l : List A), list_disjoint l []

#source_check "src/rocq/Utils/ListUtil.v|Vellvm.Utils.ListUtil|list_disjoint_cons_l_iff"
  list_disjoint_cons_l_iff : ∀ (A : Type u) (a : A) (l₁ l₂ : List A), list_disjoint (a :: l₁) l₂ ↔ list_disjoint l₁ l₂ ∧ a ∉ l₂

#source_check "src/rocq/Utils/ListUtil.v|Vellvm.Utils.ListUtil|list_disjoint_singleton_left"
  list_disjoint_singleton_left : ∀ {A : Type u} (l : List A) (x : A), list_disjoint [x] l ↔ x ∉ l

#source_check "src/rocq/Utils/ListUtil.v|Vellvm.Utils.ListUtil|list_disjoint_singleton_right"
  list_disjoint_singleton_right : ∀ {A : Type u} (l : List A) (x : A), list_disjoint l [x] ↔ x ∉ l

#source_check "src/rocq/Utils/ListUtil.v|Vellvm.Utils.ListUtil|list_disjoint_app_l"
  list_disjoint_app_l : ∀ {A : Type u} (l₁ l₂ l₃ : List A), list_disjoint (l₁ ++ l₂) l₃ ↔ list_disjoint l₁ l₃ ∧ list_disjoint l₂ l₃

#source_check "src/rocq/Utils/ListUtil.v|Vellvm.Utils.ListUtil|list_disjoint_app_r"
  list_disjoint_app_r : ∀ {A : Type u} (l₁ l₂ l₃ : List A), list_disjoint l₁ (l₂ ++ l₃) ↔ list_disjoint l₁ l₂ ∧ list_disjoint l₁ l₃

#source_check "src/rocq/Utils/ListUtil.v|Vellvm.Utils.ListUtil|list_disjoint_singletons"
  list_disjoint_singletons : ∀ {A : Type u} (x y : A), list_disjoint [x] [y] ↔ x ≠ y

#source_check "src/rocq/Utils/ListUtil.v|Vellvm.Utils.ListUtil|Forall_disjoint"
  Forall_disjoint : ∀ {A : Type u} (l₁ l₂ : List A) (P Q : A → Prop), List.Forall P l₁ → List.Forall Q l₂ → (∀ x, P x → ¬ Q x) → list_disjoint l₁ l₂

#source_check "src/rocq/Utils/ListUtil.v|Vellvm.Utils.ListUtil|Forall2_repeat"
  Forall2_repeat : ∀ {A : Type u} {B : Type v} (R : A → B → Prop) (a : A) (b : B) (n : Nat), R a b → List.Forall₂ R (List.replicate n a) (List.replicate n b)

#source_check "src/rocq/Utils/ListUtil.v|Vellvm.Utils.ListUtil|Forall2_diag"
  Forall2_diag : ∀ {A : Type u} (P : A → A → Prop) (l : List A), List.Forall₂ P l l ↔ List.Forall (fun a ↦ P a a) l

#source_check "src/rocq/Utils/ListUtil.v|Vellvm.Utils.ListUtil|Forall2_combine"
  Forall2_combine : ∀ {A : Type u} {B : Type v} {C : Type w} {D : Type z} (RA : A → B → Prop) (RB : C → D → Prop) (l₁ : List A) (l₂ : List B) (k₁ : List C) (k₂ : List D), List.Forall₂ RA l₁ l₂ → List.Forall₂ RB k₁ k₂ → List.Forall₂ (prod_rel RA RB) (l₁.zip k₁) (l₂.zip k₂)

#source_check "src/rocq/Utils/ListUtil.v|Vellvm.Utils.ListUtil|Forall2_length_N_h"
  Forall2_length_N_h : ∀ {A : Type u} {B : Type v} (R : A → B → Prop) (l₁ : List A) (l₂ : List B) (acc : Nat), List.Forall₂ R l₁ l₂ → N.length_h l₁ acc = N.length_h l₂ acc

#source_check "src/rocq/Utils/ListUtil.v|Vellvm.Utils.ListUtil|Forall2_length_N"
  Forall2_length_N : ∀ {A : Type u} {B : Type v} (R : A → B → Prop) (l₁ : List A) (l₂ : List B), List.Forall₂ R l₁ l₂ → N.length l₁ = N.length l₂

#source_check "src/rocq/Utils/ListUtil.v|Vellvm.Utils.ListUtil|Forall2_map2"
  Forall2_map2 : ∀ {A : Type u} {B : Type v} {C : Type w} (R : B → C → Prop) (f : A → B) (g : A → C) (l : List A), (∀ x ∈ l, R (f x) (g x)) → List.Forall₂ R (l.map f) (l.map g)

#source_check "src/rocq/Utils/ListUtil.v|Vellvm.Utils.ListUtil|Forall2_take"
  Forall2_take : ∀ {A : Type u} {B : Type v} (R : A → B → Prop) (l₁ : List A) (l₂ : List B), List.Forall₂ R l₁ l₂ → ∀ n, List.Forall₂ R (take n l₁) (take n l₂)

#source_check "src/rocq/Utils/ListUtil.v|Vellvm.Utils.ListUtil|Forall2_drop"
  Forall2_drop : ∀ {A : Type u} {B : Type v} (R : A → B → Prop) (l₁ : List A) (l₂ : List B), List.Forall₂ R l₁ l₂ → ∀ n, List.Forall₂ R (drop n l₁) (drop n l₂)

#source_check "src/rocq/Utils/ListUtil.v|Vellvm.Utils.ListUtil|Forall2_repeatN"
  Forall2_repeatN : ∀ {A : Type u} {B : Type v} (R : A → B → Prop) (a : A) (b : B), R a b → ∀ n, List.Forall₂ R (repeatN n a) (repeatN n b)

#source_check "src/rocq/Utils/ListUtil.v|Vellvm.Utils.ListUtil|Forall2_eq"
  Forall2_eq : ∀ {A : Type u} (l₁ l₂ : List A), List.Forall₂ Eq l₁ l₂ → l₁ = l₂

#source_check "src/rocq/Utils/ListUtil.v|Vellvm.Utils.ListUtil|eq_Forall2"
  eq_Forall2 : ∀ {A : Type u} (l : List A), List.Forall₂ Eq l l

#source_check "src/rocq/Utils/ListUtil.v|Vellvm.Utils.ListUtil|Forall2_filter"
  Forall2_filter : ∀ {A : Type u} {B : Type v} (R : A → B → Prop) (p : A → Bool) (q : B → Bool), (∀ a b, R a b → p a = q b) → ∀ (l₁ : List A) (l₂ : List B), List.Forall₂ R l₁ l₂ → List.Forall₂ R (l₁.filter p) (l₂.filter q)

#source_check "src/rocq/Utils/ListUtil.v|Vellvm.Utils.ListUtil|Forall2_concat"
  Forall2_concat : ∀ {A : Type u} {B : Type v} (R : A → B → Prop) (ls₁ : List (List A)) (ls₂ : List (List B)), List.Forall₂ (List.Forall₂ R) ls₁ ls₂ → List.Forall₂ R ls₁.flatten ls₂.flatten

#source_check "src/rocq/Utils/ListUtil.v|Vellvm.Utils.ListUtil|Forall2_zip"
  Forall2_zip : ∀ {A : Type u} {B : Type v} {C : Type w} {D : Type z} (RA : A → B → Prop) (RB : C → D → Prop) (l₁ : List A) (l₂ : List B), List.Forall₂ RA l₁ l₂ → ∀ (k₁ : List C) (k₂ : List D), List.Forall₂ RB k₁ k₂ → List.Forall₂ (prod_rel RA RB) (zip l₁ k₁) (zip l₂ k₂)

#source_check "src/rocq/Utils/ListUtil.v|Vellvm.Utils.ListUtil|Forall2_split_every_pos"
  Forall2_split_every_pos : ∀ {A : Type u} {B : Type v} (R : A → B → Prop) (n : Positive) (k : Nat) (l₁ : List A) (l₂ : List B), l₁.length ≤ k → List.Forall₂ R l₁ l₂ → List.Forall₂ (List.Forall₂ R) (split_every_pos n l₁) (split_every_pos n l₂)

#source_check "src/rocq/Utils/ListUtil.v|Vellvm.Utils.ListUtil|Forall2_split_every_nil"
  Forall2_split_every_nil : ∀ {A : Type u} {B : Type v} (R : A → B → Prop) (n : Nat) (l₁ : List A) (l₂ : List B), List.Forall₂ R l₁ l₂ → List.Forall₂ (List.Forall₂ R) (split_every_nil n l₁) (split_every_nil n l₂)

#source_check "src/rocq/Utils/ListUtil.v|Vellvm.Utils.ListUtil|Forall2_nth_error"
  Forall2_nth_error : ∀ {A : Type u} {B : Type v} (R : A → B → Prop) (l₁ : List A) (l₂ : List B), List.Forall₂ R l₁ l₂ → ∀ n : Nat, match l₁[n]?, l₂[n]? with
      | some a, some b => R a b
      | none, none => True
      | _, _ => False

#source_check "src/rocq/Utils/ListUtil.v|Vellvm.Utils.ListUtil|Forall2_map_rel"
  Forall2_map_rel : ∀ {A : Type u} {B : Type v} {C : Type w} {D : Type z} (RA : A → B → Prop) (RB : C → D → Prop) (f : A → C) (g : B → D), (∀ a b, RA a b → RB (f a) (g b)) → ∀ (l₁ : List A) (l₂ : List B), List.Forall₂ RA l₁ l₂ → List.Forall₂ RB (l₁.map f) (l₂.map g)

#source_check "src/rocq/Utils/ListUtil.v|Vellvm.Utils.ListUtil|Forall2_rev_append"
  Forall2_rev_append : ∀ {A : Type u} {B : Type v} (R : A → B → Prop) (l₁ : List A) (l₂ : List B), List.Forall₂ R l₁ l₂ → ∀ (m₁ : List A) (m₂ : List B), List.Forall₂ R m₁ m₂ → List.Forall₂ R (l₁.reverseAux m₁) (l₂.reverseAux m₂)

#source_check "src/rocq/Utils/ListUtil.v|Vellvm.Utils.ListUtil|Forall2_nth_Nseq"
  Forall2_nth_Nseq : ∀ {A : Type u} {B : Type v} (R : A → B → Prop) (f : Nat → B) (d : A) (l : List A) (s : Nat), (∀ i, i < l.length → R (l.getD i d) (f (s+i))) → List.Forall₂ R l ((Nseq s l.length).map f)

#source_check "src/rocq/Utils/ListUtil.v|Vellvm.Utils.ListUtil|Forall2_rev_loop_acc"
  Forall2_rev_loop_acc : ∀ {A : Type u} {B : Type v} (R : A → B → Prop) (f : Nat → A) (g : Nat → B), (∀ i, R (f i) (g i)) → ∀ (n i : Nat) (xs : List A) (ys : List B), List.Forall₂ R xs ys → List.Forall₂ R (N.rev_loop_acc f n i xs) (N.rev_loop_acc g n i ys)

#source_check "src/rocq/Utils/ListUtil.v|Vellvm.Utils.ListUtil|sequence_cons"
  sequence_cons : ∀ {m : Type u → Type v} [Monad m] {A : Type u} (ma : m A) (mas : List (m A)), sequence (ma :: mas) = (ma >>= fun x ↦ sequence mas >>= fun xs ↦ pure (x :: xs))

#source_check "src/rocq/Utils/ListUtil.v|Vellvm.Utils.ListUtil|eqit_map_monad"
  eqit_map_monad : ∀ {E B : ITree.Effect.{u}} {X Y : Type u} {A : Type v} {C : Type w} {b₁ b₂ : Bool} (RR : X → Y → Prop) (f : A → CTree.CTree E B X) (g : C → CTree.CTree E B Y) (l : List A) (r : List C), List.Forall₂ (fun a b ↦ eqit RR b₁ b₂ (f a) (g b)) l r → eqit (List.Forall₂ RR) b₁ b₂ (map_monad f l) (map_monad g r)

#source_check "src/rocq/Utils/ListUtil.v|Vellvm.Utils.ListUtil|eqit_map_monad'"
  eqit_map_monad' : ∀ {E B : ITree.Effect.{u}} {X : Type u} {A : Type v} {b₁ b₂ : Bool} (f g : A → CTree.CTree E B X) (l r : List A), List.Forall₂ (fun a b ↦ eqit Eq b₁ b₂ (f a) (g b)) l r → eqit Eq b₁ b₂ (map_monad f l) (map_monad g r)
