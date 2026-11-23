import Vellvm.Semantics.DynamicValues.Canonical
import Vellvm.Semantics.DynamicValues.Show

namespace Vellvm.Semantics.DynamicValues

universe u v

def split_h {A : Type u} (pre : List A) (idx : Int) : List A → Option ((List A × A) × List A)
  | [] => none
  | h :: tl => if idx = 0 then some ((pre, h), tl) else split_h (pre ++ [h]) (idx - 1) tl

def split {A : Type u} (pre : List A) (idx : Int) (l : List A) : Option ((List A × A) × List A) :=
  if idx < 0 then none else split_h pre idx l

def split_acc_go {A : Type u} (rev_pre : List A) (idx : Int) : List A → Option ((List A × A) × List A)
  | [] => none
  | h :: tl =>
    if idx = 0 then some ((rev_pre.reverseAux [], h), tl) else split_acc_go (h :: rev_pre) (idx - 1) tl

def split_acc {A : Type u} (idx : Int) (l : List A) : Option ((List A × A) × List A) :=
  if idx < 0 then none else split_acc_go [] idx l

theorem split_acc_go_eq {A : Type u} (l : List A) (idx : Int) (rev_pre : List A) :
    split_acc_go rev_pre idx l = split_h (rev_pre.reverseAux []) idx l := by
  induction l generalizing idx rev_pre with
  | nil => rfl
  | cons h tl ih =>
    by_cases hz : idx = 0
    · simp only [split_acc_go, split_h, ite_eq_left hz]
    · simp only [split_acc_go, split_h, ite_eq_right hz]
      rw [ih]
      exact congrArg (fun p ↦ split_h p (idx - 1) tl) List.reverse_cons

theorem split_acc_eq {A : Type u} (idx : Int) (l : List A) : split_acc idx l = split [] idx l := by
  simp only [split_acc, split, split_acc_go_eq, List.reverseAux]

theorem Forall2_split_h {A : Type u} {B : Type v} (R : A → B → Prop) (i : Int)
    (l1 : List A) (l2 : List B) (hl : List.Forall₂ R l1 l2) (pre1 : List A) (pre2 : List B)
    (hp : List.Forall₂ R pre1 pre2) :
    match split_h pre1 i l1, split_h pre2 i l2 with
    | some ((p1, x1), q1), some ((p2, x2), q2) =>
      List.Forall₂ R p1 p2 ∧ R x1 x2 ∧ List.Forall₂ R q1 q2
    | none, none => True
    | _, _ => False := by
  induction hl generalizing i pre1 pre2 with
  | nil => trivial
  | cons hx htl ih =>
    by_cases hz : i = 0
    · simpa only [split_h, ite_eq_left hz] using And.intro hp (And.intro hx htl)
    · simp only [split_h, ite_eq_right hz]
      exact ih (i - 1) _ _ (List.rel_append hp (.cons hx .nil))

theorem Forall2_split {A : Type u} {B : Type v} (R : A → B → Prop) (i : Int)
    (l1 : List A) (l2 : List B) (hl : List.Forall₂ R l1 l2) :
    match split [] i l1, split [] i l2 with
    | some ((p1, x1), q1), some ((p2, x2), q2) =>
      List.Forall₂ R p1 p2 ∧ R x1 x2 ∧ List.Forall₂ R q1 q2
    | none, none => True
    | _, _ => False := by
  by_cases hn : i < 0
  · simp only [split, ite_eq_left hn]
  · simpa only [split, ite_eq_right hn] using Forall2_split_h R i l1 l2 hl [] [] .nil

def split_indices (idx : Int) (sz : Nat) : Option (Nat × Nat) :=
  if idx < 0 then none else
  if idx < (sz : Int) then some (idx.toNat, ((sz : Int) - (idx + 1)).toNat) else none

open Interfaces.Params Syntax.DynamicTypes Utils.ListUtil EOU

variable [Pa : Params]

def insert_value (str_t : dtyp) (str elt : dvalue) (idxs : List Int) : EOU dvalue :=
  match idxs with
  | [] => pure elt
  | i :: tl =>
    match str_t with
    | DTYPE_Struct _ ts => do
      let ((pre_t, sub_t), post_t) ← option_ub "insertvalue: struct type size inconsistency".toUTF8
        (split [] i ts)
      match str with
      | DVALUE_Struct _ elts =>
        let ((pre, sub), post) ← option_ub "insertvalue: struct dynamic index out of bounds".toUTF8
          (split [] i elts)
        let field ← insert_value sub_t sub elt tl
        return canonicalize_agg str_t (pre ++ field :: post)
      | DVALUE_Base DVALUE_Poison =>
        let field ← insert_value sub_t (poison_of_dtyp sub_t) elt tl
        return canonicalize_agg str_t (pre_t.map poison_of_dtyp ++ field :: post_t.map poison_of_dtyp)
      | _ => raise_error "insertvalue: type mismatch, found non-struct value".toUTF8
    | DTYPE_Array false sz t =>
      match str with
      | DVALUE_Array false elts => do
        let ((pre, sub), post) ← option_ub "insertvalue array index out of bounds".toUTF8
          (split [] i elts)
        let field ← insert_value t sub elt tl
        return canonicalize_agg str_t (pre ++ field :: post)
      | DVALUE_Base DVALUE_Poison => do
        let (pre, post) ← option_ub "insertvalue: array type size inconsistency".toUTF8
          (split_indices i sz)
        let poison := poison_of_dtyp t
        let field ← insert_value t poison elt tl
        return canonicalize_agg str_t (repeatN pre poison ++ field :: repeatN post poison)
      | _ => raise_error "insertvalue: type mismatch, found non-array value".toUTF8
    | DTYPE_Array true _ _ => raise_error "insertvalue: type mismatch, found vector type".toUTF8
    | DTYPE_Base _ => raise_error "insertvalue: type mismatch, found base type".toUTF8
termination_by structural idxs

def extract_value (str_t : dtyp) (str : dvalue) (idxs : List Int) : EOU dvalue :=
  match idxs with
  | [] => pure str
  | i :: tl =>
    match str_t with
    | DTYPE_Struct _ ts => do
      let ((_, sub_t), _) ← option_ub "extractvalue: struct type size inconsistency".toUTF8
        (split [] i ts)
      match str with
      | DVALUE_Struct _ elts =>
        let ((_, sub), _) ← option_ub "extractvalue: struct dynamic index out of bounds".toUTF8
          (split [] i elts)
        extract_value sub_t sub tl
      | DVALUE_Base DVALUE_Poison => extract_value sub_t (poison_of_dtyp sub_t) tl
      | _ => raise_error "extractvalue: type mismatch, found non-struct value".toUTF8
    | DTYPE_Array false _ t =>
      match str with
      | DVALUE_Array false elts => do
        let ((_, sub), _) ← option_ub "extractvalue array index out of bounds".toUTF8
          (split [] i elts)
        extract_value t sub tl
      | DVALUE_Base DVALUE_Poison => extract_value t (poison_of_dtyp t) tl
      | _ => raise_error "extractvalue: type mismatch, found non-array value".toUTF8
    | DTYPE_Array true _ _ => raise_error "extractvalue: type mismatch, found vector type".toUTF8
    | DTYPE_Base _ => raise_error "extractvalue: type mismatch, found base type".toUTF8
termination_by structural idxs

def vector_index : dvalue → Option Int
  | DVALUE_Base (DVALUE_I _ x) => some (Numeric.Integers.unsigned x)
  | _ => none

def extract_element (vec idx : dvalue) : EOU dvalue :=
  match vec with
  | DVALUE_Array true [] | DVALUE_Base DVALUE_Poison => pure (DVALUE_Base DVALUE_Poison)
  | DVALUE_Array true elts =>
    match vector_index idx with
    | some i =>
      match split_acc i elts with
      | some ((_, elt), _) => pure elt
      | none => pure (DVALUE_Base DVALUE_Poison)
    | none =>
      match idx with
      | DVALUE_Base DVALUE_Poison => pure (DVALUE_Base DVALUE_Poison)
      | _ => raise_error "extractelemnt: non-integer index".toUTF8
  | _ => raise_error "extractelement: non-vector value".toUTF8

def insert_element (vec_t : dtyp) (vec elt idx : dvalue) : EOU dvalue :=
  match vec_t with
  | DTYPE_Array true sz _ =>
    match vector_elts sz vec with
    | some elts =>
      match vector_index idx with
      | some i =>
        match split_acc i elts with
        | some ((pre, _), post) => pure (canonicalize_agg vec_t (pre ++ elt :: post))
        | none => pure (DVALUE_Base DVALUE_Poison)
      | none =>
        match idx with
        | DVALUE_Base DVALUE_Poison => pure (DVALUE_Base DVALUE_Poison)
        | _ => raise_error "insertelement: non-integer index".toUTF8
    | none => raise_error ("insertelement: non-vector value ".toUTF8 ++ show_dvalue vec)
  | _ => raise_error ("insertelemnt: non-vector type".toUTF8 ++ Syntax.ShowAST.show_dtyp vec_t)

def shuffle_vector (vec_t : dtyp) (vec1 vec2 mask : dvalue) : EOU dvalue :=
  match vec_t with
  | DTYPE_Array true sz t =>
    match vector_elts sz vec1, vector_elts sz vec2, mask with
    | some elts1, some elts2, DVALUE_Array true idxs =>
      let combined := elts1 ++ elts2
      let lane := fun idx ↦
        match vector_index idx with
        | some i => combined.getD i.toNat (DVALUE_Base DVALUE_Poison)
        | none => DVALUE_Base DVALUE_Poison
      pure (canonicalize_agg (DTYPE_Array true idxs.length t) (idxs.map lane))
    | _, _, DVALUE_Base DVALUE_Poison => pure (DVALUE_Base DVALUE_Poison)
    | _, _, _ => raise_error "shufflevector: non-vector operand value".toUTF8
  | _ => raise_error "shufflevector: non-vector operand type".toUTF8

end Vellvm.Semantics.DynamicValues
