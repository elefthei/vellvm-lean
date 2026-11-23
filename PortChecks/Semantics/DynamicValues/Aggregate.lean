import PortChecks.SourceType
import Vellvm.Semantics.DynamicValues.Aggregate

open Vellvm.Semantics.DynamicValues

universe u v

#source_check "src/rocq/Semantics/DynamicValues.v|Vellvm.Semantics.DynamicValues|split_acc_go_eq"
  split_acc_go_eq : ∀ {A : Type u} (l : List A) (idx : Int) (rev_pre : List A),
    split_acc_go rev_pre idx l = split_h (rev_pre.reverseAux []) idx l

#source_check "src/rocq/Semantics/DynamicValues.v|Vellvm.Semantics.DynamicValues|split_acc_eq"
  split_acc_eq : ∀ {A : Type u} (idx : Int) (l : List A), split_acc idx l = split [] idx l

#source_check "src/rocq/Semantics/DynamicValues.v|Vellvm.Semantics.DynamicValues|Forall2_split_h"
  Forall2_split_h : ∀ {A : Type u} {B : Type v} (R : A → B → Prop) (i : Int)
    (l1 : List A) (l2 : List B), List.Forall₂ R l1 l2 → ∀ (pre1 : List A) (pre2 : List B),
    List.Forall₂ R pre1 pre2 →
    match split_h pre1 i l1, split_h pre2 i l2 with
    | some ((p1, x1), q1), some ((p2, x2), q2) =>
      List.Forall₂ R p1 p2 ∧ R x1 x2 ∧ List.Forall₂ R q1 q2
    | none, none => True
    | _, _ => False

#source_check "src/rocq/Semantics/DynamicValues.v|Vellvm.Semantics.DynamicValues|Forall2_split"
  Forall2_split : ∀ {A : Type u} {B : Type v} (R : A → B → Prop) (i : Int)
    (l1 : List A) (l2 : List B), List.Forall₂ R l1 l2 →
    match split [] i l1, split [] i l2 with
    | some ((p1, x1), q1), some ((p2, x2), q2) =>
      List.Forall₂ R p1 p2 ∧ R x1 x2 ∧ List.Forall₂ R q1 q2
    | none, none => True
    | _, _ => False
