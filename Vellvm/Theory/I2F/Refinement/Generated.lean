module

public import Vellvm.Theory.I2F.Refinement.Events
public import Vellvm.Theory.I2F.Refinement.Schemes

@[expose] public section
namespace Vellvm.Theory.I2F.Refinement
open Vellvm Vellvm.Semantics Vellvm.Semantics.DynamicValues Vellvm.Semantics.LLVMEvents
open Vellvm.Syntax.LLVMAst Vellvm.Syntax.DynamicTypes

universe u

theorem I2FE_Call_equation_1 :
    (∀ (τ1 : dtyp) (cc1 : cconv) (f1 : (@dvalue PInf)) (args1 : (List (Prod dtyp (@dvalue PInf))))
    (τ2 : dtyp) (cc2 : cconv) (f2 : (@dvalue PFin)) (args2 : (List (Prod dtyp (@dvalue PFin)))), (Eq
    (I2FE_Call (@Call PInf τ1 cc1 f1 args1) (@Call PFin τ2 cc2 f2 args2)) (And (Eq τ1 τ2) (And (Eq
    cc1 cc2) (And (I2F_dvalue f1 f2) (I2F_targs args1 args2)))))) := by intros; rfl

inductive I2FE_Call_graph :
    (∀ (e : (@CallE PInf).I) (f : (@CallE PFin).I) (_ : Prop), Type) where
  | case1 :
      (∀ (τ1 : dtyp) (cc1 : cconv) (f1 : (@dvalue PInf)) (args1 : (List (Prod dtyp (@dvalue PInf))))
      (τ2 : dtyp) (cc2 : cconv) (f2 : (@dvalue PFin)) (args2 : (List (Prod dtyp (@dvalue PFin)))),
      (I2FE_Call_graph (@Call PInf τ1 cc1 f1 args1) (@Call PFin τ2 cc2 f2 args2) (And (Eq τ1 τ2)
      (And (Eq cc1 cc2) (And (I2F_dvalue f1 f2) (I2F_targs args1 args2))))))

abbrev I2FE_Call_graph_equation_1 := @I2FE_Call_graph.case1

def I2FE_Call_graph_rect :
    (∀ (P : (∀ (e : (@CallE PInf).I) (f : (@CallE PFin).I) (_ : Prop), Type u)) (_ : (∀ (τ1 : dtyp)
    (cc1 : cconv) (f1 : (@dvalue PInf)) (args1 : (List (Prod dtyp (@dvalue PInf)))) (τ2 : dtyp) (cc2
    : cconv) (f2 : (@dvalue PFin)) (args2 : (List (Prod dtyp (@dvalue PFin)))), (P (@Call PInf τ1
    cc1 f1 args1) (@Call PFin τ2 cc2 f2 args2) (And (Eq τ1 τ2) (And (Eq cc1 cc2) (And (I2F_dvalue f1
    f2) (I2F_targs args1 args2))))))) {c : (@CallE PInf).I} {c0 : (@CallE PFin).I} {P0 : Prop} (_ :
    (I2FE_Call_graph c c0 P0)), (P c c0 P0)) := by
  intro P h1 e f p witness
  cases witness
  next => apply h1

def I2FE_Call_graph_correct :
    (∀ (c : (@CallE PInf).I) (c0 : (@CallE PFin).I), (I2FE_Call_graph c c0 (I2FE_Call c c0))) := by
  intro e f
  cases e <;> cases f <;> first
    | apply I2FE_Call_graph.case1

def I2FE_Call_elim :
    (∀ (P : (∀ (e : (@CallE PInf).I) (f : (@CallE PFin).I) (_ : Prop), Type u)) (_ : (∀ (τ1 : dtyp)
    (cc1 : cconv) (f1 : (@dvalue PInf)) (args1 : (List (Prod dtyp (@dvalue PInf)))) (τ2 : dtyp) (cc2
    : cconv) (f2 : (@dvalue PFin)) (args2 : (List (Prod dtyp (@dvalue PFin)))), (P (@Call PInf τ1
    cc1 f1 args1) (@Call PFin τ2 cc2 f2 args2) (And (Eq τ1 τ2) (And (Eq cc1 cc2) (And (I2F_dvalue f1
    f2) (I2F_targs args1 args2))))))) (c : (@CallE PInf).I) (c0 : (@CallE PFin).I), (P c c0
    (I2FE_Call c c0))) := by
  intro P h1 e f
  exact I2FE_Call_graph_rect P h1 (I2FE_Call_graph_correct e f)

instance FunctionalInduction_I2FE_Call :
    (FunctionalInduction.{0, 0} I2FE_Call) := ⟨_, I2FE_Call_graph_correct⟩

instance FunctionalElimination_I2FE_Call :
    FunctionalElimination I2FE_Call (∀ (P : (∀ (e : (@CallE PInf).I) (f : (@CallE PFin).I) (_ : Prop), Type u)) (_ : (∀ (τ1 : dtyp)
    (cc1 : cconv) (f1 : (@dvalue PInf)) (args1 : (List (Prod dtyp (@dvalue PInf)))) (τ2 : dtyp) (cc2
    : cconv) (f2 : (@dvalue PFin)) (args2 : (List (Prod dtyp (@dvalue PFin)))), (P (@Call PInf τ1
    cc1 f1 args1) (@Call PFin τ2 cc2 f2 args2) (And (Eq τ1 τ2) (And (Eq cc1 cc2) (And (I2F_dvalue f1
    f2) (I2F_targs args1 args2))))))) (c : (@CallE PInf).I) (c0 : (@CallE PFin).I), (P c c0
    (I2FE_Call c c0))) 2 :=
  ⟨I2FE_Call_elim⟩

theorem I2FE_ExternalCall_equation_1 :
    (∀ (τ1 : dtyp) (f1 : (@dvalue PInf)) (args1 : (List (Prod dtyp (@dvalue PInf)))) (τ2 : dtyp) (f2
    : (@dvalue PFin)) (args2 : (List (Prod dtyp (@dvalue PFin)))), (Eq (I2FE_ExternalCall
    (@ExternalCall PInf τ1 f1 args1) (@ExternalCall PFin τ2 f2 args2)) (And (Eq τ1 τ2) (And
    (I2F_dvalue f1 f2) (I2F_targs args1 args2))))) := by intros; rfl

theorem I2FE_ExternalCall_equation_2 :
    (∀ (t : dtyp) (f : (@dvalue PInf)) (args0 : (List (Prod dtyp (@dvalue PInf)))) (str : (List
    VellvmIntegers.int8)), (Eq (I2FE_ExternalCall (@ExternalCall PInf t f args0) (@IO_stdout PFin
    str)) False)) := by intros; rfl

theorem I2FE_ExternalCall_equation_3 :
    (∀ (t : dtyp) (f : (@dvalue PInf)) (args0 : (List (Prod dtyp (@dvalue PInf)))) (str0 : (List
    VellvmIntegers.int8)), (Eq (I2FE_ExternalCall (@ExternalCall PInf t f args0) (@IO_stderr PFin
    str0)) False)) := by intros; rfl

theorem I2FE_ExternalCall_equation_4 :
    (∀ (str : (List VellvmIntegers.int8)) (t : dtyp) (f : (@dvalue PFin)) (args0 : (List (Prod dtyp
    (@dvalue PFin)))), (Eq (I2FE_ExternalCall (@IO_stdout PInf str) (@ExternalCall PFin t f args0))
    False)) := by intros; rfl

theorem I2FE_ExternalCall_equation_5 :
    (∀ (str1 str2 : (List VellvmIntegers.int8)), (Eq (I2FE_ExternalCall (@IO_stdout PInf str1)
    (@IO_stdout PFin str2)) (Eq str1 str2))) := by intros; rfl

theorem I2FE_ExternalCall_equation_6 :
    (∀ (str str1 : (List VellvmIntegers.int8)), (Eq (I2FE_ExternalCall (@IO_stdout PInf str)
    (@IO_stderr PFin str1)) False)) := by intros; rfl

theorem I2FE_ExternalCall_equation_7 :
    (∀ (str0 : (List VellvmIntegers.int8)) (t : dtyp) (f : (@dvalue PFin)) (args0 : (List (Prod dtyp
    (@dvalue PFin)))), (Eq (I2FE_ExternalCall (@IO_stderr PInf str0) (@ExternalCall PFin t f args0))
    False)) := by intros; rfl

theorem I2FE_ExternalCall_equation_8 :
    (∀ (str0 str : (List VellvmIntegers.int8)), (Eq (I2FE_ExternalCall (@IO_stderr PInf str0)
    (@IO_stdout PFin str)) False)) := by intros; rfl

theorem I2FE_ExternalCall_equation_9 :
    (∀ (str1 str2 : (List VellvmIntegers.int8)), (Eq (I2FE_ExternalCall (@IO_stderr PInf str1)
    (@IO_stderr PFin str2)) (Eq str1 str2))) := by intros; rfl

inductive I2FE_ExternalCall_graph :
    (∀ (e : (@ExternalCallE PInf).I) (f : (@ExternalCallE PFin).I) (_ : Prop), Type) where
  | case1 :
      (∀ (τ1 : dtyp) (f1 : (@dvalue PInf)) (args1 : (List (Prod dtyp (@dvalue PInf)))) (τ2 : dtyp)
      (f2 : (@dvalue PFin)) (args2 : (List (Prod dtyp (@dvalue PFin)))), (I2FE_ExternalCall_graph
      (@ExternalCall PInf τ1 f1 args1) (@ExternalCall PFin τ2 f2 args2) (And (Eq τ1 τ2) (And
      (I2F_dvalue f1 f2) (I2F_targs args1 args2)))))
  | case2 :
      (∀ (t : dtyp) (f : (@dvalue PInf)) (args0 : (List (Prod dtyp (@dvalue PInf)))) (str : (List
      VellvmIntegers.int8)), (I2FE_ExternalCall_graph (@ExternalCall PInf t f args0) (@IO_stdout
      PFin str) False))
  | case3 :
      (∀ (t : dtyp) (f : (@dvalue PInf)) (args0 : (List (Prod dtyp (@dvalue PInf)))) (str0 : (List
      VellvmIntegers.int8)), (I2FE_ExternalCall_graph (@ExternalCall PInf t f args0) (@IO_stderr
      PFin str0) False))
  | case4 :
      (∀ (str : (List VellvmIntegers.int8)) (t : dtyp) (f : (@dvalue PFin)) (args0 : (List (Prod
      dtyp (@dvalue PFin)))), (I2FE_ExternalCall_graph (@IO_stdout PInf str) (@ExternalCall PFin t f
      args0) False))
  | case5 :
      (∀ (str1 str2 : (List VellvmIntegers.int8)), (I2FE_ExternalCall_graph (@IO_stdout PInf str1)
      (@IO_stdout PFin str2) (Eq str1 str2)))
  | case6 :
      (∀ (str str1 : (List VellvmIntegers.int8)), (I2FE_ExternalCall_graph (@IO_stdout PInf str)
      (@IO_stderr PFin str1) False))
  | case7 :
      (∀ (str0 : (List VellvmIntegers.int8)) (t : dtyp) (f : (@dvalue PFin)) (args0 : (List (Prod
      dtyp (@dvalue PFin)))), (I2FE_ExternalCall_graph (@IO_stderr PInf str0) (@ExternalCall PFin t
      f args0) False))
  | case8 :
      (∀ (str0 str : (List VellvmIntegers.int8)), (I2FE_ExternalCall_graph (@IO_stderr PInf str0)
      (@IO_stdout PFin str) False))
  | case9 :
      (∀ (str1 str2 : (List VellvmIntegers.int8)), (I2FE_ExternalCall_graph (@IO_stderr PInf str1)
      (@IO_stderr PFin str2) (Eq str1 str2)))

abbrev I2FE_ExternalCall_graph_equation_1 := @I2FE_ExternalCall_graph.case1
abbrev I2FE_ExternalCall_graph_equation_2 := @I2FE_ExternalCall_graph.case2
abbrev I2FE_ExternalCall_graph_equation_3 := @I2FE_ExternalCall_graph.case3
abbrev I2FE_ExternalCall_graph_equation_4 := @I2FE_ExternalCall_graph.case4
abbrev I2FE_ExternalCall_graph_equation_5 := @I2FE_ExternalCall_graph.case5
abbrev I2FE_ExternalCall_graph_equation_6 := @I2FE_ExternalCall_graph.case6
abbrev I2FE_ExternalCall_graph_equation_7 := @I2FE_ExternalCall_graph.case7
abbrev I2FE_ExternalCall_graph_equation_8 := @I2FE_ExternalCall_graph.case8
abbrev I2FE_ExternalCall_graph_equation_9 := @I2FE_ExternalCall_graph.case9

def I2FE_ExternalCall_graph_rect :
    (∀ (P : (∀ (e : (@ExternalCallE PInf).I) (f : (@ExternalCallE PFin).I) (_ : Prop), Type u)) (_ :
    (∀ (τ1 : dtyp) (f1 : (@dvalue PInf)) (args1 : (List (Prod dtyp (@dvalue PInf)))) (τ2 : dtyp) (f2
    : (@dvalue PFin)) (args2 : (List (Prod dtyp (@dvalue PFin)))), (P (@ExternalCall PInf τ1 f1
    args1) (@ExternalCall PFin τ2 f2 args2) (And (Eq τ1 τ2) (And (I2F_dvalue f1 f2) (I2F_targs args1
    args2)))))) (_ : (∀ (t : dtyp) (f : (@dvalue PInf)) (args0 : (List (Prod dtyp (@dvalue PInf))))
    (str : (List VellvmIntegers.int8)), (P (@ExternalCall PInf t f args0) (@IO_stdout PFin str)
    False))) (_ : (∀ (t : dtyp) (f : (@dvalue PInf)) (args0 : (List (Prod dtyp (@dvalue PInf))))
    (str0 : (List VellvmIntegers.int8)), (P (@ExternalCall PInf t f args0) (@IO_stderr PFin str0)
    False))) (_ : (∀ (str : (List VellvmIntegers.int8)) (t : dtyp) (f : (@dvalue PFin)) (args0 :
    (List (Prod dtyp (@dvalue PFin)))), (P (@IO_stdout PInf str) (@ExternalCall PFin t f args0)
    False))) (_ : (∀ (str1 str2 : (List VellvmIntegers.int8)), (P (@IO_stdout PInf str1) (@IO_stdout
    PFin str2) (Eq str1 str2)))) (_ : (∀ (str str1 : (List VellvmIntegers.int8)), (P (@IO_stdout
    PInf str) (@IO_stderr PFin str1) False))) (_ : (∀ (str0 : (List VellvmIntegers.int8)) (t : dtyp)
    (f : (@dvalue PFin)) (args0 : (List (Prod dtyp (@dvalue PFin)))), (P (@IO_stderr PInf str0)
    (@ExternalCall PFin t f args0) False))) (_ : (∀ (str0 str : (List VellvmIntegers.int8)), (P
    (@IO_stderr PInf str0) (@IO_stdout PFin str) False))) (_ : (∀ (str1 str2 : (List
    VellvmIntegers.int8)), (P (@IO_stderr PInf str1) (@IO_stderr PFin str2) (Eq str1 str2)))) {e :
    (@ExternalCallE PInf).I} {e0 : (@ExternalCallE PFin).I} {P0 : Prop} (_ :
    (I2FE_ExternalCall_graph e e0 P0)), (P e e0 P0)) := by
  intro P h1 h2 h3 h4 h5 h6 h7 h8 h9 e f p witness
  cases witness
  next => apply h1
  next => apply h2
  next => apply h3
  next => apply h4
  next => apply h5
  next => apply h6
  next => apply h7
  next => apply h8
  next => apply h9

def I2FE_ExternalCall_graph_correct :
    (∀ (e : (@ExternalCallE PInf).I) (e0 : (@ExternalCallE PFin).I), (I2FE_ExternalCall_graph e e0
    (I2FE_ExternalCall e e0))) := by
  intro e f
  cases e <;> cases f <;> first
    | apply I2FE_ExternalCall_graph.case1
    | apply I2FE_ExternalCall_graph.case2
    | apply I2FE_ExternalCall_graph.case3
    | apply I2FE_ExternalCall_graph.case4
    | apply I2FE_ExternalCall_graph.case5
    | apply I2FE_ExternalCall_graph.case6
    | apply I2FE_ExternalCall_graph.case7
    | apply I2FE_ExternalCall_graph.case8
    | apply I2FE_ExternalCall_graph.case9

def I2FE_ExternalCall_elim :
    (∀ (P : (∀ (e : (@ExternalCallE PInf).I) (f : (@ExternalCallE PFin).I) (_ : Prop), Type u)) (_ :
    (∀ (τ1 : dtyp) (f1 : (@dvalue PInf)) (args1 : (List (Prod dtyp (@dvalue PInf)))) (τ2 : dtyp) (f2
    : (@dvalue PFin)) (args2 : (List (Prod dtyp (@dvalue PFin)))), (P (@ExternalCall PInf τ1 f1
    args1) (@ExternalCall PFin τ2 f2 args2) (And (Eq τ1 τ2) (And (I2F_dvalue f1 f2) (I2F_targs args1
    args2)))))) (_ : (∀ (t : dtyp) (f : (@dvalue PInf)) (args0 : (List (Prod dtyp (@dvalue PInf))))
    (str : (List VellvmIntegers.int8)), (P (@ExternalCall PInf t f args0) (@IO_stdout PFin str)
    False))) (_ : (∀ (t : dtyp) (f : (@dvalue PInf)) (args0 : (List (Prod dtyp (@dvalue PInf))))
    (str0 : (List VellvmIntegers.int8)), (P (@ExternalCall PInf t f args0) (@IO_stderr PFin str0)
    False))) (_ : (∀ (str : (List VellvmIntegers.int8)) (t : dtyp) (f : (@dvalue PFin)) (args0 :
    (List (Prod dtyp (@dvalue PFin)))), (P (@IO_stdout PInf str) (@ExternalCall PFin t f args0)
    False))) (_ : (∀ (str1 str2 : (List VellvmIntegers.int8)), (P (@IO_stdout PInf str1) (@IO_stdout
    PFin str2) (Eq str1 str2)))) (_ : (∀ (str str1 : (List VellvmIntegers.int8)), (P (@IO_stdout
    PInf str) (@IO_stderr PFin str1) False))) (_ : (∀ (str0 : (List VellvmIntegers.int8)) (t : dtyp)
    (f : (@dvalue PFin)) (args0 : (List (Prod dtyp (@dvalue PFin)))), (P (@IO_stderr PInf str0)
    (@ExternalCall PFin t f args0) False))) (_ : (∀ (str0 str : (List VellvmIntegers.int8)), (P
    (@IO_stderr PInf str0) (@IO_stdout PFin str) False))) (_ : (∀ (str1 str2 : (List
    VellvmIntegers.int8)), (P (@IO_stderr PInf str1) (@IO_stderr PFin str2) (Eq str1 str2)))) (e :
    (@ExternalCallE PInf).I) (e0 : (@ExternalCallE PFin).I), (P e e0 (I2FE_ExternalCall e e0))) := by
  intro P h1 h2 h3 h4 h5 h6 h7 h8 h9 e f
  exact I2FE_ExternalCall_graph_rect P h1 h2 h3 h4 h5 h6 h7 h8 h9 (I2FE_ExternalCall_graph_correct e f)

instance FunctionalInduction_I2FE_ExternalCall :
    (FunctionalInduction.{0, 0} I2FE_ExternalCall) := ⟨_, I2FE_ExternalCall_graph_correct⟩

instance FunctionalElimination_I2FE_ExternalCall :
    FunctionalElimination I2FE_ExternalCall (∀ (P : (∀ (e : (@ExternalCallE PInf).I) (f : (@ExternalCallE PFin).I) (_ : Prop), Type u)) (_ :
    (∀ (τ1 : dtyp) (f1 : (@dvalue PInf)) (args1 : (List (Prod dtyp (@dvalue PInf)))) (τ2 : dtyp) (f2
    : (@dvalue PFin)) (args2 : (List (Prod dtyp (@dvalue PFin)))), (P (@ExternalCall PInf τ1 f1
    args1) (@ExternalCall PFin τ2 f2 args2) (And (Eq τ1 τ2) (And (I2F_dvalue f1 f2) (I2F_targs args1
    args2)))))) (_ : (∀ (t : dtyp) (f : (@dvalue PInf)) (args0 : (List (Prod dtyp (@dvalue PInf))))
    (str : (List VellvmIntegers.int8)), (P (@ExternalCall PInf t f args0) (@IO_stdout PFin str)
    False))) (_ : (∀ (t : dtyp) (f : (@dvalue PInf)) (args0 : (List (Prod dtyp (@dvalue PInf))))
    (str0 : (List VellvmIntegers.int8)), (P (@ExternalCall PInf t f args0) (@IO_stderr PFin str0)
    False))) (_ : (∀ (str : (List VellvmIntegers.int8)) (t : dtyp) (f : (@dvalue PFin)) (args0 :
    (List (Prod dtyp (@dvalue PFin)))), (P (@IO_stdout PInf str) (@ExternalCall PFin t f args0)
    False))) (_ : (∀ (str1 str2 : (List VellvmIntegers.int8)), (P (@IO_stdout PInf str1) (@IO_stdout
    PFin str2) (Eq str1 str2)))) (_ : (∀ (str str1 : (List VellvmIntegers.int8)), (P (@IO_stdout
    PInf str) (@IO_stderr PFin str1) False))) (_ : (∀ (str0 : (List VellvmIntegers.int8)) (t : dtyp)
    (f : (@dvalue PFin)) (args0 : (List (Prod dtyp (@dvalue PFin)))), (P (@IO_stderr PInf str0)
    (@ExternalCall PFin t f args0) False))) (_ : (∀ (str0 str : (List VellvmIntegers.int8)), (P
    (@IO_stderr PInf str0) (@IO_stdout PFin str) False))) (_ : (∀ (str1 str2 : (List
    VellvmIntegers.int8)), (P (@IO_stderr PInf str1) (@IO_stderr PFin str2) (Eq str1 str2)))) (e :
    (@ExternalCallE PInf).I) (e0 : (@ExternalCallE PFin).I), (P e e0 (I2FE_ExternalCall e e0))) 10 :=
  ⟨I2FE_ExternalCall_elim⟩

theorem I2FE_Intrinsic_equation_1 :
    (∀ (τ1 : dtyp) (f1 : IRString) (args1 : (List (Prod dtyp (@dvalue PInf)))) (va1 : (Option
    PInf.PTR.ptr)) (τ2 : dtyp) (f2 : IRString) (args2 : (List (Prod dtyp (@dvalue PFin)))) (va2 :
    (Option PFin.PTR.ptr)), (Eq (I2FE_Intrinsic (@Intrinsic PInf τ1 f1 args1 va1) (@Intrinsic PFin
    τ2 f2 args2 va2)) (And (Eq τ1 τ2) (And (Eq f1 f2) (And (I2F_targs args1 args2)
    (Numeric.Rocqlib.option_rel I2F_Addr va1 va2)))))) := by intros; rfl

inductive I2FE_Intrinsic_graph :
    (∀ (e : (@IntrinsicE PInf).I) (f : (@IntrinsicE PFin).I) (_ : Prop), Type) where
  | case1 :
      (∀ (τ1 : dtyp) (f1 : IRString) (args1 : (List (Prod dtyp (@dvalue PInf)))) (va1 : (Option
      PInf.PTR.ptr)) (τ2 : dtyp) (f2 : IRString) (args2 : (List (Prod dtyp (@dvalue PFin)))) (va2 :
      (Option PFin.PTR.ptr)), (I2FE_Intrinsic_graph (@Intrinsic PInf τ1 f1 args1 va1) (@Intrinsic
      PFin τ2 f2 args2 va2) (And (Eq τ1 τ2) (And (Eq f1 f2) (And (I2F_targs args1 args2)
      (Numeric.Rocqlib.option_rel I2F_Addr va1 va2))))))

abbrev I2FE_Intrinsic_graph_equation_1 := @I2FE_Intrinsic_graph.case1

def I2FE_Intrinsic_graph_rect :
    (∀ (P : (∀ (e : (@IntrinsicE PInf).I) (f : (@IntrinsicE PFin).I) (_ : Prop), Type u)) (_ : (∀
    (τ1 : dtyp) (f1 : IRString) (args1 : (List (Prod dtyp (@dvalue PInf)))) (va1 : (Option
    PInf.PTR.ptr)) (τ2 : dtyp) (f2 : IRString) (args2 : (List (Prod dtyp (@dvalue PFin)))) (va2 :
    (Option PFin.PTR.ptr)), (P (@Intrinsic PInf τ1 f1 args1 va1) (@Intrinsic PFin τ2 f2 args2 va2)
    (And (Eq τ1 τ2) (And (Eq f1 f2) (And (I2F_targs args1 args2) (Numeric.Rocqlib.option_rel
    I2F_Addr va1 va2))))))) {i : (@IntrinsicE PInf).I} {i0 : (@IntrinsicE PFin).I} {P0 : Prop} (_ :
    (I2FE_Intrinsic_graph i i0 P0)), (P i i0 P0)) := by
  intro P h1 e f p witness
  cases witness
  next => apply h1

def I2FE_Intrinsic_graph_correct :
    (∀ (i : (@IntrinsicE PInf).I) (i0 : (@IntrinsicE PFin).I), (I2FE_Intrinsic_graph i i0
    (I2FE_Intrinsic i i0))) := by
  intro e f
  cases e <;> cases f <;> first
    | apply I2FE_Intrinsic_graph.case1

def I2FE_Intrinsic_elim :
    (∀ (P : (∀ (e : (@IntrinsicE PInf).I) (f : (@IntrinsicE PFin).I) (_ : Prop), Type u)) (_ : (∀
    (τ1 : dtyp) (f1 : IRString) (args1 : (List (Prod dtyp (@dvalue PInf)))) (va1 : (Option
    PInf.PTR.ptr)) (τ2 : dtyp) (f2 : IRString) (args2 : (List (Prod dtyp (@dvalue PFin)))) (va2 :
    (Option PFin.PTR.ptr)), (P (@Intrinsic PInf τ1 f1 args1 va1) (@Intrinsic PFin τ2 f2 args2 va2)
    (And (Eq τ1 τ2) (And (Eq f1 f2) (And (I2F_targs args1 args2) (Numeric.Rocqlib.option_rel
    I2F_Addr va1 va2))))))) (i : (@IntrinsicE PInf).I) (i0 : (@IntrinsicE PFin).I), (P i i0
    (I2FE_Intrinsic i i0))) := by
  intro P h1 e f
  exact I2FE_Intrinsic_graph_rect P h1 (I2FE_Intrinsic_graph_correct e f)

instance FunctionalInduction_I2FE_Intrinsic :
    (FunctionalInduction.{0, 0} I2FE_Intrinsic) := ⟨_, I2FE_Intrinsic_graph_correct⟩

instance FunctionalElimination_I2FE_Intrinsic :
    FunctionalElimination I2FE_Intrinsic (∀ (P : (∀ (e : (@IntrinsicE PInf).I) (f : (@IntrinsicE PFin).I) (_ : Prop), Type u)) (_ : (∀
    (τ1 : dtyp) (f1 : IRString) (args1 : (List (Prod dtyp (@dvalue PInf)))) (va1 : (Option
    PInf.PTR.ptr)) (τ2 : dtyp) (f2 : IRString) (args2 : (List (Prod dtyp (@dvalue PFin)))) (va2 :
    (Option PFin.PTR.ptr)), (P (@Intrinsic PInf τ1 f1 args1 va1) (@Intrinsic PFin τ2 f2 args2 va2)
    (And (Eq τ1 τ2) (And (Eq f1 f2) (And (I2F_targs args1 args2) (Numeric.Rocqlib.option_rel
    I2F_Addr va1 va2))))))) (i : (@IntrinsicE PInf).I) (i0 : (@IntrinsicE PFin).I), (P i i0
    (I2FE_Intrinsic i i0))) 2 :=
  ⟨I2FE_Intrinsic_elim⟩

theorem I2FE_Global_equation_1 :
    (∀ (x1 : raw_id) (dv1 : (@dvalue PInf)) (x2 : raw_id) (dv2 : (@dvalue PFin)), (Eq (I2FE_Global
    (@GlobalWrite PInf x1 dv1) (@GlobalWrite PFin x2 dv2)) (And (Eq x1 x2) (I2F_dvalue dv1 dv2)))) := by intros; rfl

theorem I2FE_Global_equation_2 :
    (∀ (id0 : raw_id) (dv : (@dvalue PInf)) (id2 : raw_id), (Eq (I2FE_Global (@GlobalWrite PInf id0
    dv) (@GlobalRead PFin id2)) False)) := by intros; rfl

theorem I2FE_Global_equation_3 :
    (∀ (id1 id0 : raw_id) (dv : (@dvalue PFin)), (Eq (I2FE_Global (@GlobalRead PInf id1)
    (@GlobalWrite PFin id0 dv)) False)) := by intros; rfl

theorem I2FE_Global_equation_4 :
    (∀ (x1 x2 : raw_id), (Eq (I2FE_Global (@GlobalRead PInf x1) (@GlobalRead PFin x2)) (Eq x1 x2))) := by intros; rfl

inductive I2FE_Global_graph :
    (∀ (e : (@GlobalE PInf).I) (f : (@GlobalE PFin).I) (_ : Prop), Type) where
  | case1 :
      (∀ (x1 : raw_id) (dv1 : (@dvalue PInf)) (x2 : raw_id) (dv2 : (@dvalue PFin)),
      (I2FE_Global_graph (@GlobalWrite PInf x1 dv1) (@GlobalWrite PFin x2 dv2) (And (Eq x1 x2)
      (I2F_dvalue dv1 dv2))))
  | case2 :
      (∀ (id0 : raw_id) (dv : (@dvalue PInf)) (id2 : raw_id), (I2FE_Global_graph (@GlobalWrite PInf
      id0 dv) (@GlobalRead PFin id2) False))
  | case3 :
      (∀ (id1 id0 : raw_id) (dv : (@dvalue PFin)), (I2FE_Global_graph (@GlobalRead PInf id1)
      (@GlobalWrite PFin id0 dv) False))
  | case4 :
      (∀ (x1 x2 : raw_id), (I2FE_Global_graph (@GlobalRead PInf x1) (@GlobalRead PFin x2) (Eq x1
      x2)))

abbrev I2FE_Global_graph_equation_1 := @I2FE_Global_graph.case1
abbrev I2FE_Global_graph_equation_2 := @I2FE_Global_graph.case2
abbrev I2FE_Global_graph_equation_3 := @I2FE_Global_graph.case3
abbrev I2FE_Global_graph_equation_4 := @I2FE_Global_graph.case4

def I2FE_Global_graph_rect :
    (∀ (P : (∀ (e : (@GlobalE PInf).I) (f : (@GlobalE PFin).I) (_ : Prop), Type u)) (_ : (∀ (x1 :
    raw_id) (dv1 : (@dvalue PInf)) (x2 : raw_id) (dv2 : (@dvalue PFin)), (P (@GlobalWrite PInf x1
    dv1) (@GlobalWrite PFin x2 dv2) (And (Eq x1 x2) (I2F_dvalue dv1 dv2))))) (_ : (∀ (id0 : raw_id)
    (dv : (@dvalue PInf)) (id2 : raw_id), (P (@GlobalWrite PInf id0 dv) (@GlobalRead PFin id2)
    False))) (_ : (∀ (id1 id0 : raw_id) (dv : (@dvalue PFin)), (P (@GlobalRead PInf id1)
    (@GlobalWrite PFin id0 dv) False))) (_ : (∀ (x1 x2 : raw_id), (P (@GlobalRead PInf x1)
    (@GlobalRead PFin x2) (Eq x1 x2)))) {g : (@GlobalE PInf).I} {g0 : (@GlobalE PFin).I} {P0 : Prop}
    (_ : (I2FE_Global_graph g g0 P0)), (P g g0 P0)) := by
  intro P h1 h2 h3 h4 e f p witness
  cases witness
  next => apply h1
  next => apply h2
  next => apply h3
  next => apply h4

def I2FE_Global_graph_correct :
    (∀ (g : (@GlobalE PInf).I) (g0 : (@GlobalE PFin).I), (I2FE_Global_graph g g0 (I2FE_Global g
    g0))) := by
  intro e f
  cases e <;> cases f <;> first
    | apply I2FE_Global_graph.case1
    | apply I2FE_Global_graph.case2
    | apply I2FE_Global_graph.case3
    | apply I2FE_Global_graph.case4

def I2FE_Global_elim :
    (∀ (P : (∀ (e : (@GlobalE PInf).I) (f : (@GlobalE PFin).I) (_ : Prop), Type u)) (_ : (∀ (x1 :
    raw_id) (dv1 : (@dvalue PInf)) (x2 : raw_id) (dv2 : (@dvalue PFin)), (P (@GlobalWrite PInf x1
    dv1) (@GlobalWrite PFin x2 dv2) (And (Eq x1 x2) (I2F_dvalue dv1 dv2))))) (_ : (∀ (id0 : raw_id)
    (dv : (@dvalue PInf)) (id2 : raw_id), (P (@GlobalWrite PInf id0 dv) (@GlobalRead PFin id2)
    False))) (_ : (∀ (id1 id0 : raw_id) (dv : (@dvalue PFin)), (P (@GlobalRead PInf id1)
    (@GlobalWrite PFin id0 dv) False))) (_ : (∀ (x1 x2 : raw_id), (P (@GlobalRead PInf x1)
    (@GlobalRead PFin x2) (Eq x1 x2)))) (g : (@GlobalE PInf).I) (g0 : (@GlobalE PFin).I), (P g g0
    (I2FE_Global g g0))) := by
  intro P h1 h2 h3 h4 e f
  exact I2FE_Global_graph_rect P h1 h2 h3 h4 (I2FE_Global_graph_correct e f)

instance FunctionalInduction_I2FE_Global :
    (FunctionalInduction.{0, 0} I2FE_Global) := ⟨_, I2FE_Global_graph_correct⟩

instance FunctionalElimination_I2FE_Global :
    FunctionalElimination I2FE_Global (∀ (P : (∀ (e : (@GlobalE PInf).I) (f : (@GlobalE PFin).I) (_ : Prop), Type u)) (_ : (∀ (x1 :
    raw_id) (dv1 : (@dvalue PInf)) (x2 : raw_id) (dv2 : (@dvalue PFin)), (P (@GlobalWrite PInf x1
    dv1) (@GlobalWrite PFin x2 dv2) (And (Eq x1 x2) (I2F_dvalue dv1 dv2))))) (_ : (∀ (id0 : raw_id)
    (dv : (@dvalue PInf)) (id2 : raw_id), (P (@GlobalWrite PInf id0 dv) (@GlobalRead PFin id2)
    False))) (_ : (∀ (id1 id0 : raw_id) (dv : (@dvalue PFin)), (P (@GlobalRead PInf id1)
    (@GlobalWrite PFin id0 dv) False))) (_ : (∀ (x1 x2 : raw_id), (P (@GlobalRead PInf x1)
    (@GlobalRead PFin x2) (Eq x1 x2)))) (g : (@GlobalE PInf).I) (g0 : (@GlobalE PFin).I), (P g g0
    (I2FE_Global g g0))) 5 :=
  ⟨I2FE_Global_elim⟩

theorem I2FE_Local_equation_1 :
    (∀ (x1 : raw_id) (dv1 : (@dvalue PInf)) (x2 : raw_id) (dv2 : (@dvalue PFin)), (Eq (I2FE_Local
    (@LocalWrite PInf x1 dv1) (@LocalWrite PFin x2 dv2)) (And (Eq x1 x2) (I2F_dvalue dv1 dv2)))) := by intros; rfl

theorem I2FE_Local_equation_2 :
    (∀ (id0 : raw_id) (dv : (@dvalue PInf)) (id2 : raw_id), (Eq (I2FE_Local (@LocalWrite PInf id0
    dv) (@LocalRead PFin id2)) False)) := by intros; rfl

theorem I2FE_Local_equation_3 :
    (∀ (id1 id0 : raw_id) (dv : (@dvalue PFin)), (Eq (I2FE_Local (@LocalRead PInf id1) (@LocalWrite
    PFin id0 dv)) False)) := by intros; rfl

theorem I2FE_Local_equation_4 :
    (∀ (x1 x2 : raw_id), (Eq (I2FE_Local (@LocalRead PInf x1) (@LocalRead PFin x2)) (Eq x1 x2))) := by intros; rfl

inductive I2FE_Local_graph :
    (∀ (e : (@LocalE PInf).I) (f : (@LocalE PFin).I) (_ : Prop), Type) where
  | case1 :
      (∀ (x1 : raw_id) (dv1 : (@dvalue PInf)) (x2 : raw_id) (dv2 : (@dvalue PFin)),
      (I2FE_Local_graph (@LocalWrite PInf x1 dv1) (@LocalWrite PFin x2 dv2) (And (Eq x1 x2)
      (I2F_dvalue dv1 dv2))))
  | case2 :
      (∀ (id0 : raw_id) (dv : (@dvalue PInf)) (id2 : raw_id), (I2FE_Local_graph (@LocalWrite PInf
      id0 dv) (@LocalRead PFin id2) False))
  | case3 :
      (∀ (id1 id0 : raw_id) (dv : (@dvalue PFin)), (I2FE_Local_graph (@LocalRead PInf id1)
      (@LocalWrite PFin id0 dv) False))
  | case4 :
      (∀ (x1 x2 : raw_id), (I2FE_Local_graph (@LocalRead PInf x1) (@LocalRead PFin x2) (Eq x1 x2)))

abbrev I2FE_Local_graph_equation_1 := @I2FE_Local_graph.case1
abbrev I2FE_Local_graph_equation_2 := @I2FE_Local_graph.case2
abbrev I2FE_Local_graph_equation_3 := @I2FE_Local_graph.case3
abbrev I2FE_Local_graph_equation_4 := @I2FE_Local_graph.case4

def I2FE_Local_graph_rect :
    (∀ (P : (∀ (e : (@LocalE PInf).I) (f : (@LocalE PFin).I) (_ : Prop), Type u)) (_ : (∀ (x1 :
    raw_id) (dv1 : (@dvalue PInf)) (x2 : raw_id) (dv2 : (@dvalue PFin)), (P (@LocalWrite PInf x1
    dv1) (@LocalWrite PFin x2 dv2) (And (Eq x1 x2) (I2F_dvalue dv1 dv2))))) (_ : (∀ (id0 : raw_id)
    (dv : (@dvalue PInf)) (id2 : raw_id), (P (@LocalWrite PInf id0 dv) (@LocalRead PFin id2)
    False))) (_ : (∀ (id1 id0 : raw_id) (dv : (@dvalue PFin)), (P (@LocalRead PInf id1) (@LocalWrite
    PFin id0 dv) False))) (_ : (∀ (x1 x2 : raw_id), (P (@LocalRead PInf x1) (@LocalRead PFin x2) (Eq
    x1 x2)))) {l : (@LocalE PInf).I} {l0 : (@LocalE PFin).I} {P0 : Prop} (_ : (I2FE_Local_graph l l0
    P0)), (P l l0 P0)) := by
  intro P h1 h2 h3 h4 e f p witness
  cases witness
  next => apply h1
  next => apply h2
  next => apply h3
  next => apply h4

def I2FE_Local_graph_correct :
    (∀ (l : (@LocalE PInf).I) (l0 : (@LocalE PFin).I), (I2FE_Local_graph l l0 (I2FE_Local l l0))) := by
  intro e f
  cases e <;> cases f <;> first
    | apply I2FE_Local_graph.case1
    | apply I2FE_Local_graph.case2
    | apply I2FE_Local_graph.case3
    | apply I2FE_Local_graph.case4

def I2FE_Local_elim :
    (∀ (P : (∀ (e : (@LocalE PInf).I) (f : (@LocalE PFin).I) (_ : Prop), Type u)) (_ : (∀ (x1 :
    raw_id) (dv1 : (@dvalue PInf)) (x2 : raw_id) (dv2 : (@dvalue PFin)), (P (@LocalWrite PInf x1
    dv1) (@LocalWrite PFin x2 dv2) (And (Eq x1 x2) (I2F_dvalue dv1 dv2))))) (_ : (∀ (id0 : raw_id)
    (dv : (@dvalue PInf)) (id2 : raw_id), (P (@LocalWrite PInf id0 dv) (@LocalRead PFin id2)
    False))) (_ : (∀ (id1 id0 : raw_id) (dv : (@dvalue PFin)), (P (@LocalRead PInf id1) (@LocalWrite
    PFin id0 dv) False))) (_ : (∀ (x1 x2 : raw_id), (P (@LocalRead PInf x1) (@LocalRead PFin x2) (Eq
    x1 x2)))) (l : (@LocalE PInf).I) (l0 : (@LocalE PFin).I), (P l l0 (I2FE_Local l l0))) := by
  intro P h1 h2 h3 h4 e f
  exact I2FE_Local_graph_rect P h1 h2 h3 h4 (I2FE_Local_graph_correct e f)

instance FunctionalInduction_I2FE_Local :
    (FunctionalInduction.{0, 0} I2FE_Local) := ⟨_, I2FE_Local_graph_correct⟩

instance FunctionalElimination_I2FE_Local :
    FunctionalElimination I2FE_Local (∀ (P : (∀ (e : (@LocalE PInf).I) (f : (@LocalE PFin).I) (_ : Prop), Type u)) (_ : (∀ (x1 :
    raw_id) (dv1 : (@dvalue PInf)) (x2 : raw_id) (dv2 : (@dvalue PFin)), (P (@LocalWrite PInf x1
    dv1) (@LocalWrite PFin x2 dv2) (And (Eq x1 x2) (I2F_dvalue dv1 dv2))))) (_ : (∀ (id0 : raw_id)
    (dv : (@dvalue PInf)) (id2 : raw_id), (P (@LocalWrite PInf id0 dv) (@LocalRead PFin id2)
    False))) (_ : (∀ (id1 id0 : raw_id) (dv : (@dvalue PFin)), (P (@LocalRead PInf id1) (@LocalWrite
    PFin id0 dv) False))) (_ : (∀ (x1 x2 : raw_id), (P (@LocalRead PInf x1) (@LocalRead PFin x2) (Eq
    x1 x2)))) (l : (@LocalE PInf).I) (l0 : (@LocalE PFin).I), (P l l0 (I2FE_Local l l0))) 5 :=
  ⟨I2FE_Local_elim⟩

theorem I2FE_Stack_equation_1 :
    (∀ (args1 : (List (Prod raw_id (@dvalue PInf)))) (args2 : (List (Prod raw_id (@dvalue PFin)))),
    (Eq (I2FE_Stack (@StackPush PInf args1) (@StackPush PFin args2)) (List.Forall₂
    (Utils.RelationsUtil.prod_rel Eq I2F_dvalue) args1 args2))) := by intros; rfl

theorem I2FE_Stack_equation_2 :
    (∀ (args0 : (List (Prod raw_id (@dvalue PInf)))), (Eq (I2FE_Stack (@StackPush PInf args0)
    (@StackPop PFin)) False)) := by intros; rfl

theorem I2FE_Stack_equation_3 :
    (∀ (args0 : (List (Prod raw_id (@dvalue PInf)))) (e : (@exc PFin)), (Eq (I2FE_Stack (@StackPush
    PInf args0) (@StackRaise PFin e)) False)) := by intros; rfl

theorem I2FE_Stack_equation_4 :
    (∀ (args0 : (List (Prod raw_id (@dvalue PInf)))), (Eq (I2FE_Stack (@StackPush PInf args0)
    (@StackGetExc PFin)) False)) := by intros; rfl

theorem I2FE_Stack_equation_5 :
    (∀ (args0 : (List (Prod raw_id (@dvalue PFin)))), (Eq (I2FE_Stack (@StackPop PInf) (@StackPush
    PFin args0)) False)) := by intros; rfl

theorem I2FE_Stack_equation_6 :
    (Eq (I2FE_Stack (@StackPop PInf) (@StackPop PFin)) True) := by rfl

theorem I2FE_Stack_equation_7 :
    (∀ (e : (@exc PFin)), (Eq (I2FE_Stack (@StackPop PInf) (@StackRaise PFin e)) False)) := by intros; rfl

theorem I2FE_Stack_equation_8 :
    (Eq (I2FE_Stack (@StackPop PInf) (@StackGetExc PFin)) False) := by rfl

theorem I2FE_Stack_equation_9 :
    (∀ (e : (@exc PInf)) (args0 : (List (Prod raw_id (@dvalue PFin)))), (Eq (I2FE_Stack (@StackRaise
    PInf e) (@StackPush PFin args0)) False)) := by intros; rfl

theorem I2FE_Stack_equation_10 :
    (∀ (e : (@exc PInf)), (Eq (I2FE_Stack (@StackRaise PInf e) (@StackPop PFin)) False)) := by intros; rfl

theorem I2FE_Stack_equation_11 :
    (∀ (exc1 : (@exc PInf)) (exc2 : (@exc PFin)), (Eq (I2FE_Stack (@StackRaise PInf exc1)
    (@StackRaise PFin exc2)) (I2F_dvalue exc1 exc2))) := by intros; rfl

theorem I2FE_Stack_equation_12 :
    (∀ (e : (@exc PInf)), (Eq (I2FE_Stack (@StackRaise PInf e) (@StackGetExc PFin)) False)) := by intros; rfl

theorem I2FE_Stack_equation_13 :
    (∀ (args0 : (List (Prod raw_id (@dvalue PFin)))), (Eq (I2FE_Stack (@StackGetExc PInf)
    (@StackPush PFin args0)) False)) := by intros; rfl

theorem I2FE_Stack_equation_14 :
    (Eq (I2FE_Stack (@StackGetExc PInf) (@StackPop PFin)) False) := by rfl

theorem I2FE_Stack_equation_15 :
    (∀ (e : (@exc PFin)), (Eq (I2FE_Stack (@StackGetExc PInf) (@StackRaise PFin e)) False)) := by intros; rfl

theorem I2FE_Stack_equation_16 :
    (Eq (I2FE_Stack (@StackGetExc PInf) (@StackGetExc PFin)) True) := by rfl

inductive I2FE_Stack_graph :
    (∀ (e : (@StackE PInf).I) (f : (@StackE PFin).I) (_ : Prop), Type) where
  | case1 :
      (∀ (args1 : (List (Prod raw_id (@dvalue PInf)))) (args2 : (List (Prod raw_id (@dvalue
      PFin)))), (I2FE_Stack_graph (@StackPush PInf args1) (@StackPush PFin args2) (List.Forall₂
      (Utils.RelationsUtil.prod_rel Eq I2F_dvalue) args1 args2)))
  | case2 :
      (∀ (args0 : (List (Prod raw_id (@dvalue PInf)))), (I2FE_Stack_graph (@StackPush PInf args0)
      (@StackPop PFin) False))
  | case3 :
      (∀ (args0 : (List (Prod raw_id (@dvalue PInf)))) (e : (@exc PFin)), (I2FE_Stack_graph
      (@StackPush PInf args0) (@StackRaise PFin e) False))
  | case4 :
      (∀ (args0 : (List (Prod raw_id (@dvalue PInf)))), (I2FE_Stack_graph (@StackPush PInf args0)
      (@StackGetExc PFin) False))
  | case5 :
      (∀ (args0 : (List (Prod raw_id (@dvalue PFin)))), (I2FE_Stack_graph (@StackPop PInf)
      (@StackPush PFin args0) False))
  | case6 :
      (I2FE_Stack_graph (@StackPop PInf) (@StackPop PFin) True)
  | case7 :
      (∀ (e : (@exc PFin)), (I2FE_Stack_graph (@StackPop PInf) (@StackRaise PFin e) False))
  | case8 :
      (I2FE_Stack_graph (@StackPop PInf) (@StackGetExc PFin) False)
  | case9 :
      (∀ (e : (@exc PInf)) (args0 : (List (Prod raw_id (@dvalue PFin)))), (I2FE_Stack_graph
      (@StackRaise PInf e) (@StackPush PFin args0) False))
  | case10 :
      (∀ (e : (@exc PInf)), (I2FE_Stack_graph (@StackRaise PInf e) (@StackPop PFin) False))
  | case11 :
      (∀ (exc1 : (@exc PInf)) (exc2 : (@exc PFin)), (I2FE_Stack_graph (@StackRaise PInf exc1)
      (@StackRaise PFin exc2) (I2F_dvalue exc1 exc2)))
  | case12 :
      (∀ (e : (@exc PInf)), (I2FE_Stack_graph (@StackRaise PInf e) (@StackGetExc PFin) False))
  | case13 :
      (∀ (args0 : (List (Prod raw_id (@dvalue PFin)))), (I2FE_Stack_graph (@StackGetExc PInf)
      (@StackPush PFin args0) False))
  | case14 :
      (I2FE_Stack_graph (@StackGetExc PInf) (@StackPop PFin) False)
  | case15 :
      (∀ (e : (@exc PFin)), (I2FE_Stack_graph (@StackGetExc PInf) (@StackRaise PFin e) False))
  | case16 :
      (I2FE_Stack_graph (@StackGetExc PInf) (@StackGetExc PFin) True)

abbrev I2FE_Stack_graph_equation_1 := @I2FE_Stack_graph.case1
abbrev I2FE_Stack_graph_equation_2 := @I2FE_Stack_graph.case2
abbrev I2FE_Stack_graph_equation_3 := @I2FE_Stack_graph.case3
abbrev I2FE_Stack_graph_equation_4 := @I2FE_Stack_graph.case4
abbrev I2FE_Stack_graph_equation_5 := @I2FE_Stack_graph.case5
abbrev I2FE_Stack_graph_equation_6 := @I2FE_Stack_graph.case6
abbrev I2FE_Stack_graph_equation_7 := @I2FE_Stack_graph.case7
abbrev I2FE_Stack_graph_equation_8 := @I2FE_Stack_graph.case8
abbrev I2FE_Stack_graph_equation_9 := @I2FE_Stack_graph.case9
abbrev I2FE_Stack_graph_equation_10 := @I2FE_Stack_graph.case10
abbrev I2FE_Stack_graph_equation_11 := @I2FE_Stack_graph.case11
abbrev I2FE_Stack_graph_equation_12 := @I2FE_Stack_graph.case12
abbrev I2FE_Stack_graph_equation_13 := @I2FE_Stack_graph.case13
abbrev I2FE_Stack_graph_equation_14 := @I2FE_Stack_graph.case14
abbrev I2FE_Stack_graph_equation_15 := @I2FE_Stack_graph.case15
abbrev I2FE_Stack_graph_equation_16 := @I2FE_Stack_graph.case16

def I2FE_Stack_graph_rect :
    (∀ (P : (∀ (e : (@StackE PInf).I) (f : (@StackE PFin).I) (_ : Prop), Type u)) (_ : (∀ (args1 :
    (List (Prod raw_id (@dvalue PInf)))) (args2 : (List (Prod raw_id (@dvalue PFin)))), (P
    (@StackPush PInf args1) (@StackPush PFin args2) (List.Forall₂ (Utils.RelationsUtil.prod_rel Eq
    I2F_dvalue) args1 args2)))) (_ : (∀ (args0 : (List (Prod raw_id (@dvalue PInf)))), (P
    (@StackPush PInf args0) (@StackPop PFin) False))) (_ : (∀ (args0 : (List (Prod raw_id (@dvalue
    PInf)))) (e : (@exc PFin)), (P (@StackPush PInf args0) (@StackRaise PFin e) False))) (_ : (∀
    (args0 : (List (Prod raw_id (@dvalue PInf)))), (P (@StackPush PInf args0) (@StackGetExc PFin)
    False))) (_ : (∀ (args0 : (List (Prod raw_id (@dvalue PFin)))), (P (@StackPop PInf) (@StackPush
    PFin args0) False))) (_ : (P (@StackPop PInf) (@StackPop PFin) True)) (_ : (∀ (e : (@exc PFin)),
    (P (@StackPop PInf) (@StackRaise PFin e) False))) (_ : (P (@StackPop PInf) (@StackGetExc PFin)
    False)) (_ : (∀ (e : (@exc PInf)) (args0 : (List (Prod raw_id (@dvalue PFin)))), (P (@StackRaise
    PInf e) (@StackPush PFin args0) False))) (_ : (∀ (e : (@exc PInf)), (P (@StackRaise PInf e)
    (@StackPop PFin) False))) (_ : (∀ (exc1 : (@exc PInf)) (exc2 : (@exc PFin)), (P (@StackRaise
    PInf exc1) (@StackRaise PFin exc2) (I2F_dvalue exc1 exc2)))) (_ : (∀ (e : (@exc PInf)), (P
    (@StackRaise PInf e) (@StackGetExc PFin) False))) (_ : (∀ (args0 : (List (Prod raw_id (@dvalue
    PFin)))), (P (@StackGetExc PInf) (@StackPush PFin args0) False))) (_ : (P (@StackGetExc PInf)
    (@StackPop PFin) False)) (_ : (∀ (e : (@exc PFin)), (P (@StackGetExc PInf) (@StackRaise PFin e)
    False))) (_ : (P (@StackGetExc PInf) (@StackGetExc PFin) True)) {s : (@StackE PInf).I} {s0 :
    (@StackE PFin).I} {P0 : Prop} (_ : (I2FE_Stack_graph s s0 P0)), (P s s0 P0)) := by
  intro P h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15 h16 e f p witness
  cases witness
  next => apply h1
  next => apply h2
  next => apply h3
  next => apply h4
  next => apply h5
  next => apply h6
  next => apply h7
  next => apply h8
  next => apply h9
  next => apply h10
  next => apply h11
  next => apply h12
  next => apply h13
  next => apply h14
  next => apply h15
  next => apply h16

def I2FE_Stack_graph_correct :
    (∀ (s : (@StackE PInf).I) (s0 : (@StackE PFin).I), (I2FE_Stack_graph s s0 (I2FE_Stack s s0))) := by
  intro e f
  cases e <;> cases f <;> first
    | apply I2FE_Stack_graph.case1
    | apply I2FE_Stack_graph.case2
    | apply I2FE_Stack_graph.case3
    | apply I2FE_Stack_graph.case4
    | apply I2FE_Stack_graph.case5
    | apply I2FE_Stack_graph.case6
    | apply I2FE_Stack_graph.case7
    | apply I2FE_Stack_graph.case8
    | apply I2FE_Stack_graph.case9
    | apply I2FE_Stack_graph.case10
    | apply I2FE_Stack_graph.case11
    | apply I2FE_Stack_graph.case12
    | apply I2FE_Stack_graph.case13
    | apply I2FE_Stack_graph.case14
    | apply I2FE_Stack_graph.case15
    | apply I2FE_Stack_graph.case16

def I2FE_Stack_elim :
    (∀ (P : (∀ (e : (@StackE PInf).I) (f : (@StackE PFin).I) (_ : Prop), Type u)) (_ : (∀ (args1 :
    (List (Prod raw_id (@dvalue PInf)))) (args2 : (List (Prod raw_id (@dvalue PFin)))), (P
    (@StackPush PInf args1) (@StackPush PFin args2) (List.Forall₂ (Utils.RelationsUtil.prod_rel Eq
    I2F_dvalue) args1 args2)))) (_ : (∀ (args0 : (List (Prod raw_id (@dvalue PInf)))), (P
    (@StackPush PInf args0) (@StackPop PFin) False))) (_ : (∀ (args0 : (List (Prod raw_id (@dvalue
    PInf)))) (e : (@exc PFin)), (P (@StackPush PInf args0) (@StackRaise PFin e) False))) (_ : (∀
    (args0 : (List (Prod raw_id (@dvalue PInf)))), (P (@StackPush PInf args0) (@StackGetExc PFin)
    False))) (_ : (∀ (args0 : (List (Prod raw_id (@dvalue PFin)))), (P (@StackPop PInf) (@StackPush
    PFin args0) False))) (_ : (P (@StackPop PInf) (@StackPop PFin) True)) (_ : (∀ (e : (@exc PFin)),
    (P (@StackPop PInf) (@StackRaise PFin e) False))) (_ : (P (@StackPop PInf) (@StackGetExc PFin)
    False)) (_ : (∀ (e : (@exc PInf)) (args0 : (List (Prod raw_id (@dvalue PFin)))), (P (@StackRaise
    PInf e) (@StackPush PFin args0) False))) (_ : (∀ (e : (@exc PInf)), (P (@StackRaise PInf e)
    (@StackPop PFin) False))) (_ : (∀ (exc1 : (@exc PInf)) (exc2 : (@exc PFin)), (P (@StackRaise
    PInf exc1) (@StackRaise PFin exc2) (I2F_dvalue exc1 exc2)))) (_ : (∀ (e : (@exc PInf)), (P
    (@StackRaise PInf e) (@StackGetExc PFin) False))) (_ : (∀ (args0 : (List (Prod raw_id (@dvalue
    PFin)))), (P (@StackGetExc PInf) (@StackPush PFin args0) False))) (_ : (P (@StackGetExc PInf)
    (@StackPop PFin) False)) (_ : (∀ (e : (@exc PFin)), (P (@StackGetExc PInf) (@StackRaise PFin e)
    False))) (_ : (P (@StackGetExc PInf) (@StackGetExc PFin) True)) (s : (@StackE PInf).I) (s0 :
    (@StackE PFin).I), (P s s0 (I2FE_Stack s s0))) := by
  intro P h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15 h16 e f
  exact I2FE_Stack_graph_rect P h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15 h16
    (I2FE_Stack_graph_correct e f)

instance FunctionalInduction_I2FE_Stack :
    (FunctionalInduction.{0, 0} I2FE_Stack) := ⟨_, I2FE_Stack_graph_correct⟩

instance FunctionalElimination_I2FE_Stack :
    FunctionalElimination I2FE_Stack (∀ (P : (∀ (e : (@StackE PInf).I) (f : (@StackE PFin).I) (_ : Prop), Type u)) (_ : (∀ (args1 :
    (List (Prod raw_id (@dvalue PInf)))) (args2 : (List (Prod raw_id (@dvalue PFin)))), (P
    (@StackPush PInf args1) (@StackPush PFin args2) (List.Forall₂ (Utils.RelationsUtil.prod_rel Eq
    I2F_dvalue) args1 args2)))) (_ : (∀ (args0 : (List (Prod raw_id (@dvalue PInf)))), (P
    (@StackPush PInf args0) (@StackPop PFin) False))) (_ : (∀ (args0 : (List (Prod raw_id (@dvalue
    PInf)))) (e : (@exc PFin)), (P (@StackPush PInf args0) (@StackRaise PFin e) False))) (_ : (∀
    (args0 : (List (Prod raw_id (@dvalue PInf)))), (P (@StackPush PInf args0) (@StackGetExc PFin)
    False))) (_ : (∀ (args0 : (List (Prod raw_id (@dvalue PFin)))), (P (@StackPop PInf) (@StackPush
    PFin args0) False))) (_ : (P (@StackPop PInf) (@StackPop PFin) True)) (_ : (∀ (e : (@exc PFin)),
    (P (@StackPop PInf) (@StackRaise PFin e) False))) (_ : (P (@StackPop PInf) (@StackGetExc PFin)
    False)) (_ : (∀ (e : (@exc PInf)) (args0 : (List (Prod raw_id (@dvalue PFin)))), (P (@StackRaise
    PInf e) (@StackPush PFin args0) False))) (_ : (∀ (e : (@exc PInf)), (P (@StackRaise PInf e)
    (@StackPop PFin) False))) (_ : (∀ (exc1 : (@exc PInf)) (exc2 : (@exc PFin)), (P (@StackRaise
    PInf exc1) (@StackRaise PFin exc2) (I2F_dvalue exc1 exc2)))) (_ : (∀ (e : (@exc PInf)), (P
    (@StackRaise PInf e) (@StackGetExc PFin) False))) (_ : (∀ (args0 : (List (Prod raw_id (@dvalue
    PFin)))), (P (@StackGetExc PInf) (@StackPush PFin args0) False))) (_ : (P (@StackGetExc PInf)
    (@StackPop PFin) False)) (_ : (∀ (e : (@exc PFin)), (P (@StackGetExc PInf) (@StackRaise PFin e)
    False))) (_ : (P (@StackGetExc PInf) (@StackGetExc PFin) True)) (s : (@StackE PInf).I) (s0 :
    (@StackE PFin).I), (P s s0 (I2FE_Stack s s0))) 17 :=
  ⟨I2FE_Stack_elim⟩

theorem I2FE_Memory_equation_1 :
    (Eq (I2FE_Memory (@MemPush PInf) (@MemPush PFin)) True) := by rfl

theorem I2FE_Memory_equation_2 :
    (Eq (I2FE_Memory (@MemPush PInf) (@MemPop PFin)) False) := by rfl

theorem I2FE_Memory_equation_3 :
    (∀ (t : dtyp) (num_elements : Nat) (align0 : (Option Nat)), (Eq (I2FE_Memory (@MemPush PInf)
    (@Alloca PFin t num_elements align0)) False)) := by intros; rfl

theorem I2FE_Memory_equation_4 :
    (∀ (t0 : dtyp) (a : (@dvalue PFin)), (Eq (I2FE_Memory (@MemPush PInf) (@Load PFin t0 a)) False)) := by intros; rfl

theorem I2FE_Memory_equation_5 :
    (∀ (t1 : dtyp) (a0 v : (@dvalue PFin)), (Eq (I2FE_Memory (@MemPush PInf) (@Store PFin t1 a0 v))
    False)) := by intros; rfl

theorem I2FE_Memory_equation_6 :
    (∀ (cv : impure_conversion) (t_from : dtyp) (v0 : (@dvalue PFin)) (t_to : dtyp), (Eq
    (I2FE_Memory (@MemPush PInf) (@Conv PFin cv t_from v0 t_to)) False)) := by intros; rfl

theorem I2FE_Memory_equation_7 :
    (Eq (I2FE_Memory (@MemPop PInf) (@MemPush PFin)) False) := by rfl

theorem I2FE_Memory_equation_8 :
    (Eq (I2FE_Memory (@MemPop PInf) (@MemPop PFin)) True) := by rfl

theorem I2FE_Memory_equation_9 :
    (∀ (t : dtyp) (num_elements : Nat) (align0 : (Option Nat)), (Eq (I2FE_Memory (@MemPop PInf)
    (@Alloca PFin t num_elements align0)) False)) := by intros; rfl

theorem I2FE_Memory_equation_10 :
    (∀ (t0 : dtyp) (a : (@dvalue PFin)), (Eq (I2FE_Memory (@MemPop PInf) (@Load PFin t0 a)) False)) := by intros; rfl

theorem I2FE_Memory_equation_11 :
    (∀ (t1 : dtyp) (a0 v : (@dvalue PFin)), (Eq (I2FE_Memory (@MemPop PInf) (@Store PFin t1 a0 v))
    False)) := by intros; rfl

theorem I2FE_Memory_equation_12 :
    (∀ (cv : impure_conversion) (t_from : dtyp) (v0 : (@dvalue PFin)) (t_to : dtyp), (Eq
    (I2FE_Memory (@MemPop PInf) (@Conv PFin cv t_from v0 t_to)) False)) := by intros; rfl

theorem I2FE_Memory_equation_13 :
    (∀ (t : dtyp) (num_elements : Nat) (align0 : (Option Nat)), (Eq (I2FE_Memory (@Alloca PInf t
    num_elements align0) (@MemPush PFin)) False)) := by intros; rfl

theorem I2FE_Memory_equation_14 :
    (∀ (t : dtyp) (num_elements : Nat) (align0 : (Option Nat)), (Eq (I2FE_Memory (@Alloca PInf t
    num_elements align0) (@MemPop PFin)) False)) := by intros; rfl

theorem I2FE_Memory_equation_15 :
    (∀ (τ1 : dtyp) (n1 : Nat) (align1 : (Option Nat)) (τ2 : dtyp) (n2 : Nat) (align2 : (Option
    Nat)), (Eq (I2FE_Memory (@Alloca PInf τ1 n1 align1) (@Alloca PFin τ2 n2 align2)) (And (Eq τ1 τ2)
    (And (Eq n1 n2) (Eq align1 align2))))) := by intros; rfl

theorem I2FE_Memory_equation_16 :
    (∀ (t : dtyp) (num_elements : Nat) (align0 : (Option Nat)) (t1 : dtyp) (a : (@dvalue PFin)), (Eq
    (I2FE_Memory (@Alloca PInf t num_elements align0) (@Load PFin t1 a)) False)) := by intros; rfl

theorem I2FE_Memory_equation_17 :
    (∀ (t : dtyp) (num_elements : Nat) (align0 : (Option Nat)) (t2 : dtyp) (a0 v : (@dvalue PFin)),
    (Eq (I2FE_Memory (@Alloca PInf t num_elements align0) (@Store PFin t2 a0 v)) False)) := by intros; rfl

theorem I2FE_Memory_equation_18 :
    (∀ (t : dtyp) (num_elements : Nat) (align0 : (Option Nat)) (cv : impure_conversion) (t_from :
    dtyp) (v0 : (@dvalue PFin)) (t_to : dtyp), (Eq (I2FE_Memory (@Alloca PInf t num_elements align0)
    (@Conv PFin cv t_from v0 t_to)) False)) := by intros; rfl

theorem I2FE_Memory_equation_19 :
    (∀ (t0 : dtyp) (a : (@dvalue PInf)), (Eq (I2FE_Memory (@Load PInf t0 a) (@MemPush PFin)) False)) := by intros; rfl

theorem I2FE_Memory_equation_20 :
    (∀ (t0 : dtyp) (a : (@dvalue PInf)), (Eq (I2FE_Memory (@Load PInf t0 a) (@MemPop PFin)) False)) := by intros; rfl

theorem I2FE_Memory_equation_21 :
    (∀ (t0 : dtyp) (a : (@dvalue PInf)) (t : dtyp) (num_elements : Nat) (align0 : (Option Nat)), (Eq
    (I2FE_Memory (@Load PInf t0 a) (@Alloca PFin t num_elements align0)) False)) := by intros; rfl

theorem I2FE_Memory_equation_22 :
    (∀ (τ1 : dtyp) (a1 : (@dvalue PInf)) (τ2 : dtyp) (a2 : (@dvalue PFin)), (Eq (I2FE_Memory (@Load
    PInf τ1 a1) (@Load PFin τ2 a2)) (And (Eq τ1 τ2) (I2F_dvalue a1 a2)))) := by intros; rfl

theorem I2FE_Memory_equation_23 :
    (∀ (t0 : dtyp) (a : (@dvalue PInf)) (t2 : dtyp) (a1 v : (@dvalue PFin)), (Eq (I2FE_Memory (@Load
    PInf t0 a) (@Store PFin t2 a1 v)) False)) := by intros; rfl

theorem I2FE_Memory_equation_24 :
    (∀ (t0 : dtyp) (a : (@dvalue PInf)) (cv : impure_conversion) (t_from : dtyp) (v0 : (@dvalue
    PFin)) (t_to : dtyp), (Eq (I2FE_Memory (@Load PInf t0 a) (@Conv PFin cv t_from v0 t_to)) False)) := by intros; rfl

theorem I2FE_Memory_equation_25 :
    (∀ (t1 : dtyp) (a0 v : (@dvalue PInf)), (Eq (I2FE_Memory (@Store PInf t1 a0 v) (@MemPush PFin))
    False)) := by intros; rfl

theorem I2FE_Memory_equation_26 :
    (∀ (t1 : dtyp) (a0 v : (@dvalue PInf)), (Eq (I2FE_Memory (@Store PInf t1 a0 v) (@MemPop PFin))
    False)) := by intros; rfl

theorem I2FE_Memory_equation_27 :
    (∀ (t1 : dtyp) (a0 v : (@dvalue PInf)) (t : dtyp) (num_elements : Nat) (align0 : (Option Nat)),
    (Eq (I2FE_Memory (@Store PInf t1 a0 v) (@Alloca PFin t num_elements align0)) False)) := by intros; rfl

theorem I2FE_Memory_equation_28 :
    (∀ (t1 : dtyp) (a0 v : (@dvalue PInf)) (t0 : dtyp) (a : (@dvalue PFin)), (Eq (I2FE_Memory
    (@Store PInf t1 a0 v) (@Load PFin t0 a)) False)) := by intros; rfl

theorem I2FE_Memory_equation_29 :
    (∀ (τ1 : dtyp) (a1 v1 : (@dvalue PInf)) (τ2 : dtyp) (a2 v2 : (@dvalue PFin)), (Eq (I2FE_Memory
    (@Store PInf τ1 a1 v1) (@Store PFin τ2 a2 v2)) (And (Eq τ1 τ2) (And (I2F_dvalue a1 a2)
    (I2F_dvalue v1 v2))))) := by intros; rfl

theorem I2FE_Memory_equation_30 :
    (∀ (t1 : dtyp) (a0 v : (@dvalue PInf)) (cv : impure_conversion) (t_from : dtyp) (v1 : (@dvalue
    PFin)) (t_to : dtyp), (Eq (I2FE_Memory (@Store PInf t1 a0 v) (@Conv PFin cv t_from v1 t_to))
    False)) := by intros; rfl

theorem I2FE_Memory_equation_31 :
    (∀ (cv : impure_conversion) (t_from : dtyp) (v0 : (@dvalue PInf)) (t_to : dtyp), (Eq
    (I2FE_Memory (@Conv PInf cv t_from v0 t_to) (@MemPush PFin)) False)) := by intros; rfl

theorem I2FE_Memory_equation_32 :
    (∀ (cv : impure_conversion) (t_from : dtyp) (v0 : (@dvalue PInf)) (t_to : dtyp), (Eq
    (I2FE_Memory (@Conv PInf cv t_from v0 t_to) (@MemPop PFin)) False)) := by intros; rfl

theorem I2FE_Memory_equation_33 :
    (∀ (cv : impure_conversion) (t_from : dtyp) (v0 : (@dvalue PInf)) (t_to t : dtyp) (num_elements
    : Nat) (align0 : (Option Nat)), (Eq (I2FE_Memory (@Conv PInf cv t_from v0 t_to) (@Alloca PFin t
    num_elements align0)) False)) := by intros; rfl

theorem I2FE_Memory_equation_34 :
    (∀ (cv : impure_conversion) (t_from : dtyp) (v0 : (@dvalue PInf)) (t_to t0 : dtyp) (a : (@dvalue
    PFin)), (Eq (I2FE_Memory (@Conv PInf cv t_from v0 t_to) (@Load PFin t0 a)) False)) := by intros; rfl

theorem I2FE_Memory_equation_35 :
    (∀ (cv : impure_conversion) (t_from : dtyp) (v0 : (@dvalue PInf)) (t_to t1 : dtyp) (a0 v :
    (@dvalue PFin)), (Eq (I2FE_Memory (@Conv PInf cv t_from v0 t_to) (@Store PFin t1 a0 v)) False)) := by intros; rfl

theorem I2FE_Memory_equation_36 :
    (∀ (cv1 : impure_conversion) (tf1 : dtyp) (v1 : (@dvalue PInf)) (tt1 : dtyp) (cv2 :
    impure_conversion) (tf2 : dtyp) (v2 : (@dvalue PFin)) (tt2 : dtyp), (Eq (I2FE_Memory (@Conv PInf
    cv1 tf1 v1 tt1) (@Conv PFin cv2 tf2 v2 tt2)) (And (Eq cv1 cv2) (And (Eq tf1 tf2) (And
    (I2F_dvalue v1 v2) (Eq tt1 tt2)))))) := by intros; rfl

inductive I2FE_Memory_graph :
    (∀ (e : (@MemoryE PInf).I) (f : (@MemoryE PFin).I) (_ : Prop), Type) where
  | case1 :
      (I2FE_Memory_graph (@MemPush PInf) (@MemPush PFin) True)
  | case2 :
      (I2FE_Memory_graph (@MemPush PInf) (@MemPop PFin) False)
  | case3 :
      (∀ (t : dtyp) (num_elements : Nat) (align0 : (Option Nat)), (I2FE_Memory_graph (@MemPush PInf)
      (@Alloca PFin t num_elements align0) False))
  | case4 :
      (∀ (t0 : dtyp) (a : (@dvalue PFin)), (I2FE_Memory_graph (@MemPush PInf) (@Load PFin t0 a)
      False))
  | case5 :
      (∀ (t1 : dtyp) (a0 v : (@dvalue PFin)), (I2FE_Memory_graph (@MemPush PInf) (@Store PFin t1 a0
      v) False))
  | case6 :
      (∀ (cv : impure_conversion) (t_from : dtyp) (v0 : (@dvalue PFin)) (t_to : dtyp),
      (I2FE_Memory_graph (@MemPush PInf) (@Conv PFin cv t_from v0 t_to) False))
  | case7 :
      (I2FE_Memory_graph (@MemPop PInf) (@MemPush PFin) False)
  | case8 :
      (I2FE_Memory_graph (@MemPop PInf) (@MemPop PFin) True)
  | case9 :
      (∀ (t : dtyp) (num_elements : Nat) (align0 : (Option Nat)), (I2FE_Memory_graph (@MemPop PInf)
      (@Alloca PFin t num_elements align0) False))
  | case10 :
      (∀ (t0 : dtyp) (a : (@dvalue PFin)), (I2FE_Memory_graph (@MemPop PInf) (@Load PFin t0 a)
      False))
  | case11 :
      (∀ (t1 : dtyp) (a0 v : (@dvalue PFin)), (I2FE_Memory_graph (@MemPop PInf) (@Store PFin t1 a0
      v) False))
  | case12 :
      (∀ (cv : impure_conversion) (t_from : dtyp) (v0 : (@dvalue PFin)) (t_to : dtyp),
      (I2FE_Memory_graph (@MemPop PInf) (@Conv PFin cv t_from v0 t_to) False))
  | case13 :
      (∀ (t : dtyp) (num_elements : Nat) (align0 : (Option Nat)), (I2FE_Memory_graph (@Alloca PInf t
      num_elements align0) (@MemPush PFin) False))
  | case14 :
      (∀ (t : dtyp) (num_elements : Nat) (align0 : (Option Nat)), (I2FE_Memory_graph (@Alloca PInf t
      num_elements align0) (@MemPop PFin) False))
  | case15 :
      (∀ (τ1 : dtyp) (n1 : Nat) (align1 : (Option Nat)) (τ2 : dtyp) (n2 : Nat) (align2 : (Option
      Nat)), (I2FE_Memory_graph (@Alloca PInf τ1 n1 align1) (@Alloca PFin τ2 n2 align2) (And (Eq τ1
      τ2) (And (Eq n1 n2) (Eq align1 align2)))))
  | case16 :
      (∀ (t : dtyp) (num_elements : Nat) (align0 : (Option Nat)) (t1 : dtyp) (a : (@dvalue PFin)),
      (I2FE_Memory_graph (@Alloca PInf t num_elements align0) (@Load PFin t1 a) False))
  | case17 :
      (∀ (t : dtyp) (num_elements : Nat) (align0 : (Option Nat)) (t2 : dtyp) (a0 v : (@dvalue
      PFin)), (I2FE_Memory_graph (@Alloca PInf t num_elements align0) (@Store PFin t2 a0 v) False))
  | case18 :
      (∀ (t : dtyp) (num_elements : Nat) (align0 : (Option Nat)) (cv : impure_conversion) (t_from :
      dtyp) (v0 : (@dvalue PFin)) (t_to : dtyp), (I2FE_Memory_graph (@Alloca PInf t num_elements
      align0) (@Conv PFin cv t_from v0 t_to) False))
  | case19 :
      (∀ (t0 : dtyp) (a : (@dvalue PInf)), (I2FE_Memory_graph (@Load PInf t0 a) (@MemPush PFin)
      False))
  | case20 :
      (∀ (t0 : dtyp) (a : (@dvalue PInf)), (I2FE_Memory_graph (@Load PInf t0 a) (@MemPop PFin)
      False))
  | case21 :
      (∀ (t0 : dtyp) (a : (@dvalue PInf)) (t : dtyp) (num_elements : Nat) (align0 : (Option Nat)),
      (I2FE_Memory_graph (@Load PInf t0 a) (@Alloca PFin t num_elements align0) False))
  | case22 :
      (∀ (τ1 : dtyp) (a1 : (@dvalue PInf)) (τ2 : dtyp) (a2 : (@dvalue PFin)), (I2FE_Memory_graph
      (@Load PInf τ1 a1) (@Load PFin τ2 a2) (And (Eq τ1 τ2) (I2F_dvalue a1 a2))))
  | case23 :
      (∀ (t0 : dtyp) (a : (@dvalue PInf)) (t2 : dtyp) (a1 v : (@dvalue PFin)), (I2FE_Memory_graph
      (@Load PInf t0 a) (@Store PFin t2 a1 v) False))
  | case24 :
      (∀ (t0 : dtyp) (a : (@dvalue PInf)) (cv : impure_conversion) (t_from : dtyp) (v0 : (@dvalue
      PFin)) (t_to : dtyp), (I2FE_Memory_graph (@Load PInf t0 a) (@Conv PFin cv t_from v0 t_to)
      False))
  | case25 :
      (∀ (t1 : dtyp) (a0 v : (@dvalue PInf)), (I2FE_Memory_graph (@Store PInf t1 a0 v) (@MemPush
      PFin) False))
  | case26 :
      (∀ (t1 : dtyp) (a0 v : (@dvalue PInf)), (I2FE_Memory_graph (@Store PInf t1 a0 v) (@MemPop
      PFin) False))
  | case27 :
      (∀ (t1 : dtyp) (a0 v : (@dvalue PInf)) (t : dtyp) (num_elements : Nat) (align0 : (Option
      Nat)), (I2FE_Memory_graph (@Store PInf t1 a0 v) (@Alloca PFin t num_elements align0) False))
  | case28 :
      (∀ (t1 : dtyp) (a0 v : (@dvalue PInf)) (t0 : dtyp) (a : (@dvalue PFin)), (I2FE_Memory_graph
      (@Store PInf t1 a0 v) (@Load PFin t0 a) False))
  | case29 :
      (∀ (τ1 : dtyp) (a1 v1 : (@dvalue PInf)) (τ2 : dtyp) (a2 v2 : (@dvalue PFin)),
      (I2FE_Memory_graph (@Store PInf τ1 a1 v1) (@Store PFin τ2 a2 v2) (And (Eq τ1 τ2) (And
      (I2F_dvalue a1 a2) (I2F_dvalue v1 v2)))))
  | case30 :
      (∀ (t1 : dtyp) (a0 v : (@dvalue PInf)) (cv : impure_conversion) (t_from : dtyp) (v1 : (@dvalue
      PFin)) (t_to : dtyp), (I2FE_Memory_graph (@Store PInf t1 a0 v) (@Conv PFin cv t_from v1 t_to)
      False))
  | case31 :
      (∀ (cv : impure_conversion) (t_from : dtyp) (v0 : (@dvalue PInf)) (t_to : dtyp),
      (I2FE_Memory_graph (@Conv PInf cv t_from v0 t_to) (@MemPush PFin) False))
  | case32 :
      (∀ (cv : impure_conversion) (t_from : dtyp) (v0 : (@dvalue PInf)) (t_to : dtyp),
      (I2FE_Memory_graph (@Conv PInf cv t_from v0 t_to) (@MemPop PFin) False))
  | case33 :
      (∀ (cv : impure_conversion) (t_from : dtyp) (v0 : (@dvalue PInf)) (t_to t : dtyp)
      (num_elements : Nat) (align0 : (Option Nat)), (I2FE_Memory_graph (@Conv PInf cv t_from v0
      t_to) (@Alloca PFin t num_elements align0) False))
  | case34 :
      (∀ (cv : impure_conversion) (t_from : dtyp) (v0 : (@dvalue PInf)) (t_to t0 : dtyp) (a :
      (@dvalue PFin)), (I2FE_Memory_graph (@Conv PInf cv t_from v0 t_to) (@Load PFin t0 a) False))
  | case35 :
      (∀ (cv : impure_conversion) (t_from : dtyp) (v0 : (@dvalue PInf)) (t_to t1 : dtyp) (a0 v :
      (@dvalue PFin)), (I2FE_Memory_graph (@Conv PInf cv t_from v0 t_to) (@Store PFin t1 a0 v)
      False))
  | case36 :
      (∀ (cv1 : impure_conversion) (tf1 : dtyp) (v1 : (@dvalue PInf)) (tt1 : dtyp) (cv2 :
      impure_conversion) (tf2 : dtyp) (v2 : (@dvalue PFin)) (tt2 : dtyp), (I2FE_Memory_graph (@Conv
      PInf cv1 tf1 v1 tt1) (@Conv PFin cv2 tf2 v2 tt2) (And (Eq cv1 cv2) (And (Eq tf1 tf2) (And
      (I2F_dvalue v1 v2) (Eq tt1 tt2))))))

abbrev I2FE_Memory_graph_equation_1 := @I2FE_Memory_graph.case1
abbrev I2FE_Memory_graph_equation_2 := @I2FE_Memory_graph.case2
abbrev I2FE_Memory_graph_equation_3 := @I2FE_Memory_graph.case3
abbrev I2FE_Memory_graph_equation_4 := @I2FE_Memory_graph.case4
abbrev I2FE_Memory_graph_equation_5 := @I2FE_Memory_graph.case5
abbrev I2FE_Memory_graph_equation_6 := @I2FE_Memory_graph.case6
abbrev I2FE_Memory_graph_equation_7 := @I2FE_Memory_graph.case7
abbrev I2FE_Memory_graph_equation_8 := @I2FE_Memory_graph.case8
abbrev I2FE_Memory_graph_equation_9 := @I2FE_Memory_graph.case9
abbrev I2FE_Memory_graph_equation_10 := @I2FE_Memory_graph.case10
abbrev I2FE_Memory_graph_equation_11 := @I2FE_Memory_graph.case11
abbrev I2FE_Memory_graph_equation_12 := @I2FE_Memory_graph.case12
abbrev I2FE_Memory_graph_equation_13 := @I2FE_Memory_graph.case13
abbrev I2FE_Memory_graph_equation_14 := @I2FE_Memory_graph.case14
abbrev I2FE_Memory_graph_equation_15 := @I2FE_Memory_graph.case15
abbrev I2FE_Memory_graph_equation_16 := @I2FE_Memory_graph.case16
abbrev I2FE_Memory_graph_equation_17 := @I2FE_Memory_graph.case17
abbrev I2FE_Memory_graph_equation_18 := @I2FE_Memory_graph.case18
abbrev I2FE_Memory_graph_equation_19 := @I2FE_Memory_graph.case19
abbrev I2FE_Memory_graph_equation_20 := @I2FE_Memory_graph.case20
abbrev I2FE_Memory_graph_equation_21 := @I2FE_Memory_graph.case21
abbrev I2FE_Memory_graph_equation_22 := @I2FE_Memory_graph.case22
abbrev I2FE_Memory_graph_equation_23 := @I2FE_Memory_graph.case23
abbrev I2FE_Memory_graph_equation_24 := @I2FE_Memory_graph.case24
abbrev I2FE_Memory_graph_equation_25 := @I2FE_Memory_graph.case25
abbrev I2FE_Memory_graph_equation_26 := @I2FE_Memory_graph.case26
abbrev I2FE_Memory_graph_equation_27 := @I2FE_Memory_graph.case27
abbrev I2FE_Memory_graph_equation_28 := @I2FE_Memory_graph.case28
abbrev I2FE_Memory_graph_equation_29 := @I2FE_Memory_graph.case29
abbrev I2FE_Memory_graph_equation_30 := @I2FE_Memory_graph.case30
abbrev I2FE_Memory_graph_equation_31 := @I2FE_Memory_graph.case31
abbrev I2FE_Memory_graph_equation_32 := @I2FE_Memory_graph.case32
abbrev I2FE_Memory_graph_equation_33 := @I2FE_Memory_graph.case33
abbrev I2FE_Memory_graph_equation_34 := @I2FE_Memory_graph.case34
abbrev I2FE_Memory_graph_equation_35 := @I2FE_Memory_graph.case35
abbrev I2FE_Memory_graph_equation_36 := @I2FE_Memory_graph.case36

def I2FE_Memory_graph_rect :
    (∀ (P : (∀ (e : (@MemoryE PInf).I) (f : (@MemoryE PFin).I) (_ : Prop), Type u)) (_ : (P
    (@MemPush PInf) (@MemPush PFin) True)) (_ : (P (@MemPush PInf) (@MemPop PFin) False)) (_ : (∀ (t
    : dtyp) (num_elements : Nat) (align0 : (Option Nat)), (P (@MemPush PInf) (@Alloca PFin t
    num_elements align0) False))) (_ : (∀ (t0 : dtyp) (a : (@dvalue PFin)), (P (@MemPush PInf)
    (@Load PFin t0 a) False))) (_ : (∀ (t1 : dtyp) (a0 v : (@dvalue PFin)), (P (@MemPush PInf)
    (@Store PFin t1 a0 v) False))) (_ : (∀ (cv : impure_conversion) (t_from : dtyp) (v0 : (@dvalue
    PFin)) (t_to : dtyp), (P (@MemPush PInf) (@Conv PFin cv t_from v0 t_to) False))) (_ : (P
    (@MemPop PInf) (@MemPush PFin) False)) (_ : (P (@MemPop PInf) (@MemPop PFin) True)) (_ : (∀ (t :
    dtyp) (num_elements : Nat) (align0 : (Option Nat)), (P (@MemPop PInf) (@Alloca PFin t
    num_elements align0) False))) (_ : (∀ (t0 : dtyp) (a : (@dvalue PFin)), (P (@MemPop PInf) (@Load
    PFin t0 a) False))) (_ : (∀ (t1 : dtyp) (a0 v : (@dvalue PFin)), (P (@MemPop PInf) (@Store PFin
    t1 a0 v) False))) (_ : (∀ (cv : impure_conversion) (t_from : dtyp) (v0 : (@dvalue PFin)) (t_to :
    dtyp), (P (@MemPop PInf) (@Conv PFin cv t_from v0 t_to) False))) (_ : (∀ (t : dtyp)
    (num_elements : Nat) (align0 : (Option Nat)), (P (@Alloca PInf t num_elements align0) (@MemPush
    PFin) False))) (_ : (∀ (t : dtyp) (num_elements : Nat) (align0 : (Option Nat)), (P (@Alloca PInf
    t num_elements align0) (@MemPop PFin) False))) (_ : (∀ (τ1 : dtyp) (n1 : Nat) (align1 : (Option
    Nat)) (τ2 : dtyp) (n2 : Nat) (align2 : (Option Nat)), (P (@Alloca PInf τ1 n1 align1) (@Alloca
    PFin τ2 n2 align2) (And (Eq τ1 τ2) (And (Eq n1 n2) (Eq align1 align2)))))) (_ : (∀ (t : dtyp)
    (num_elements : Nat) (align0 : (Option Nat)) (t1 : dtyp) (a : (@dvalue PFin)), (P (@Alloca PInf
    t num_elements align0) (@Load PFin t1 a) False))) (_ : (∀ (t : dtyp) (num_elements : Nat)
    (align0 : (Option Nat)) (t2 : dtyp) (a0 v : (@dvalue PFin)), (P (@Alloca PInf t num_elements
    align0) (@Store PFin t2 a0 v) False))) (_ : (∀ (t : dtyp) (num_elements : Nat) (align0 : (Option
    Nat)) (cv : impure_conversion) (t_from : dtyp) (v0 : (@dvalue PFin)) (t_to : dtyp), (P (@Alloca
    PInf t num_elements align0) (@Conv PFin cv t_from v0 t_to) False))) (_ : (∀ (t0 : dtyp) (a :
    (@dvalue PInf)), (P (@Load PInf t0 a) (@MemPush PFin) False))) (_ : (∀ (t0 : dtyp) (a : (@dvalue
    PInf)), (P (@Load PInf t0 a) (@MemPop PFin) False))) (_ : (∀ (t0 : dtyp) (a : (@dvalue PInf)) (t
    : dtyp) (num_elements : Nat) (align0 : (Option Nat)), (P (@Load PInf t0 a) (@Alloca PFin t
    num_elements align0) False))) (_ : (∀ (τ1 : dtyp) (a1 : (@dvalue PInf)) (τ2 : dtyp) (a2 :
    (@dvalue PFin)), (P (@Load PInf τ1 a1) (@Load PFin τ2 a2) (And (Eq τ1 τ2) (I2F_dvalue a1 a2)))))
    (_ : (∀ (t0 : dtyp) (a : (@dvalue PInf)) (t2 : dtyp) (a1 v : (@dvalue PFin)), (P (@Load PInf t0
    a) (@Store PFin t2 a1 v) False))) (_ : (∀ (t0 : dtyp) (a : (@dvalue PInf)) (cv :
    impure_conversion) (t_from : dtyp) (v0 : (@dvalue PFin)) (t_to : dtyp), (P (@Load PInf t0 a)
    (@Conv PFin cv t_from v0 t_to) False))) (_ : (∀ (t1 : dtyp) (a0 v : (@dvalue PInf)), (P (@Store
    PInf t1 a0 v) (@MemPush PFin) False))) (_ : (∀ (t1 : dtyp) (a0 v : (@dvalue PInf)), (P (@Store
    PInf t1 a0 v) (@MemPop PFin) False))) (_ : (∀ (t1 : dtyp) (a0 v : (@dvalue PInf)) (t : dtyp)
    (num_elements : Nat) (align0 : (Option Nat)), (P (@Store PInf t1 a0 v) (@Alloca PFin t
    num_elements align0) False))) (_ : (∀ (t1 : dtyp) (a0 v : (@dvalue PInf)) (t0 : dtyp) (a :
    (@dvalue PFin)), (P (@Store PInf t1 a0 v) (@Load PFin t0 a) False))) (_ : (∀ (τ1 : dtyp) (a1 v1
    : (@dvalue PInf)) (τ2 : dtyp) (a2 v2 : (@dvalue PFin)), (P (@Store PInf τ1 a1 v1) (@Store PFin
    τ2 a2 v2) (And (Eq τ1 τ2) (And (I2F_dvalue a1 a2) (I2F_dvalue v1 v2)))))) (_ : (∀ (t1 : dtyp)
    (a0 v : (@dvalue PInf)) (cv : impure_conversion) (t_from : dtyp) (v1 : (@dvalue PFin)) (t_to :
    dtyp), (P (@Store PInf t1 a0 v) (@Conv PFin cv t_from v1 t_to) False))) (_ : (∀ (cv :
    impure_conversion) (t_from : dtyp) (v0 : (@dvalue PInf)) (t_to : dtyp), (P (@Conv PInf cv t_from
    v0 t_to) (@MemPush PFin) False))) (_ : (∀ (cv : impure_conversion) (t_from : dtyp) (v0 :
    (@dvalue PInf)) (t_to : dtyp), (P (@Conv PInf cv t_from v0 t_to) (@MemPop PFin) False))) (_ : (∀
    (cv : impure_conversion) (t_from : dtyp) (v0 : (@dvalue PInf)) (t_to t : dtyp) (num_elements :
    Nat) (align0 : (Option Nat)), (P (@Conv PInf cv t_from v0 t_to) (@Alloca PFin t num_elements
    align0) False))) (_ : (∀ (cv : impure_conversion) (t_from : dtyp) (v0 : (@dvalue PInf)) (t_to t0
    : dtyp) (a : (@dvalue PFin)), (P (@Conv PInf cv t_from v0 t_to) (@Load PFin t0 a) False))) (_ :
    (∀ (cv : impure_conversion) (t_from : dtyp) (v0 : (@dvalue PInf)) (t_to t1 : dtyp) (a0 v :
    (@dvalue PFin)), (P (@Conv PInf cv t_from v0 t_to) (@Store PFin t1 a0 v) False))) (_ : (∀ (cv1 :
    impure_conversion) (tf1 : dtyp) (v1 : (@dvalue PInf)) (tt1 : dtyp) (cv2 : impure_conversion)
    (tf2 : dtyp) (v2 : (@dvalue PFin)) (tt2 : dtyp), (P (@Conv PInf cv1 tf1 v1 tt1) (@Conv PFin cv2
    tf2 v2 tt2) (And (Eq cv1 cv2) (And (Eq tf1 tf2) (And (I2F_dvalue v1 v2) (Eq tt1 tt2))))))) {m :
    (@MemoryE PInf).I} {m0 : (@MemoryE PFin).I} {P0 : Prop} (_ : (I2FE_Memory_graph m m0 P0)), (P m
    m0 P0)) := by
  intro P h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15 h16 h17 h18 h19 h20 h21 h22 h23 h24 h25 h26 h27 h28 h29 h30 h31 h32 h33 h34 h35 h36 e f p witness
  cases witness
  next => apply h1
  next => apply h2
  next => apply h3
  next => apply h4
  next => apply h5
  next => apply h6
  next => apply h7
  next => apply h8
  next => apply h9
  next => apply h10
  next => apply h11
  next => apply h12
  next => apply h13
  next => apply h14
  next => apply h15
  next => apply h16
  next => apply h17
  next => apply h18
  next => apply h19
  next => apply h20
  next => apply h21
  next => apply h22
  next => apply h23
  next => apply h24
  next => apply h25
  next => apply h26
  next => apply h27
  next => apply h28
  next => apply h29
  next => apply h30
  next => apply h31
  next => apply h32
  next => apply h33
  next => apply h34
  next => apply h35
  next => apply h36

def I2FE_Memory_graph_correct :
    (∀ (m : (@MemoryE PInf).I) (m0 : (@MemoryE PFin).I), (I2FE_Memory_graph m m0 (I2FE_Memory m
    m0))) := by
  intro e f
  cases e <;> cases f <;> first
    | apply I2FE_Memory_graph.case1
    | apply I2FE_Memory_graph.case2
    | apply I2FE_Memory_graph.case3
    | apply I2FE_Memory_graph.case4
    | apply I2FE_Memory_graph.case5
    | apply I2FE_Memory_graph.case6
    | apply I2FE_Memory_graph.case7
    | apply I2FE_Memory_graph.case8
    | apply I2FE_Memory_graph.case9
    | apply I2FE_Memory_graph.case10
    | apply I2FE_Memory_graph.case11
    | apply I2FE_Memory_graph.case12
    | apply I2FE_Memory_graph.case13
    | apply I2FE_Memory_graph.case14
    | apply I2FE_Memory_graph.case15
    | apply I2FE_Memory_graph.case16
    | apply I2FE_Memory_graph.case17
    | apply I2FE_Memory_graph.case18
    | apply I2FE_Memory_graph.case19
    | apply I2FE_Memory_graph.case20
    | apply I2FE_Memory_graph.case21
    | apply I2FE_Memory_graph.case22
    | apply I2FE_Memory_graph.case23
    | apply I2FE_Memory_graph.case24
    | apply I2FE_Memory_graph.case25
    | apply I2FE_Memory_graph.case26
    | apply I2FE_Memory_graph.case27
    | apply I2FE_Memory_graph.case28
    | apply I2FE_Memory_graph.case29
    | apply I2FE_Memory_graph.case30
    | apply I2FE_Memory_graph.case31
    | apply I2FE_Memory_graph.case32
    | apply I2FE_Memory_graph.case33
    | apply I2FE_Memory_graph.case34
    | apply I2FE_Memory_graph.case35
    | apply I2FE_Memory_graph.case36

def I2FE_Memory_elim :
    (∀ (P : (∀ (e : (@MemoryE PInf).I) (f : (@MemoryE PFin).I) (_ : Prop), Type u)) (_ : (P
    (@MemPush PInf) (@MemPush PFin) True)) (_ : (P (@MemPush PInf) (@MemPop PFin) False)) (_ : (∀ (t
    : dtyp) (num_elements : Nat) (align0 : (Option Nat)), (P (@MemPush PInf) (@Alloca PFin t
    num_elements align0) False))) (_ : (∀ (t0 : dtyp) (a : (@dvalue PFin)), (P (@MemPush PInf)
    (@Load PFin t0 a) False))) (_ : (∀ (t1 : dtyp) (a0 v : (@dvalue PFin)), (P (@MemPush PInf)
    (@Store PFin t1 a0 v) False))) (_ : (∀ (cv : impure_conversion) (t_from : dtyp) (v0 : (@dvalue
    PFin)) (t_to : dtyp), (P (@MemPush PInf) (@Conv PFin cv t_from v0 t_to) False))) (_ : (P
    (@MemPop PInf) (@MemPush PFin) False)) (_ : (P (@MemPop PInf) (@MemPop PFin) True)) (_ : (∀ (t :
    dtyp) (num_elements : Nat) (align0 : (Option Nat)), (P (@MemPop PInf) (@Alloca PFin t
    num_elements align0) False))) (_ : (∀ (t0 : dtyp) (a : (@dvalue PFin)), (P (@MemPop PInf) (@Load
    PFin t0 a) False))) (_ : (∀ (t1 : dtyp) (a0 v : (@dvalue PFin)), (P (@MemPop PInf) (@Store PFin
    t1 a0 v) False))) (_ : (∀ (cv : impure_conversion) (t_from : dtyp) (v0 : (@dvalue PFin)) (t_to :
    dtyp), (P (@MemPop PInf) (@Conv PFin cv t_from v0 t_to) False))) (_ : (∀ (t : dtyp)
    (num_elements : Nat) (align0 : (Option Nat)), (P (@Alloca PInf t num_elements align0) (@MemPush
    PFin) False))) (_ : (∀ (t : dtyp) (num_elements : Nat) (align0 : (Option Nat)), (P (@Alloca PInf
    t num_elements align0) (@MemPop PFin) False))) (_ : (∀ (τ1 : dtyp) (n1 : Nat) (align1 : (Option
    Nat)) (τ2 : dtyp) (n2 : Nat) (align2 : (Option Nat)), (P (@Alloca PInf τ1 n1 align1) (@Alloca
    PFin τ2 n2 align2) (And (Eq τ1 τ2) (And (Eq n1 n2) (Eq align1 align2)))))) (_ : (∀ (t : dtyp)
    (num_elements : Nat) (align0 : (Option Nat)) (t1 : dtyp) (a : (@dvalue PFin)), (P (@Alloca PInf
    t num_elements align0) (@Load PFin t1 a) False))) (_ : (∀ (t : dtyp) (num_elements : Nat)
    (align0 : (Option Nat)) (t2 : dtyp) (a0 v : (@dvalue PFin)), (P (@Alloca PInf t num_elements
    align0) (@Store PFin t2 a0 v) False))) (_ : (∀ (t : dtyp) (num_elements : Nat) (align0 : (Option
    Nat)) (cv : impure_conversion) (t_from : dtyp) (v0 : (@dvalue PFin)) (t_to : dtyp), (P (@Alloca
    PInf t num_elements align0) (@Conv PFin cv t_from v0 t_to) False))) (_ : (∀ (t0 : dtyp) (a :
    (@dvalue PInf)), (P (@Load PInf t0 a) (@MemPush PFin) False))) (_ : (∀ (t0 : dtyp) (a : (@dvalue
    PInf)), (P (@Load PInf t0 a) (@MemPop PFin) False))) (_ : (∀ (t0 : dtyp) (a : (@dvalue PInf)) (t
    : dtyp) (num_elements : Nat) (align0 : (Option Nat)), (P (@Load PInf t0 a) (@Alloca PFin t
    num_elements align0) False))) (_ : (∀ (τ1 : dtyp) (a1 : (@dvalue PInf)) (τ2 : dtyp) (a2 :
    (@dvalue PFin)), (P (@Load PInf τ1 a1) (@Load PFin τ2 a2) (And (Eq τ1 τ2) (I2F_dvalue a1 a2)))))
    (_ : (∀ (t0 : dtyp) (a : (@dvalue PInf)) (t2 : dtyp) (a1 v : (@dvalue PFin)), (P (@Load PInf t0
    a) (@Store PFin t2 a1 v) False))) (_ : (∀ (t0 : dtyp) (a : (@dvalue PInf)) (cv :
    impure_conversion) (t_from : dtyp) (v0 : (@dvalue PFin)) (t_to : dtyp), (P (@Load PInf t0 a)
    (@Conv PFin cv t_from v0 t_to) False))) (_ : (∀ (t1 : dtyp) (a0 v : (@dvalue PInf)), (P (@Store
    PInf t1 a0 v) (@MemPush PFin) False))) (_ : (∀ (t1 : dtyp) (a0 v : (@dvalue PInf)), (P (@Store
    PInf t1 a0 v) (@MemPop PFin) False))) (_ : (∀ (t1 : dtyp) (a0 v : (@dvalue PInf)) (t : dtyp)
    (num_elements : Nat) (align0 : (Option Nat)), (P (@Store PInf t1 a0 v) (@Alloca PFin t
    num_elements align0) False))) (_ : (∀ (t1 : dtyp) (a0 v : (@dvalue PInf)) (t0 : dtyp) (a :
    (@dvalue PFin)), (P (@Store PInf t1 a0 v) (@Load PFin t0 a) False))) (_ : (∀ (τ1 : dtyp) (a1 v1
    : (@dvalue PInf)) (τ2 : dtyp) (a2 v2 : (@dvalue PFin)), (P (@Store PInf τ1 a1 v1) (@Store PFin
    τ2 a2 v2) (And (Eq τ1 τ2) (And (I2F_dvalue a1 a2) (I2F_dvalue v1 v2)))))) (_ : (∀ (t1 : dtyp)
    (a0 v : (@dvalue PInf)) (cv : impure_conversion) (t_from : dtyp) (v1 : (@dvalue PFin)) (t_to :
    dtyp), (P (@Store PInf t1 a0 v) (@Conv PFin cv t_from v1 t_to) False))) (_ : (∀ (cv :
    impure_conversion) (t_from : dtyp) (v0 : (@dvalue PInf)) (t_to : dtyp), (P (@Conv PInf cv t_from
    v0 t_to) (@MemPush PFin) False))) (_ : (∀ (cv : impure_conversion) (t_from : dtyp) (v0 :
    (@dvalue PInf)) (t_to : dtyp), (P (@Conv PInf cv t_from v0 t_to) (@MemPop PFin) False))) (_ : (∀
    (cv : impure_conversion) (t_from : dtyp) (v0 : (@dvalue PInf)) (t_to t : dtyp) (num_elements :
    Nat) (align0 : (Option Nat)), (P (@Conv PInf cv t_from v0 t_to) (@Alloca PFin t num_elements
    align0) False))) (_ : (∀ (cv : impure_conversion) (t_from : dtyp) (v0 : (@dvalue PInf)) (t_to t0
    : dtyp) (a : (@dvalue PFin)), (P (@Conv PInf cv t_from v0 t_to) (@Load PFin t0 a) False))) (_ :
    (∀ (cv : impure_conversion) (t_from : dtyp) (v0 : (@dvalue PInf)) (t_to t1 : dtyp) (a0 v :
    (@dvalue PFin)), (P (@Conv PInf cv t_from v0 t_to) (@Store PFin t1 a0 v) False))) (_ : (∀ (cv1 :
    impure_conversion) (tf1 : dtyp) (v1 : (@dvalue PInf)) (tt1 : dtyp) (cv2 : impure_conversion)
    (tf2 : dtyp) (v2 : (@dvalue PFin)) (tt2 : dtyp), (P (@Conv PInf cv1 tf1 v1 tt1) (@Conv PFin cv2
    tf2 v2 tt2) (And (Eq cv1 cv2) (And (Eq tf1 tf2) (And (I2F_dvalue v1 v2) (Eq tt1 tt2))))))) (m :
    (@MemoryE PInf).I) (m0 : (@MemoryE PFin).I), (P m m0 (I2FE_Memory m m0))) := by
  intro P h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15 h16 h17 h18 h19 h20 h21 h22 h23 h24 h25 h26 h27 h28 h29 h30 h31 h32 h33 h34 h35 h36 e f
  exact I2FE_Memory_graph_rect P h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15 h16 h17 h18 h19 h20
    h21 h22 h23 h24 h25 h26 h27 h28 h29 h30 h31 h32 h33 h34 h35 h36 (I2FE_Memory_graph_correct e f)

instance FunctionalInduction_I2FE_Memory :
    (FunctionalInduction.{0, 0} I2FE_Memory) := ⟨_, I2FE_Memory_graph_correct⟩

instance FunctionalElimination_I2FE_Memory :
    FunctionalElimination I2FE_Memory (∀ (P : (∀ (e : (@MemoryE PInf).I) (f : (@MemoryE PFin).I) (_ : Prop), Type u)) (_ : (P
    (@MemPush PInf) (@MemPush PFin) True)) (_ : (P (@MemPush PInf) (@MemPop PFin) False)) (_ : (∀ (t
    : dtyp) (num_elements : Nat) (align0 : (Option Nat)), (P (@MemPush PInf) (@Alloca PFin t
    num_elements align0) False))) (_ : (∀ (t0 : dtyp) (a : (@dvalue PFin)), (P (@MemPush PInf)
    (@Load PFin t0 a) False))) (_ : (∀ (t1 : dtyp) (a0 v : (@dvalue PFin)), (P (@MemPush PInf)
    (@Store PFin t1 a0 v) False))) (_ : (∀ (cv : impure_conversion) (t_from : dtyp) (v0 : (@dvalue
    PFin)) (t_to : dtyp), (P (@MemPush PInf) (@Conv PFin cv t_from v0 t_to) False))) (_ : (P
    (@MemPop PInf) (@MemPush PFin) False)) (_ : (P (@MemPop PInf) (@MemPop PFin) True)) (_ : (∀ (t :
    dtyp) (num_elements : Nat) (align0 : (Option Nat)), (P (@MemPop PInf) (@Alloca PFin t
    num_elements align0) False))) (_ : (∀ (t0 : dtyp) (a : (@dvalue PFin)), (P (@MemPop PInf) (@Load
    PFin t0 a) False))) (_ : (∀ (t1 : dtyp) (a0 v : (@dvalue PFin)), (P (@MemPop PInf) (@Store PFin
    t1 a0 v) False))) (_ : (∀ (cv : impure_conversion) (t_from : dtyp) (v0 : (@dvalue PFin)) (t_to :
    dtyp), (P (@MemPop PInf) (@Conv PFin cv t_from v0 t_to) False))) (_ : (∀ (t : dtyp)
    (num_elements : Nat) (align0 : (Option Nat)), (P (@Alloca PInf t num_elements align0) (@MemPush
    PFin) False))) (_ : (∀ (t : dtyp) (num_elements : Nat) (align0 : (Option Nat)), (P (@Alloca PInf
    t num_elements align0) (@MemPop PFin) False))) (_ : (∀ (τ1 : dtyp) (n1 : Nat) (align1 : (Option
    Nat)) (τ2 : dtyp) (n2 : Nat) (align2 : (Option Nat)), (P (@Alloca PInf τ1 n1 align1) (@Alloca
    PFin τ2 n2 align2) (And (Eq τ1 τ2) (And (Eq n1 n2) (Eq align1 align2)))))) (_ : (∀ (t : dtyp)
    (num_elements : Nat) (align0 : (Option Nat)) (t1 : dtyp) (a : (@dvalue PFin)), (P (@Alloca PInf
    t num_elements align0) (@Load PFin t1 a) False))) (_ : (∀ (t : dtyp) (num_elements : Nat)
    (align0 : (Option Nat)) (t2 : dtyp) (a0 v : (@dvalue PFin)), (P (@Alloca PInf t num_elements
    align0) (@Store PFin t2 a0 v) False))) (_ : (∀ (t : dtyp) (num_elements : Nat) (align0 : (Option
    Nat)) (cv : impure_conversion) (t_from : dtyp) (v0 : (@dvalue PFin)) (t_to : dtyp), (P (@Alloca
    PInf t num_elements align0) (@Conv PFin cv t_from v0 t_to) False))) (_ : (∀ (t0 : dtyp) (a :
    (@dvalue PInf)), (P (@Load PInf t0 a) (@MemPush PFin) False))) (_ : (∀ (t0 : dtyp) (a : (@dvalue
    PInf)), (P (@Load PInf t0 a) (@MemPop PFin) False))) (_ : (∀ (t0 : dtyp) (a : (@dvalue PInf)) (t
    : dtyp) (num_elements : Nat) (align0 : (Option Nat)), (P (@Load PInf t0 a) (@Alloca PFin t
    num_elements align0) False))) (_ : (∀ (τ1 : dtyp) (a1 : (@dvalue PInf)) (τ2 : dtyp) (a2 :
    (@dvalue PFin)), (P (@Load PInf τ1 a1) (@Load PFin τ2 a2) (And (Eq τ1 τ2) (I2F_dvalue a1 a2)))))
    (_ : (∀ (t0 : dtyp) (a : (@dvalue PInf)) (t2 : dtyp) (a1 v : (@dvalue PFin)), (P (@Load PInf t0
    a) (@Store PFin t2 a1 v) False))) (_ : (∀ (t0 : dtyp) (a : (@dvalue PInf)) (cv :
    impure_conversion) (t_from : dtyp) (v0 : (@dvalue PFin)) (t_to : dtyp), (P (@Load PInf t0 a)
    (@Conv PFin cv t_from v0 t_to) False))) (_ : (∀ (t1 : dtyp) (a0 v : (@dvalue PInf)), (P (@Store
    PInf t1 a0 v) (@MemPush PFin) False))) (_ : (∀ (t1 : dtyp) (a0 v : (@dvalue PInf)), (P (@Store
    PInf t1 a0 v) (@MemPop PFin) False))) (_ : (∀ (t1 : dtyp) (a0 v : (@dvalue PInf)) (t : dtyp)
    (num_elements : Nat) (align0 : (Option Nat)), (P (@Store PInf t1 a0 v) (@Alloca PFin t
    num_elements align0) False))) (_ : (∀ (t1 : dtyp) (a0 v : (@dvalue PInf)) (t0 : dtyp) (a :
    (@dvalue PFin)), (P (@Store PInf t1 a0 v) (@Load PFin t0 a) False))) (_ : (∀ (τ1 : dtyp) (a1 v1
    : (@dvalue PInf)) (τ2 : dtyp) (a2 v2 : (@dvalue PFin)), (P (@Store PInf τ1 a1 v1) (@Store PFin
    τ2 a2 v2) (And (Eq τ1 τ2) (And (I2F_dvalue a1 a2) (I2F_dvalue v1 v2)))))) (_ : (∀ (t1 : dtyp)
    (a0 v : (@dvalue PInf)) (cv : impure_conversion) (t_from : dtyp) (v1 : (@dvalue PFin)) (t_to :
    dtyp), (P (@Store PInf t1 a0 v) (@Conv PFin cv t_from v1 t_to) False))) (_ : (∀ (cv :
    impure_conversion) (t_from : dtyp) (v0 : (@dvalue PInf)) (t_to : dtyp), (P (@Conv PInf cv t_from
    v0 t_to) (@MemPush PFin) False))) (_ : (∀ (cv : impure_conversion) (t_from : dtyp) (v0 :
    (@dvalue PInf)) (t_to : dtyp), (P (@Conv PInf cv t_from v0 t_to) (@MemPop PFin) False))) (_ : (∀
    (cv : impure_conversion) (t_from : dtyp) (v0 : (@dvalue PInf)) (t_to t : dtyp) (num_elements :
    Nat) (align0 : (Option Nat)), (P (@Conv PInf cv t_from v0 t_to) (@Alloca PFin t num_elements
    align0) False))) (_ : (∀ (cv : impure_conversion) (t_from : dtyp) (v0 : (@dvalue PInf)) (t_to t0
    : dtyp) (a : (@dvalue PFin)), (P (@Conv PInf cv t_from v0 t_to) (@Load PFin t0 a) False))) (_ :
    (∀ (cv : impure_conversion) (t_from : dtyp) (v0 : (@dvalue PInf)) (t_to t1 : dtyp) (a0 v :
    (@dvalue PFin)), (P (@Conv PInf cv t_from v0 t_to) (@Store PFin t1 a0 v) False))) (_ : (∀ (cv1 :
    impure_conversion) (tf1 : dtyp) (v1 : (@dvalue PInf)) (tt1 : dtyp) (cv2 : impure_conversion)
    (tf2 : dtyp) (v2 : (@dvalue PFin)) (tt2 : dtyp), (P (@Conv PInf cv1 tf1 v1 tt1) (@Conv PFin cv2
    tf2 v2 tt2) (And (Eq cv1 cv2) (And (Eq tf1 tf2) (And (I2F_dvalue v1 v2) (Eq tt1 tt2))))))) (m :
    (@MemoryE PInf).I) (m0 : (@MemoryE PFin).I), (P m m0 (I2FE_Memory m m0))) 37 :=
  ⟨I2FE_Memory_elim⟩

theorem I2FE_Draw_equation_1 :
    (∀ (τ1 τ2 : dtyp), (Eq (I2FE_Draw (Draw τ1) (Draw τ2)) (Eq τ1 τ2))) := by intros; rfl

inductive I2FE_Draw_graph :
    (∀ (e : (@DrawE PInf).I) (f : (@DrawE PFin).I) (_ : Prop), Type) where
  | case1 :
      (∀ (τ1 τ2 : dtyp), (I2FE_Draw_graph (Draw τ1) (Draw τ2) (Eq τ1 τ2)))

abbrev I2FE_Draw_graph_equation_1 := @I2FE_Draw_graph.case1

def I2FE_Draw_graph_rect :
    (∀ (P : (∀ (e : (@DrawE PInf).I) (f : (@DrawE PFin).I) (_ : Prop), Type u)) (_ : (∀ (τ1 τ2 :
    dtyp), (P (Draw τ1) (Draw τ2) (Eq τ1 τ2)))) {d : (@DrawE PInf).I} {d0 : (@DrawE PFin).I} {P0 :
    Prop} (_ : (I2FE_Draw_graph d d0 P0)), (P d d0 P0)) := by
  intro P h1 e f p witness
  cases witness
  next => apply h1

def I2FE_Draw_graph_correct :
    (∀ (d : (@DrawE PInf).I) (d0 : (@DrawE PFin).I), (I2FE_Draw_graph d d0 (I2FE_Draw d d0))) := by
  intro e f
  cases e <;> cases f <;> first
    | apply I2FE_Draw_graph.case1

def I2FE_Draw_elim :
    (∀ (P : (∀ (e : (@DrawE PInf).I) (f : (@DrawE PFin).I) (_ : Prop), Type u)) (_ : (∀ (τ1 τ2 :
    dtyp), (P (Draw τ1) (Draw τ2) (Eq τ1 τ2)))) (d : (@DrawE PInf).I) (d0 : (@DrawE PFin).I), (P d
    d0 (I2FE_Draw d d0))) := by
  intro P h1 e f
  exact I2FE_Draw_graph_rect P h1 (I2FE_Draw_graph_correct e f)

instance FunctionalInduction_I2FE_Draw :
    (FunctionalInduction.{0, 0} I2FE_Draw) := ⟨_, I2FE_Draw_graph_correct⟩

instance FunctionalElimination_I2FE_Draw :
    FunctionalElimination I2FE_Draw (∀ (P : (∀ (e : (@DrawE PInf).I) (f : (@DrawE PFin).I) (_ : Prop), Type u)) (_ : (∀ (τ1 τ2 :
    dtyp), (P (Draw τ1) (Draw τ2) (Eq τ1 τ2)))) (d : (@DrawE PInf).I) (d0 : (@DrawE PFin).I), (P d
    d0 (I2FE_Draw d d0))) 2 :=
  ⟨I2FE_Draw_elim⟩

theorem I2FE_Exc_equation_1 :
    (∀ (exc1 : (@exc PInf)) (exc2 : (@exc PFin)), (Eq (I2FE_Exc (@LLVMExc PInf exc1) (@LLVMExc PFin
    exc2)) (I2F_dvalue exc1 exc2))) := by intros; rfl

inductive I2FE_Exc_graph :
    (∀ (e : (@LLVMExcE PInf).I) (f : (@LLVMExcE PFin).I) (_ : Prop), Type) where
  | case1 :
      (∀ (exc1 : (@exc PInf)) (exc2 : (@exc PFin)), (I2FE_Exc_graph (@LLVMExc PInf exc1) (@LLVMExc
      PFin exc2) (I2F_dvalue exc1 exc2)))

abbrev I2FE_Exc_graph_equation_1 := @I2FE_Exc_graph.case1

def I2FE_Exc_graph_rect :
    (∀ (P : (∀ (e : (@LLVMExcE PInf).I) (f : (@LLVMExcE PFin).I) (_ : Prop), Type u)) (_ : (∀ (exc1
    : (@exc PInf)) (exc2 : (@exc PFin)), (P (@LLVMExc PInf exc1) (@LLVMExc PFin exc2) (I2F_dvalue
    exc1 exc2)))) {l : (@LLVMExcE PInf).I} {l0 : (@LLVMExcE PFin).I} {P0 : Prop} (_ :
    (I2FE_Exc_graph l l0 P0)), (P l l0 P0)) := by
  intro P h1 e f p witness
  cases witness
  next => apply h1

def I2FE_Exc_graph_correct :
    (∀ (l : (@LLVMExcE PInf).I) (l0 : (@LLVMExcE PFin).I), (I2FE_Exc_graph l l0 (I2FE_Exc l l0))) := by
  intro e f
  cases e <;> cases f <;> first
    | apply I2FE_Exc_graph.case1

def I2FE_Exc_elim :
    (∀ (P : (∀ (e : (@LLVMExcE PInf).I) (f : (@LLVMExcE PFin).I) (_ : Prop), Type u)) (_ : (∀ (exc1
    : (@exc PInf)) (exc2 : (@exc PFin)), (P (@LLVMExc PInf exc1) (@LLVMExc PFin exc2) (I2F_dvalue
    exc1 exc2)))) (l : (@LLVMExcE PInf).I) (l0 : (@LLVMExcE PFin).I), (P l l0 (I2FE_Exc l l0))) := by
  intro P h1 e f
  exact I2FE_Exc_graph_rect P h1 (I2FE_Exc_graph_correct e f)

instance FunctionalInduction_I2FE_Exc :
    (FunctionalInduction.{0, 0} I2FE_Exc) := ⟨_, I2FE_Exc_graph_correct⟩

instance FunctionalElimination_I2FE_Exc :
    FunctionalElimination I2FE_Exc (∀ (P : (∀ (e : (@LLVMExcE PInf).I) (f : (@LLVMExcE PFin).I) (_ : Prop), Type u)) (_ : (∀ (exc1
    : (@exc PInf)) (exc2 : (@exc PFin)), (P (@LLVMExc PInf exc1) (@LLVMExc PFin exc2) (I2F_dvalue
    exc1 exc2)))) (l : (@LLVMExcE PInf).I) (l0 : (@LLVMExcE PFin).I), (P l l0 (I2FE_Exc l l0))) 2 :=
  ⟨I2FE_Exc_elim⟩

theorem I2FE_OOM_equation_1 :
    (∀ (u1 u2 : Unit), (Eq (I2FE_OOM (ThrowOOM u1) (ThrowOOM u2)) True)) := by intros; rfl

inductive I2FE_OOM_graph :
    (∀ (e : OOME.I) (f : OOME.I) (_ : Prop), Type) where
  | case1 :
      (∀ (u1 u2 : Unit), (I2FE_OOM_graph (ThrowOOM u1) (ThrowOOM u2) True))

abbrev I2FE_OOM_graph_equation_1 := @I2FE_OOM_graph.case1

def I2FE_OOM_graph_rect :
    (∀ (P : (∀ (e : OOME.I) (f : OOME.I) (_ : Prop), Type u)) (_ : (∀ (u1 u2 : Unit), (P (ThrowOOM
    u1) (ThrowOOM u2) True))) {o : OOME.I} {o0 : OOME.I} {P0 : Prop} (_ : (I2FE_OOM_graph o o0 P0)),
    (P o o0 P0)) := by
  intro P h1 e f p witness
  cases witness
  next => apply h1

def I2FE_OOM_graph_correct :
    (∀ (o : OOME.I) (o0 : OOME.I), (I2FE_OOM_graph o o0 (I2FE_OOM o o0))) := by
  intro e f
  cases e <;> cases f <;> first
    | apply I2FE_OOM_graph.case1

def I2FE_OOM_elim :
    (∀ (P : (∀ (e : OOME.I) (f : OOME.I) (_ : Prop), Type u)) (_ : (∀ (u1 u2 : Unit), (P (ThrowOOM
    u1) (ThrowOOM u2) True))) (o : OOME.I) (o0 : OOME.I), (P o o0 (I2FE_OOM o o0))) := by
  intro P h1 e f
  exact I2FE_OOM_graph_rect P h1 (I2FE_OOM_graph_correct e f)

instance FunctionalInduction_I2FE_OOM :
    (FunctionalInduction.{0, 0} I2FE_OOM) := ⟨_, I2FE_OOM_graph_correct⟩

instance FunctionalElimination_I2FE_OOM :
    FunctionalElimination I2FE_OOM (∀ (P : (∀ (e : OOME.I) (f : OOME.I) (_ : Prop), Type u)) (_ : (∀ (u1 u2 : Unit), (P (ThrowOOM
    u1) (ThrowOOM u2) True))) (o : OOME.I) (o0 : OOME.I), (P o o0 (I2FE_OOM o o0))) 2 :=
  ⟨I2FE_OOM_elim⟩

theorem I2FE_UB_equation_1 :
    (∀ (u1 u2 : Unit), (Eq (I2FE_UB (ThrowUB u1) (ThrowUB u2)) True)) := by intros; rfl

inductive I2FE_UB_graph :
    (∀ (e : UBE.I) (f : UBE.I) (_ : Prop), Type) where
  | case1 :
      (∀ (u1 u2 : Unit), (I2FE_UB_graph (ThrowUB u1) (ThrowUB u2) True))

abbrev I2FE_UB_graph_equation_1 := @I2FE_UB_graph.case1

def I2FE_UB_graph_rect :
    (∀ (P : (∀ (e : UBE.I) (f : UBE.I) (_ : Prop), Type u)) (_ : (∀ (u1 u2 : Unit), (P (ThrowUB u1)
    (ThrowUB u2) True))) {u : UBE.I} {u0 : UBE.I} {P0 : Prop} (_ : (I2FE_UB_graph u u0 P0)), (P u u0
    P0)) := by
  intro P h1 e f p witness
  cases witness
  next => apply h1

def I2FE_UB_graph_correct :
    (∀ (u : UBE.I) (u0 : UBE.I), (I2FE_UB_graph u u0 (I2FE_UB u u0))) := by
  intro e f
  cases e <;> cases f <;> first
    | apply I2FE_UB_graph.case1

def I2FE_UB_elim :
    (∀ (P : (∀ (e : UBE.I) (f : UBE.I) (_ : Prop), Type u)) (_ : (∀ (u1 u2 : Unit), (P (ThrowUB u1)
    (ThrowUB u2) True))) (u : UBE.I) (u0 : UBE.I), (P u u0 (I2FE_UB u u0))) := by
  intro P h1 e f
  exact I2FE_UB_graph_rect P h1 (I2FE_UB_graph_correct e f)

instance FunctionalInduction_I2FE_UB :
    (FunctionalInduction.{0, 0} I2FE_UB) := ⟨_, I2FE_UB_graph_correct⟩

instance FunctionalElimination_I2FE_UB :
    FunctionalElimination I2FE_UB (∀ (P : (∀ (e : UBE.I) (f : UBE.I) (_ : Prop), Type u)) (_ : (∀ (u1 u2 : Unit), (P (ThrowUB u1)
    (ThrowUB u2) True))) (u : UBE.I) (u0 : UBE.I), (P u u0 (I2FE_UB u u0))) 2 :=
  ⟨I2FE_UB_elim⟩

theorem I2FE_Debug_equation_1 :
    (∀ (u1 u2 : Unit), (Eq (I2FE_Debug (Debug u1) (Debug u2)) True)) := by intros; rfl

inductive I2FE_Debug_graph :
    (∀ (e : DebugE.I) (f : DebugE.I) (_ : Prop), Type) where
  | case1 :
      (∀ (u1 u2 : Unit), (I2FE_Debug_graph (Debug u1) (Debug u2) True))

abbrev I2FE_Debug_graph_equation_1 := @I2FE_Debug_graph.case1

def I2FE_Debug_graph_rect :
    (∀ (P : (∀ (e : DebugE.I) (f : DebugE.I) (_ : Prop), Type u)) (_ : (∀ (u1 u2 : Unit), (P (Debug
    u1) (Debug u2) True))) {d : DebugE.I} {d0 : DebugE.I} {P0 : Prop} (_ : (I2FE_Debug_graph d d0
    P0)), (P d d0 P0)) := by
  intro P h1 e f p witness
  cases witness
  next => apply h1

def I2FE_Debug_graph_correct :
    (∀ (d : DebugE.I) (d0 : DebugE.I), (I2FE_Debug_graph d d0 (I2FE_Debug d d0))) := by
  intro e f
  cases e <;> cases f <;> first
    | apply I2FE_Debug_graph.case1

def I2FE_Debug_elim :
    (∀ (P : (∀ (e : DebugE.I) (f : DebugE.I) (_ : Prop), Type u)) (_ : (∀ (u1 u2 : Unit), (P (Debug
    u1) (Debug u2) True))) (d : DebugE.I) (d0 : DebugE.I), (P d d0 (I2FE_Debug d d0))) := by
  intro P h1 e f
  exact I2FE_Debug_graph_rect P h1 (I2FE_Debug_graph_correct e f)

instance FunctionalInduction_I2FE_Debug :
    (FunctionalInduction.{0, 0} I2FE_Debug) := ⟨_, I2FE_Debug_graph_correct⟩

instance FunctionalElimination_I2FE_Debug :
    FunctionalElimination I2FE_Debug (∀ (P : (∀ (e : DebugE.I) (f : DebugE.I) (_ : Prop), Type u)) (_ : (∀ (u1 u2 : Unit), (P (Debug
    u1) (Debug u2) True))) (d : DebugE.I) (d0 : DebugE.I), (P d d0 (I2FE_Debug d d0))) 2 :=
  ⟨I2FE_Debug_elim⟩

theorem I2FE_Failure_equation_1 :
    (∀ (u1 u2 : Unit), (Eq (I2FE_Failure (Throw u1) (Throw u2)) True)) := by intros; rfl

inductive I2FE_Failure_graph :
    (∀ (e : FailureE.I) (f : FailureE.I) (_ : Prop), Type) where
  | case1 :
      (∀ (u1 u2 : Unit), (I2FE_Failure_graph (Throw u1) (Throw u2) True))

abbrev I2FE_Failure_graph_equation_1 := @I2FE_Failure_graph.case1

def I2FE_Failure_graph_rect :
    (∀ (P : (∀ (e : FailureE.I) (f : FailureE.I) (_ : Prop), Type u)) (_ : (∀ (u1 u2 : Unit), (P
    (Throw u1) (Throw u2) True))) {f : FailureE.I} {f0 : FailureE.I} {P0 : Prop} (_ :
    (I2FE_Failure_graph f f0 P0)), (P f f0 P0)) := by
  intro P h1 e f p witness
  cases witness
  next => apply h1

def I2FE_Failure_graph_correct :
    (∀ (f : FailureE.I) (f0 : FailureE.I), (I2FE_Failure_graph f f0 (I2FE_Failure f f0))) := by
  intro e f
  cases e <;> cases f <;> first
    | apply I2FE_Failure_graph.case1

def I2FE_Failure_elim :
    (∀ (P : (∀ (e : FailureE.I) (f : FailureE.I) (_ : Prop), Type u)) (_ : (∀ (u1 u2 : Unit), (P
    (Throw u1) (Throw u2) True))) (f : FailureE.I) (f0 : FailureE.I), (P f f0 (I2FE_Failure f f0))) := by
  intro P h1 e f
  exact I2FE_Failure_graph_rect P h1 (I2FE_Failure_graph_correct e f)

instance FunctionalInduction_I2FE_Failure :
    (FunctionalInduction.{0, 0} I2FE_Failure) := ⟨_, I2FE_Failure_graph_correct⟩

instance FunctionalElimination_I2FE_Failure :
    FunctionalElimination I2FE_Failure (∀ (P : (∀ (e : FailureE.I) (f : FailureE.I) (_ : Prop), Type u)) (_ : (∀ (u1 u2 : Unit), (P
    (Throw u1) (Throw u2) True))) (f : FailureE.I) (f0 : FailureE.I), (P f f0 (I2FE_Failure f f0))) 2 :=
  ⟨I2FE_Failure_elim⟩

theorem I2FA_Call_equation_1 :
    (∀ (τ1 : dtyp) (cc1 : cconv) (f1 : (@dvalue PInf)) (args1 : (List (Prod dtyp (@dvalue PInf))))
    (r1 : (Sum (@exc PInf) (@dvalue PInf))) (τ2 : dtyp) (cc2 : cconv) (f2 : (@dvalue PFin)) (args2 :
    (List (Prod dtyp (@dvalue PFin)))) (r2 : (Sum (@exc PFin) (@dvalue PFin))), (Eq (I2FA_Call
    (@Call PInf τ1 cc1 f1 args1) r1 (@Call PFin τ2 cc2 f2 args2) r2) (Utils.rutt_cutoff.sum_rel
    I2F_dvalue I2F_dvalue r1 r2))) := by intros; rfl

inductive I2FA_Call_graph :
    (∀ (e : (@CallE PInf).I) (_ : ((@CallE PInf).O e)) (f : (@CallE PFin).I) (_ : ((@CallE PFin).O
    f)) (_ : Prop), Type) where
  | case1 :
      (∀ (τ1 : dtyp) (cc1 : cconv) (f1 : (@dvalue PInf)) (args1 : (List (Prod dtyp (@dvalue PInf))))
      (r1 : (Sum (@exc PInf) (@dvalue PInf))) (τ2 : dtyp) (cc2 : cconv) (f2 : (@dvalue PFin)) (args2
      : (List (Prod dtyp (@dvalue PFin)))) (r2 : (Sum (@exc PFin) (@dvalue PFin))), (I2FA_Call_graph
      (@Call PInf τ1 cc1 f1 args1) r1 (@Call PFin τ2 cc2 f2 args2) r2 (Utils.rutt_cutoff.sum_rel
      I2F_dvalue I2F_dvalue r1 r2)))

abbrev I2FA_Call_graph_equation_1 := @I2FA_Call_graph.case1

def I2FA_Call_graph_rect :
    (∀ (P : (∀ (e : (@CallE PInf).I) (_ : ((@CallE PInf).O e)) (f : (@CallE PFin).I) (_ : ((@CallE
    PFin).O f)) (_ : Prop), Type u)) (_ : (∀ (τ1 : dtyp) (cc1 : cconv) (f1 : (@dvalue PInf)) (args1
    : (List (Prod dtyp (@dvalue PInf)))) (r1 : (Sum (@exc PInf) (@dvalue PInf))) (τ2 : dtyp) (cc2 :
    cconv) (f2 : (@dvalue PFin)) (args2 : (List (Prod dtyp (@dvalue PFin)))) (r2 : (Sum (@exc PFin)
    (@dvalue PFin))), (P (@Call PInf τ1 cc1 f1 args1) r1 (@Call PFin τ2 cc2 f2 args2) r2
    (Utils.rutt_cutoff.sum_rel I2F_dvalue I2F_dvalue r1 r2)))) {c : (@CallE PInf).I} {a : ((@CallE
    PInf).O c)} {c0 : (@CallE PFin).I} {b : ((@CallE PFin).O c0)} {P0 : Prop} (_ : (I2FA_Call_graph
    c a c0 b P0)), (P c a c0 b P0)) := by
  intro P h1 e a f b p witness
  cases witness
  next => apply h1

def I2FA_Call_graph_correct :
    (∀ (c : (@CallE PInf).I) (a : ((@CallE PInf).O c)) (c0 : (@CallE PFin).I) (b : ((@CallE PFin).O
    c0)), (I2FA_Call_graph c a c0 b (I2FA_Call c a c0 b))) := by
  intro e a f b
  cases e <;> cases f <;> first
    | apply I2FA_Call_graph.case1

def I2FA_Call_elim :
    (∀ (P : (∀ (e : (@CallE PInf).I) (_ : ((@CallE PInf).O e)) (f : (@CallE PFin).I) (_ : ((@CallE
    PFin).O f)) (_ : Prop), Type u)) (_ : (∀ (τ1 : dtyp) (cc1 : cconv) (f1 : (@dvalue PInf)) (args1
    : (List (Prod dtyp (@dvalue PInf)))) (r1 : (Sum (@exc PInf) (@dvalue PInf))) (τ2 : dtyp) (cc2 :
    cconv) (f2 : (@dvalue PFin)) (args2 : (List (Prod dtyp (@dvalue PFin)))) (r2 : (Sum (@exc PFin)
    (@dvalue PFin))), (P (@Call PInf τ1 cc1 f1 args1) r1 (@Call PFin τ2 cc2 f2 args2) r2
    (Utils.rutt_cutoff.sum_rel I2F_dvalue I2F_dvalue r1 r2)))) (c : (@CallE PInf).I) (a : ((@CallE
    PInf).O c)) (c0 : (@CallE PFin).I) (b : ((@CallE PFin).O c0)), (P c a c0 b (I2FA_Call c a c0
    b))) := by
  intro P h1 e a f b
  exact I2FA_Call_graph_rect P h1 (I2FA_Call_graph_correct e a f b)

instance FunctionalInduction_I2FA_Call :
    (FunctionalInduction.{0, 0} I2FA_Call) := ⟨_, I2FA_Call_graph_correct⟩

instance FunctionalElimination_I2FA_Call :
    FunctionalElimination I2FA_Call (∀ (P : (∀ (e : (@CallE PInf).I) (_ : ((@CallE PInf).O e)) (f : (@CallE PFin).I) (_ : ((@CallE
    PFin).O f)) (_ : Prop), Type u)) (_ : (∀ (τ1 : dtyp) (cc1 : cconv) (f1 : (@dvalue PInf)) (args1
    : (List (Prod dtyp (@dvalue PInf)))) (r1 : (Sum (@exc PInf) (@dvalue PInf))) (τ2 : dtyp) (cc2 :
    cconv) (f2 : (@dvalue PFin)) (args2 : (List (Prod dtyp (@dvalue PFin)))) (r2 : (Sum (@exc PFin)
    (@dvalue PFin))), (P (@Call PInf τ1 cc1 f1 args1) r1 (@Call PFin τ2 cc2 f2 args2) r2
    (Utils.rutt_cutoff.sum_rel I2F_dvalue I2F_dvalue r1 r2)))) (c : (@CallE PInf).I) (a : ((@CallE
    PInf).O c)) (c0 : (@CallE PFin).I) (b : ((@CallE PFin).O c0)), (P c a c0 b (I2FA_Call c a c0
    b))) 2 :=
  ⟨I2FA_Call_elim⟩

theorem I2FA_ExternalCall_equation_1 :
    (∀ (τ1 : dtyp) (f1 : (@dvalue PInf)) (args1 : (List (Prod dtyp (@dvalue PInf)))) (dv1 : (@dvalue
    PInf)) (τ2 : dtyp) (f2 : (@dvalue PFin)) (args2 : (List (Prod dtyp (@dvalue PFin)))) (dv2 :
    (@dvalue PFin)), (Eq (I2FA_ExternalCall (@ExternalCall PInf τ1 f1 args1) dv1 (@ExternalCall PFin
    τ2 f2 args2) dv2) (I2F_dvalue dv1 dv2))) := by intros; rfl

theorem I2FA_ExternalCall_equation_2 :
    (∀ (t : dtyp) (f : (@dvalue PInf)) (args0 : (List (Prod dtyp (@dvalue PInf)))) (a : (@dvalue
    PInf)) (str : (List VellvmIntegers.int8)) (b : Unit), (Eq (I2FA_ExternalCall (@ExternalCall PInf
    t f args0) a (@IO_stdout PFin str) b) False)) := by intros; rfl

theorem I2FA_ExternalCall_equation_3 :
    (∀ (t : dtyp) (f : (@dvalue PInf)) (args0 : (List (Prod dtyp (@dvalue PInf)))) (a : (@dvalue
    PInf)) (str0 : (List VellvmIntegers.int8)) (b : Unit), (Eq (I2FA_ExternalCall (@ExternalCall
    PInf t f args0) a (@IO_stderr PFin str0) b) False)) := by intros; rfl

theorem I2FA_ExternalCall_equation_4 :
    (∀ (str : (List VellvmIntegers.int8)) (a : Unit) (t : dtyp) (f : (@dvalue PFin)) (args0 : (List
    (Prod dtyp (@dvalue PFin)))) (b : (@dvalue PFin)), (Eq (I2FA_ExternalCall (@IO_stdout PInf str)
    a (@ExternalCall PFin t f args0) b) False)) := by intros; rfl

theorem I2FA_ExternalCall_equation_5 :
    (∀ (str1 : (List VellvmIntegers.int8)) (a : Unit) (str2 : (List VellvmIntegers.int8)) (b :
    Unit), (Eq (I2FA_ExternalCall (@IO_stdout PInf str1) a (@IO_stdout PFin str2) b) True)) := by intros; rfl

theorem I2FA_ExternalCall_equation_6 :
    (∀ (str : (List VellvmIntegers.int8)) (a : Unit) (str1 : (List VellvmIntegers.int8)) (b : Unit),
    (Eq (I2FA_ExternalCall (@IO_stdout PInf str) a (@IO_stderr PFin str1) b) False)) := by intros; rfl

theorem I2FA_ExternalCall_equation_7 :
    (∀ (str0 : (List VellvmIntegers.int8)) (a : Unit) (t : dtyp) (f : (@dvalue PFin)) (args0 : (List
    (Prod dtyp (@dvalue PFin)))) (b : (@dvalue PFin)), (Eq (I2FA_ExternalCall (@IO_stderr PInf str0)
    a (@ExternalCall PFin t f args0) b) False)) := by intros; rfl

theorem I2FA_ExternalCall_equation_8 :
    (∀ (str0 : (List VellvmIntegers.int8)) (a : Unit) (str : (List VellvmIntegers.int8)) (b : Unit),
    (Eq (I2FA_ExternalCall (@IO_stderr PInf str0) a (@IO_stdout PFin str) b) False)) := by intros; rfl

theorem I2FA_ExternalCall_equation_9 :
    (∀ (str1 : (List VellvmIntegers.int8)) (a : Unit) (str2 : (List VellvmIntegers.int8)) (b :
    Unit), (Eq (I2FA_ExternalCall (@IO_stderr PInf str1) a (@IO_stderr PFin str2) b) True)) := by intros; rfl

inductive I2FA_ExternalCall_graph :
    (∀ (e : (@ExternalCallE PInf).I) (_ : ((@ExternalCallE PInf).O e)) (f : (@ExternalCallE PFin).I)
    (_ : ((@ExternalCallE PFin).O f)) (_ : Prop), Type) where
  | case1 :
      (∀ (τ1 : dtyp) (f1 : (@dvalue PInf)) (args1 : (List (Prod dtyp (@dvalue PInf)))) (dv1 :
      (@dvalue PInf)) (τ2 : dtyp) (f2 : (@dvalue PFin)) (args2 : (List (Prod dtyp (@dvalue PFin))))
      (dv2 : (@dvalue PFin)), (I2FA_ExternalCall_graph (@ExternalCall PInf τ1 f1 args1) dv1
      (@ExternalCall PFin τ2 f2 args2) dv2 (I2F_dvalue dv1 dv2)))
  | case2 :
      (∀ (t : dtyp) (f : (@dvalue PInf)) (args0 : (List (Prod dtyp (@dvalue PInf)))) (a : (@dvalue
      PInf)) (str : (List VellvmIntegers.int8)) (b : Unit), (I2FA_ExternalCall_graph (@ExternalCall
      PInf t f args0) a (@IO_stdout PFin str) b False))
  | case3 :
      (∀ (t : dtyp) (f : (@dvalue PInf)) (args0 : (List (Prod dtyp (@dvalue PInf)))) (a : (@dvalue
      PInf)) (str0 : (List VellvmIntegers.int8)) (b : Unit), (I2FA_ExternalCall_graph (@ExternalCall
      PInf t f args0) a (@IO_stderr PFin str0) b False))
  | case4 :
      (∀ (str : (List VellvmIntegers.int8)) (a : Unit) (t : dtyp) (f : (@dvalue PFin)) (args0 :
      (List (Prod dtyp (@dvalue PFin)))) (b : (@dvalue PFin)), (I2FA_ExternalCall_graph (@IO_stdout
      PInf str) a (@ExternalCall PFin t f args0) b False))
  | case5 :
      (∀ (str1 : (List VellvmIntegers.int8)) (a : Unit) (str2 : (List VellvmIntegers.int8)) (b :
      Unit), (I2FA_ExternalCall_graph (@IO_stdout PInf str1) a (@IO_stdout PFin str2) b True))
  | case6 :
      (∀ (str : (List VellvmIntegers.int8)) (a : Unit) (str1 : (List VellvmIntegers.int8)) (b :
      Unit), (I2FA_ExternalCall_graph (@IO_stdout PInf str) a (@IO_stderr PFin str1) b False))
  | case7 :
      (∀ (str0 : (List VellvmIntegers.int8)) (a : Unit) (t : dtyp) (f : (@dvalue PFin)) (args0 :
      (List (Prod dtyp (@dvalue PFin)))) (b : (@dvalue PFin)), (I2FA_ExternalCall_graph (@IO_stderr
      PInf str0) a (@ExternalCall PFin t f args0) b False))
  | case8 :
      (∀ (str0 : (List VellvmIntegers.int8)) (a : Unit) (str : (List VellvmIntegers.int8)) (b :
      Unit), (I2FA_ExternalCall_graph (@IO_stderr PInf str0) a (@IO_stdout PFin str) b False))
  | case9 :
      (∀ (str1 : (List VellvmIntegers.int8)) (a : Unit) (str2 : (List VellvmIntegers.int8)) (b :
      Unit), (I2FA_ExternalCall_graph (@IO_stderr PInf str1) a (@IO_stderr PFin str2) b True))

abbrev I2FA_ExternalCall_graph_equation_1 := @I2FA_ExternalCall_graph.case1
abbrev I2FA_ExternalCall_graph_equation_2 := @I2FA_ExternalCall_graph.case2
abbrev I2FA_ExternalCall_graph_equation_3 := @I2FA_ExternalCall_graph.case3
abbrev I2FA_ExternalCall_graph_equation_4 := @I2FA_ExternalCall_graph.case4
abbrev I2FA_ExternalCall_graph_equation_5 := @I2FA_ExternalCall_graph.case5
abbrev I2FA_ExternalCall_graph_equation_6 := @I2FA_ExternalCall_graph.case6
abbrev I2FA_ExternalCall_graph_equation_7 := @I2FA_ExternalCall_graph.case7
abbrev I2FA_ExternalCall_graph_equation_8 := @I2FA_ExternalCall_graph.case8
abbrev I2FA_ExternalCall_graph_equation_9 := @I2FA_ExternalCall_graph.case9

def I2FA_ExternalCall_graph_rect :
    (∀ (P : (∀ (e : (@ExternalCallE PInf).I) (_ : ((@ExternalCallE PInf).O e)) (f : (@ExternalCallE
    PFin).I) (_ : ((@ExternalCallE PFin).O f)) (_ : Prop), Type u)) (_ : (∀ (τ1 : dtyp) (f1 :
    (@dvalue PInf)) (args1 : (List (Prod dtyp (@dvalue PInf)))) (dv1 : (@dvalue PInf)) (τ2 : dtyp)
    (f2 : (@dvalue PFin)) (args2 : (List (Prod dtyp (@dvalue PFin)))) (dv2 : (@dvalue PFin)), (P
    (@ExternalCall PInf τ1 f1 args1) dv1 (@ExternalCall PFin τ2 f2 args2) dv2 (I2F_dvalue dv1
    dv2)))) (_ : (∀ (t : dtyp) (f : (@dvalue PInf)) (args0 : (List (Prod dtyp (@dvalue PInf)))) (a :
    (@dvalue PInf)) (str : (List VellvmIntegers.int8)) (b : Unit), (P (@ExternalCall PInf t f args0)
    a (@IO_stdout PFin str) b False))) (_ : (∀ (t : dtyp) (f : (@dvalue PInf)) (args0 : (List (Prod
    dtyp (@dvalue PInf)))) (a : (@dvalue PInf)) (str0 : (List VellvmIntegers.int8)) (b : Unit), (P
    (@ExternalCall PInf t f args0) a (@IO_stderr PFin str0) b False))) (_ : (∀ (str : (List
    VellvmIntegers.int8)) (a : Unit) (t : dtyp) (f : (@dvalue PFin)) (args0 : (List (Prod dtyp
    (@dvalue PFin)))) (b : (@dvalue PFin)), (P (@IO_stdout PInf str) a (@ExternalCall PFin t f
    args0) b False))) (_ : (∀ (str1 : (List VellvmIntegers.int8)) (a : Unit) (str2 : (List
    VellvmIntegers.int8)) (b : Unit), (P (@IO_stdout PInf str1) a (@IO_stdout PFin str2) b True)))
    (_ : (∀ (str : (List VellvmIntegers.int8)) (a : Unit) (str1 : (List VellvmIntegers.int8)) (b :
    Unit), (P (@IO_stdout PInf str) a (@IO_stderr PFin str1) b False))) (_ : (∀ (str0 : (List
    VellvmIntegers.int8)) (a : Unit) (t : dtyp) (f : (@dvalue PFin)) (args0 : (List (Prod dtyp
    (@dvalue PFin)))) (b : (@dvalue PFin)), (P (@IO_stderr PInf str0) a (@ExternalCall PFin t f
    args0) b False))) (_ : (∀ (str0 : (List VellvmIntegers.int8)) (a : Unit) (str : (List
    VellvmIntegers.int8)) (b : Unit), (P (@IO_stderr PInf str0) a (@IO_stdout PFin str) b False)))
    (_ : (∀ (str1 : (List VellvmIntegers.int8)) (a : Unit) (str2 : (List VellvmIntegers.int8)) (b :
    Unit), (P (@IO_stderr PInf str1) a (@IO_stderr PFin str2) b True))) {e : (@ExternalCallE
    PInf).I} {a : ((@ExternalCallE PInf).O e)} {e0 : (@ExternalCallE PFin).I} {b : ((@ExternalCallE
    PFin).O e0)} {P0 : Prop} (_ : (I2FA_ExternalCall_graph e a e0 b P0)), (P e a e0 b P0)) := by
  intro P h1 h2 h3 h4 h5 h6 h7 h8 h9 e a f b p witness
  cases witness
  next => apply h1
  next => apply h2
  next => apply h3
  next => apply h4
  next => apply h5
  next => apply h6
  next => apply h7
  next => apply h8
  next => apply h9

def I2FA_ExternalCall_graph_correct :
    (∀ (e : (@ExternalCallE PInf).I) (a : ((@ExternalCallE PInf).O e)) (e0 : (@ExternalCallE
    PFin).I) (b : ((@ExternalCallE PFin).O e0)), (I2FA_ExternalCall_graph e a e0 b
    (I2FA_ExternalCall e a e0 b))) := by
  intro e a f b
  cases e <;> cases f <;> first
    | apply I2FA_ExternalCall_graph.case1
    | apply I2FA_ExternalCall_graph.case2
    | apply I2FA_ExternalCall_graph.case3
    | apply I2FA_ExternalCall_graph.case4
    | apply I2FA_ExternalCall_graph.case5
    | apply I2FA_ExternalCall_graph.case6
    | apply I2FA_ExternalCall_graph.case7
    | apply I2FA_ExternalCall_graph.case8
    | apply I2FA_ExternalCall_graph.case9

def I2FA_ExternalCall_elim :
    (∀ (P : (∀ (e : (@ExternalCallE PInf).I) (_ : ((@ExternalCallE PInf).O e)) (f : (@ExternalCallE
    PFin).I) (_ : ((@ExternalCallE PFin).O f)) (_ : Prop), Type u)) (_ : (∀ (τ1 : dtyp) (f1 :
    (@dvalue PInf)) (args1 : (List (Prod dtyp (@dvalue PInf)))) (dv1 : (@dvalue PInf)) (τ2 : dtyp)
    (f2 : (@dvalue PFin)) (args2 : (List (Prod dtyp (@dvalue PFin)))) (dv2 : (@dvalue PFin)), (P
    (@ExternalCall PInf τ1 f1 args1) dv1 (@ExternalCall PFin τ2 f2 args2) dv2 (I2F_dvalue dv1
    dv2)))) (_ : (∀ (t : dtyp) (f : (@dvalue PInf)) (args0 : (List (Prod dtyp (@dvalue PInf)))) (a :
    (@dvalue PInf)) (str : (List VellvmIntegers.int8)) (b : Unit), (P (@ExternalCall PInf t f args0)
    a (@IO_stdout PFin str) b False))) (_ : (∀ (t : dtyp) (f : (@dvalue PInf)) (args0 : (List (Prod
    dtyp (@dvalue PInf)))) (a : (@dvalue PInf)) (str0 : (List VellvmIntegers.int8)) (b : Unit), (P
    (@ExternalCall PInf t f args0) a (@IO_stderr PFin str0) b False))) (_ : (∀ (str : (List
    VellvmIntegers.int8)) (a : Unit) (t : dtyp) (f : (@dvalue PFin)) (args0 : (List (Prod dtyp
    (@dvalue PFin)))) (b : (@dvalue PFin)), (P (@IO_stdout PInf str) a (@ExternalCall PFin t f
    args0) b False))) (_ : (∀ (str1 : (List VellvmIntegers.int8)) (a : Unit) (str2 : (List
    VellvmIntegers.int8)) (b : Unit), (P (@IO_stdout PInf str1) a (@IO_stdout PFin str2) b True)))
    (_ : (∀ (str : (List VellvmIntegers.int8)) (a : Unit) (str1 : (List VellvmIntegers.int8)) (b :
    Unit), (P (@IO_stdout PInf str) a (@IO_stderr PFin str1) b False))) (_ : (∀ (str0 : (List
    VellvmIntegers.int8)) (a : Unit) (t : dtyp) (f : (@dvalue PFin)) (args0 : (List (Prod dtyp
    (@dvalue PFin)))) (b : (@dvalue PFin)), (P (@IO_stderr PInf str0) a (@ExternalCall PFin t f
    args0) b False))) (_ : (∀ (str0 : (List VellvmIntegers.int8)) (a : Unit) (str : (List
    VellvmIntegers.int8)) (b : Unit), (P (@IO_stderr PInf str0) a (@IO_stdout PFin str) b False)))
    (_ : (∀ (str1 : (List VellvmIntegers.int8)) (a : Unit) (str2 : (List VellvmIntegers.int8)) (b :
    Unit), (P (@IO_stderr PInf str1) a (@IO_stderr PFin str2) b True))) (e : (@ExternalCallE
    PInf).I) (a : ((@ExternalCallE PInf).O e)) (e0 : (@ExternalCallE PFin).I) (b : ((@ExternalCallE
    PFin).O e0)), (P e a e0 b (I2FA_ExternalCall e a e0 b))) := by
  intro P h1 h2 h3 h4 h5 h6 h7 h8 h9 e a f b
  exact I2FA_ExternalCall_graph_rect P h1 h2 h3 h4 h5 h6 h7 h8 h9 (I2FA_ExternalCall_graph_correct e a f
    b)

instance FunctionalInduction_I2FA_ExternalCall :
    (FunctionalInduction.{0, 0} I2FA_ExternalCall) := ⟨_, I2FA_ExternalCall_graph_correct⟩

instance FunctionalElimination_I2FA_ExternalCall :
    FunctionalElimination I2FA_ExternalCall (∀ (P : (∀ (e : (@ExternalCallE PInf).I) (_ : ((@ExternalCallE PInf).O e)) (f : (@ExternalCallE
    PFin).I) (_ : ((@ExternalCallE PFin).O f)) (_ : Prop), Type u)) (_ : (∀ (τ1 : dtyp) (f1 :
    (@dvalue PInf)) (args1 : (List (Prod dtyp (@dvalue PInf)))) (dv1 : (@dvalue PInf)) (τ2 : dtyp)
    (f2 : (@dvalue PFin)) (args2 : (List (Prod dtyp (@dvalue PFin)))) (dv2 : (@dvalue PFin)), (P
    (@ExternalCall PInf τ1 f1 args1) dv1 (@ExternalCall PFin τ2 f2 args2) dv2 (I2F_dvalue dv1
    dv2)))) (_ : (∀ (t : dtyp) (f : (@dvalue PInf)) (args0 : (List (Prod dtyp (@dvalue PInf)))) (a :
    (@dvalue PInf)) (str : (List VellvmIntegers.int8)) (b : Unit), (P (@ExternalCall PInf t f args0)
    a (@IO_stdout PFin str) b False))) (_ : (∀ (t : dtyp) (f : (@dvalue PInf)) (args0 : (List (Prod
    dtyp (@dvalue PInf)))) (a : (@dvalue PInf)) (str0 : (List VellvmIntegers.int8)) (b : Unit), (P
    (@ExternalCall PInf t f args0) a (@IO_stderr PFin str0) b False))) (_ : (∀ (str : (List
    VellvmIntegers.int8)) (a : Unit) (t : dtyp) (f : (@dvalue PFin)) (args0 : (List (Prod dtyp
    (@dvalue PFin)))) (b : (@dvalue PFin)), (P (@IO_stdout PInf str) a (@ExternalCall PFin t f
    args0) b False))) (_ : (∀ (str1 : (List VellvmIntegers.int8)) (a : Unit) (str2 : (List
    VellvmIntegers.int8)) (b : Unit), (P (@IO_stdout PInf str1) a (@IO_stdout PFin str2) b True)))
    (_ : (∀ (str : (List VellvmIntegers.int8)) (a : Unit) (str1 : (List VellvmIntegers.int8)) (b :
    Unit), (P (@IO_stdout PInf str) a (@IO_stderr PFin str1) b False))) (_ : (∀ (str0 : (List
    VellvmIntegers.int8)) (a : Unit) (t : dtyp) (f : (@dvalue PFin)) (args0 : (List (Prod dtyp
    (@dvalue PFin)))) (b : (@dvalue PFin)), (P (@IO_stderr PInf str0) a (@ExternalCall PFin t f
    args0) b False))) (_ : (∀ (str0 : (List VellvmIntegers.int8)) (a : Unit) (str : (List
    VellvmIntegers.int8)) (b : Unit), (P (@IO_stderr PInf str0) a (@IO_stdout PFin str) b False)))
    (_ : (∀ (str1 : (List VellvmIntegers.int8)) (a : Unit) (str2 : (List VellvmIntegers.int8)) (b :
    Unit), (P (@IO_stderr PInf str1) a (@IO_stderr PFin str2) b True))) (e : (@ExternalCallE
    PInf).I) (a : ((@ExternalCallE PInf).O e)) (e0 : (@ExternalCallE PFin).I) (b : ((@ExternalCallE
    PFin).O e0)), (P e a e0 b (I2FA_ExternalCall e a e0 b))) 10 :=
  ⟨I2FA_ExternalCall_elim⟩

theorem I2FA_Intrinsic_equation_1 :
    (∀ (τ1 : dtyp) (f1 : IRString) (args1 : (List (Prod dtyp (@dvalue PInf)))) (va1 : (Option
    PInf.PTR.ptr)) (r1 : (Sum (@exc PInf) (@dvalue PInf))) (τ2 : dtyp) (f2 : IRString) (args2 :
    (List (Prod dtyp (@dvalue PFin)))) (va2 : (Option PFin.PTR.ptr)) (r2 : (Sum (@exc PFin) (@dvalue
    PFin))), (Eq (I2FA_Intrinsic (@Intrinsic PInf τ1 f1 args1 va1) r1 (@Intrinsic PFin τ2 f2 args2
    va2) r2) (Utils.rutt_cutoff.sum_rel I2F_dvalue I2F_dvalue r1 r2))) := by intros; rfl

inductive I2FA_Intrinsic_graph :
    (∀ (e : (@IntrinsicE PInf).I) (_ : ((@IntrinsicE PInf).O e)) (f : (@IntrinsicE PFin).I) (_ :
    ((@IntrinsicE PFin).O f)) (_ : Prop), Type) where
  | case1 :
      (∀ (τ1 : dtyp) (f1 : IRString) (args1 : (List (Prod dtyp (@dvalue PInf)))) (va1 : (Option
      PInf.PTR.ptr)) (r1 : (Sum (@exc PInf) (@dvalue PInf))) (τ2 : dtyp) (f2 : IRString) (args2 :
      (List (Prod dtyp (@dvalue PFin)))) (va2 : (Option PFin.PTR.ptr)) (r2 : (Sum (@exc PFin)
      (@dvalue PFin))), (I2FA_Intrinsic_graph (@Intrinsic PInf τ1 f1 args1 va1) r1 (@Intrinsic PFin
      τ2 f2 args2 va2) r2 (Utils.rutt_cutoff.sum_rel I2F_dvalue I2F_dvalue r1 r2)))

abbrev I2FA_Intrinsic_graph_equation_1 := @I2FA_Intrinsic_graph.case1

def I2FA_Intrinsic_graph_rect :
    (∀ (P : (∀ (e : (@IntrinsicE PInf).I) (_ : ((@IntrinsicE PInf).O e)) (f : (@IntrinsicE PFin).I)
    (_ : ((@IntrinsicE PFin).O f)) (_ : Prop), Type u)) (_ : (∀ (τ1 : dtyp) (f1 : IRString) (args1 :
    (List (Prod dtyp (@dvalue PInf)))) (va1 : (Option PInf.PTR.ptr)) (r1 : (Sum (@exc PInf) (@dvalue
    PInf))) (τ2 : dtyp) (f2 : IRString) (args2 : (List (Prod dtyp (@dvalue PFin)))) (va2 : (Option
    PFin.PTR.ptr)) (r2 : (Sum (@exc PFin) (@dvalue PFin))), (P (@Intrinsic PInf τ1 f1 args1 va1) r1
    (@Intrinsic PFin τ2 f2 args2 va2) r2 (Utils.rutt_cutoff.sum_rel I2F_dvalue I2F_dvalue r1 r2))))
    {i : (@IntrinsicE PInf).I} {a : ((@IntrinsicE PInf).O i)} {i0 : (@IntrinsicE PFin).I} {b :
    ((@IntrinsicE PFin).O i0)} {P0 : Prop} (_ : (I2FA_Intrinsic_graph i a i0 b P0)), (P i a i0 b
    P0)) := by
  intro P h1 e a f b p witness
  cases witness
  next => apply h1

def I2FA_Intrinsic_graph_correct :
    (∀ (i : (@IntrinsicE PInf).I) (a : ((@IntrinsicE PInf).O i)) (i0 : (@IntrinsicE PFin).I) (b :
    ((@IntrinsicE PFin).O i0)), (I2FA_Intrinsic_graph i a i0 b (I2FA_Intrinsic i a i0 b))) := by
  intro e a f b
  cases e <;> cases f <;> first
    | apply I2FA_Intrinsic_graph.case1

def I2FA_Intrinsic_elim :
    (∀ (P : (∀ (e : (@IntrinsicE PInf).I) (_ : ((@IntrinsicE PInf).O e)) (f : (@IntrinsicE PFin).I)
    (_ : ((@IntrinsicE PFin).O f)) (_ : Prop), Type u)) (_ : (∀ (τ1 : dtyp) (f1 : IRString) (args1 :
    (List (Prod dtyp (@dvalue PInf)))) (va1 : (Option PInf.PTR.ptr)) (r1 : (Sum (@exc PInf) (@dvalue
    PInf))) (τ2 : dtyp) (f2 : IRString) (args2 : (List (Prod dtyp (@dvalue PFin)))) (va2 : (Option
    PFin.PTR.ptr)) (r2 : (Sum (@exc PFin) (@dvalue PFin))), (P (@Intrinsic PInf τ1 f1 args1 va1) r1
    (@Intrinsic PFin τ2 f2 args2 va2) r2 (Utils.rutt_cutoff.sum_rel I2F_dvalue I2F_dvalue r1 r2))))
    (i : (@IntrinsicE PInf).I) (a : ((@IntrinsicE PInf).O i)) (i0 : (@IntrinsicE PFin).I) (b :
    ((@IntrinsicE PFin).O i0)), (P i a i0 b (I2FA_Intrinsic i a i0 b))) := by
  intro P h1 e a f b
  exact I2FA_Intrinsic_graph_rect P h1 (I2FA_Intrinsic_graph_correct e a f b)

instance FunctionalInduction_I2FA_Intrinsic :
    (FunctionalInduction.{0, 0} I2FA_Intrinsic) := ⟨_, I2FA_Intrinsic_graph_correct⟩

instance FunctionalElimination_I2FA_Intrinsic :
    FunctionalElimination I2FA_Intrinsic (∀ (P : (∀ (e : (@IntrinsicE PInf).I) (_ : ((@IntrinsicE PInf).O e)) (f : (@IntrinsicE PFin).I)
    (_ : ((@IntrinsicE PFin).O f)) (_ : Prop), Type u)) (_ : (∀ (τ1 : dtyp) (f1 : IRString) (args1 :
    (List (Prod dtyp (@dvalue PInf)))) (va1 : (Option PInf.PTR.ptr)) (r1 : (Sum (@exc PInf) (@dvalue
    PInf))) (τ2 : dtyp) (f2 : IRString) (args2 : (List (Prod dtyp (@dvalue PFin)))) (va2 : (Option
    PFin.PTR.ptr)) (r2 : (Sum (@exc PFin) (@dvalue PFin))), (P (@Intrinsic PInf τ1 f1 args1 va1) r1
    (@Intrinsic PFin τ2 f2 args2 va2) r2 (Utils.rutt_cutoff.sum_rel I2F_dvalue I2F_dvalue r1 r2))))
    (i : (@IntrinsicE PInf).I) (a : ((@IntrinsicE PInf).O i)) (i0 : (@IntrinsicE PFin).I) (b :
    ((@IntrinsicE PFin).O i0)), (P i a i0 b (I2FA_Intrinsic i a i0 b))) 2 :=
  ⟨I2FA_Intrinsic_elim⟩

theorem I2FA_Global_equation_1 :
    (∀ (x1 : raw_id) (dv1 : (@dvalue PInf)) (a : Unit) (x2 : raw_id) (dv2 : (@dvalue PFin)) (b :
    Unit), (Eq (I2FA_Global (@GlobalWrite PInf x1 dv1) a (@GlobalWrite PFin x2 dv2) b) True)) := by intros; rfl

theorem I2FA_Global_equation_2 :
    (∀ (id0 : raw_id) (dv : (@dvalue PInf)) (a : Unit) (id2 : raw_id) (b : (@dvalue PFin)), (Eq
    (I2FA_Global (@GlobalWrite PInf id0 dv) a (@GlobalRead PFin id2) b) False)) := by intros; rfl

theorem I2FA_Global_equation_3 :
    (∀ (id1 : raw_id) (a : (@dvalue PInf)) (id0 : raw_id) (dv : (@dvalue PFin)) (b : Unit), (Eq
    (I2FA_Global (@GlobalRead PInf id1) a (@GlobalWrite PFin id0 dv) b) False)) := by intros; rfl

theorem I2FA_Global_equation_4 :
    (∀ (x1 : raw_id) (dv1 : (@dvalue PInf)) (x2 : raw_id) (dv2 : (@dvalue PFin)), (Eq (I2FA_Global
    (@GlobalRead PInf x1) dv1 (@GlobalRead PFin x2) dv2) (I2F_dvalue dv1 dv2))) := by intros; rfl

inductive I2FA_Global_graph :
    (∀ (e : (@GlobalE PInf).I) (_ : ((@GlobalE PInf).O e)) (f : (@GlobalE PFin).I) (_ : ((@GlobalE
    PFin).O f)) (_ : Prop), Type) where
  | case1 :
      (∀ (x1 : raw_id) (dv1 : (@dvalue PInf)) (a : Unit) (x2 : raw_id) (dv2 : (@dvalue PFin)) (b :
      Unit), (I2FA_Global_graph (@GlobalWrite PInf x1 dv1) a (@GlobalWrite PFin x2 dv2) b True))
  | case2 :
      (∀ (id0 : raw_id) (dv : (@dvalue PInf)) (a : Unit) (id2 : raw_id) (b : (@dvalue PFin)),
      (I2FA_Global_graph (@GlobalWrite PInf id0 dv) a (@GlobalRead PFin id2) b False))
  | case3 :
      (∀ (id1 : raw_id) (a : (@dvalue PInf)) (id0 : raw_id) (dv : (@dvalue PFin)) (b : Unit),
      (I2FA_Global_graph (@GlobalRead PInf id1) a (@GlobalWrite PFin id0 dv) b False))
  | case4 :
      (∀ (x1 : raw_id) (dv1 : (@dvalue PInf)) (x2 : raw_id) (dv2 : (@dvalue PFin)),
      (I2FA_Global_graph (@GlobalRead PInf x1) dv1 (@GlobalRead PFin x2) dv2 (I2F_dvalue dv1 dv2)))

abbrev I2FA_Global_graph_equation_1 := @I2FA_Global_graph.case1
abbrev I2FA_Global_graph_equation_2 := @I2FA_Global_graph.case2
abbrev I2FA_Global_graph_equation_3 := @I2FA_Global_graph.case3
abbrev I2FA_Global_graph_equation_4 := @I2FA_Global_graph.case4

def I2FA_Global_graph_rect :
    (∀ (P : (∀ (e : (@GlobalE PInf).I) (_ : ((@GlobalE PInf).O e)) (f : (@GlobalE PFin).I) (_ :
    ((@GlobalE PFin).O f)) (_ : Prop), Type u)) (_ : (∀ (x1 : raw_id) (dv1 : (@dvalue PInf)) (a :
    Unit) (x2 : raw_id) (dv2 : (@dvalue PFin)) (b : Unit), (P (@GlobalWrite PInf x1 dv1) a
    (@GlobalWrite PFin x2 dv2) b True))) (_ : (∀ (id0 : raw_id) (dv : (@dvalue PInf)) (a : Unit)
    (id2 : raw_id) (b : (@dvalue PFin)), (P (@GlobalWrite PInf id0 dv) a (@GlobalRead PFin id2) b
    False))) (_ : (∀ (id1 : raw_id) (a : (@dvalue PInf)) (id0 : raw_id) (dv : (@dvalue PFin)) (b :
    Unit), (P (@GlobalRead PInf id1) a (@GlobalWrite PFin id0 dv) b False))) (_ : (∀ (x1 : raw_id)
    (dv1 : (@dvalue PInf)) (x2 : raw_id) (dv2 : (@dvalue PFin)), (P (@GlobalRead PInf x1) dv1
    (@GlobalRead PFin x2) dv2 (I2F_dvalue dv1 dv2)))) {g : (@GlobalE PInf).I} {a : ((@GlobalE
    PInf).O g)} {g0 : (@GlobalE PFin).I} {b : ((@GlobalE PFin).O g0)} {P0 : Prop} (_ :
    (I2FA_Global_graph g a g0 b P0)), (P g a g0 b P0)) := by
  intro P h1 h2 h3 h4 e a f b p witness
  cases witness
  next => apply h1
  next => apply h2
  next => apply h3
  next => apply h4

def I2FA_Global_graph_correct :
    (∀ (g : (@GlobalE PInf).I) (a : ((@GlobalE PInf).O g)) (g0 : (@GlobalE PFin).I) (b : ((@GlobalE
    PFin).O g0)), (I2FA_Global_graph g a g0 b (I2FA_Global g a g0 b))) := by
  intro e a f b
  cases e <;> cases f <;> first
    | apply I2FA_Global_graph.case1
    | apply I2FA_Global_graph.case2
    | apply I2FA_Global_graph.case3
    | apply I2FA_Global_graph.case4

def I2FA_Global_elim :
    (∀ (P : (∀ (e : (@GlobalE PInf).I) (_ : ((@GlobalE PInf).O e)) (f : (@GlobalE PFin).I) (_ :
    ((@GlobalE PFin).O f)) (_ : Prop), Type u)) (_ : (∀ (x1 : raw_id) (dv1 : (@dvalue PInf)) (a :
    Unit) (x2 : raw_id) (dv2 : (@dvalue PFin)) (b : Unit), (P (@GlobalWrite PInf x1 dv1) a
    (@GlobalWrite PFin x2 dv2) b True))) (_ : (∀ (id0 : raw_id) (dv : (@dvalue PInf)) (a : Unit)
    (id2 : raw_id) (b : (@dvalue PFin)), (P (@GlobalWrite PInf id0 dv) a (@GlobalRead PFin id2) b
    False))) (_ : (∀ (id1 : raw_id) (a : (@dvalue PInf)) (id0 : raw_id) (dv : (@dvalue PFin)) (b :
    Unit), (P (@GlobalRead PInf id1) a (@GlobalWrite PFin id0 dv) b False))) (_ : (∀ (x1 : raw_id)
    (dv1 : (@dvalue PInf)) (x2 : raw_id) (dv2 : (@dvalue PFin)), (P (@GlobalRead PInf x1) dv1
    (@GlobalRead PFin x2) dv2 (I2F_dvalue dv1 dv2)))) (g : (@GlobalE PInf).I) (a : ((@GlobalE
    PInf).O g)) (g0 : (@GlobalE PFin).I) (b : ((@GlobalE PFin).O g0)), (P g a g0 b (I2FA_Global g a
    g0 b))) := by
  intro P h1 h2 h3 h4 e a f b
  exact I2FA_Global_graph_rect P h1 h2 h3 h4 (I2FA_Global_graph_correct e a f b)

instance FunctionalInduction_I2FA_Global :
    (FunctionalInduction.{0, 0} I2FA_Global) := ⟨_, I2FA_Global_graph_correct⟩

instance FunctionalElimination_I2FA_Global :
    FunctionalElimination I2FA_Global (∀ (P : (∀ (e : (@GlobalE PInf).I) (_ : ((@GlobalE PInf).O e)) (f : (@GlobalE PFin).I) (_ :
    ((@GlobalE PFin).O f)) (_ : Prop), Type u)) (_ : (∀ (x1 : raw_id) (dv1 : (@dvalue PInf)) (a :
    Unit) (x2 : raw_id) (dv2 : (@dvalue PFin)) (b : Unit), (P (@GlobalWrite PInf x1 dv1) a
    (@GlobalWrite PFin x2 dv2) b True))) (_ : (∀ (id0 : raw_id) (dv : (@dvalue PInf)) (a : Unit)
    (id2 : raw_id) (b : (@dvalue PFin)), (P (@GlobalWrite PInf id0 dv) a (@GlobalRead PFin id2) b
    False))) (_ : (∀ (id1 : raw_id) (a : (@dvalue PInf)) (id0 : raw_id) (dv : (@dvalue PFin)) (b :
    Unit), (P (@GlobalRead PInf id1) a (@GlobalWrite PFin id0 dv) b False))) (_ : (∀ (x1 : raw_id)
    (dv1 : (@dvalue PInf)) (x2 : raw_id) (dv2 : (@dvalue PFin)), (P (@GlobalRead PInf x1) dv1
    (@GlobalRead PFin x2) dv2 (I2F_dvalue dv1 dv2)))) (g : (@GlobalE PInf).I) (a : ((@GlobalE
    PInf).O g)) (g0 : (@GlobalE PFin).I) (b : ((@GlobalE PFin).O g0)), (P g a g0 b (I2FA_Global g a
    g0 b))) 5 :=
  ⟨I2FA_Global_elim⟩

theorem I2FA_Local_equation_1 :
    (∀ (x1 : raw_id) (dv1 : (@dvalue PInf)) (a : Unit) (x2 : raw_id) (dv2 : (@dvalue PFin)) (b :
    Unit), (Eq (I2FA_Local (@LocalWrite PInf x1 dv1) a (@LocalWrite PFin x2 dv2) b) True)) := by intros; rfl

theorem I2FA_Local_equation_2 :
    (∀ (id0 : raw_id) (dv : (@dvalue PInf)) (a : Unit) (id2 : raw_id) (b : (@dvalue PFin)), (Eq
    (I2FA_Local (@LocalWrite PInf id0 dv) a (@LocalRead PFin id2) b) False)) := by intros; rfl

theorem I2FA_Local_equation_3 :
    (∀ (id1 : raw_id) (a : (@dvalue PInf)) (id0 : raw_id) (dv : (@dvalue PFin)) (b : Unit), (Eq
    (I2FA_Local (@LocalRead PInf id1) a (@LocalWrite PFin id0 dv) b) False)) := by intros; rfl

theorem I2FA_Local_equation_4 :
    (∀ (x1 : raw_id) (dv1 : (@dvalue PInf)) (x2 : raw_id) (dv2 : (@dvalue PFin)), (Eq (I2FA_Local
    (@LocalRead PInf x1) dv1 (@LocalRead PFin x2) dv2) (I2F_dvalue dv1 dv2))) := by intros; rfl

inductive I2FA_Local_graph :
    (∀ (e : (@LocalE PInf).I) (_ : ((@LocalE PInf).O e)) (f : (@LocalE PFin).I) (_ : ((@LocalE
    PFin).O f)) (_ : Prop), Type) where
  | case1 :
      (∀ (x1 : raw_id) (dv1 : (@dvalue PInf)) (a : Unit) (x2 : raw_id) (dv2 : (@dvalue PFin)) (b :
      Unit), (I2FA_Local_graph (@LocalWrite PInf x1 dv1) a (@LocalWrite PFin x2 dv2) b True))
  | case2 :
      (∀ (id0 : raw_id) (dv : (@dvalue PInf)) (a : Unit) (id2 : raw_id) (b : (@dvalue PFin)),
      (I2FA_Local_graph (@LocalWrite PInf id0 dv) a (@LocalRead PFin id2) b False))
  | case3 :
      (∀ (id1 : raw_id) (a : (@dvalue PInf)) (id0 : raw_id) (dv : (@dvalue PFin)) (b : Unit),
      (I2FA_Local_graph (@LocalRead PInf id1) a (@LocalWrite PFin id0 dv) b False))
  | case4 :
      (∀ (x1 : raw_id) (dv1 : (@dvalue PInf)) (x2 : raw_id) (dv2 : (@dvalue PFin)),
      (I2FA_Local_graph (@LocalRead PInf x1) dv1 (@LocalRead PFin x2) dv2 (I2F_dvalue dv1 dv2)))

abbrev I2FA_Local_graph_equation_1 := @I2FA_Local_graph.case1
abbrev I2FA_Local_graph_equation_2 := @I2FA_Local_graph.case2
abbrev I2FA_Local_graph_equation_3 := @I2FA_Local_graph.case3
abbrev I2FA_Local_graph_equation_4 := @I2FA_Local_graph.case4

def I2FA_Local_graph_rect :
    (∀ (P : (∀ (e : (@LocalE PInf).I) (_ : ((@LocalE PInf).O e)) (f : (@LocalE PFin).I) (_ :
    ((@LocalE PFin).O f)) (_ : Prop), Type u)) (_ : (∀ (x1 : raw_id) (dv1 : (@dvalue PInf)) (a :
    Unit) (x2 : raw_id) (dv2 : (@dvalue PFin)) (b : Unit), (P (@LocalWrite PInf x1 dv1) a
    (@LocalWrite PFin x2 dv2) b True))) (_ : (∀ (id0 : raw_id) (dv : (@dvalue PInf)) (a : Unit) (id2
    : raw_id) (b : (@dvalue PFin)), (P (@LocalWrite PInf id0 dv) a (@LocalRead PFin id2) b False)))
    (_ : (∀ (id1 : raw_id) (a : (@dvalue PInf)) (id0 : raw_id) (dv : (@dvalue PFin)) (b : Unit), (P
    (@LocalRead PInf id1) a (@LocalWrite PFin id0 dv) b False))) (_ : (∀ (x1 : raw_id) (dv1 :
    (@dvalue PInf)) (x2 : raw_id) (dv2 : (@dvalue PFin)), (P (@LocalRead PInf x1) dv1 (@LocalRead
    PFin x2) dv2 (I2F_dvalue dv1 dv2)))) {l : (@LocalE PInf).I} {a : ((@LocalE PInf).O l)} {l0 :
    (@LocalE PFin).I} {b : ((@LocalE PFin).O l0)} {P0 : Prop} (_ : (I2FA_Local_graph l a l0 b P0)),
    (P l a l0 b P0)) := by
  intro P h1 h2 h3 h4 e a f b p witness
  cases witness
  next => apply h1
  next => apply h2
  next => apply h3
  next => apply h4

def I2FA_Local_graph_correct :
    (∀ (l : (@LocalE PInf).I) (a : ((@LocalE PInf).O l)) (l0 : (@LocalE PFin).I) (b : ((@LocalE
    PFin).O l0)), (I2FA_Local_graph l a l0 b (I2FA_Local l a l0 b))) := by
  intro e a f b
  cases e <;> cases f <;> first
    | apply I2FA_Local_graph.case1
    | apply I2FA_Local_graph.case2
    | apply I2FA_Local_graph.case3
    | apply I2FA_Local_graph.case4

def I2FA_Local_elim :
    (∀ (P : (∀ (e : (@LocalE PInf).I) (_ : ((@LocalE PInf).O e)) (f : (@LocalE PFin).I) (_ :
    ((@LocalE PFin).O f)) (_ : Prop), Type u)) (_ : (∀ (x1 : raw_id) (dv1 : (@dvalue PInf)) (a :
    Unit) (x2 : raw_id) (dv2 : (@dvalue PFin)) (b : Unit), (P (@LocalWrite PInf x1 dv1) a
    (@LocalWrite PFin x2 dv2) b True))) (_ : (∀ (id0 : raw_id) (dv : (@dvalue PInf)) (a : Unit) (id2
    : raw_id) (b : (@dvalue PFin)), (P (@LocalWrite PInf id0 dv) a (@LocalRead PFin id2) b False)))
    (_ : (∀ (id1 : raw_id) (a : (@dvalue PInf)) (id0 : raw_id) (dv : (@dvalue PFin)) (b : Unit), (P
    (@LocalRead PInf id1) a (@LocalWrite PFin id0 dv) b False))) (_ : (∀ (x1 : raw_id) (dv1 :
    (@dvalue PInf)) (x2 : raw_id) (dv2 : (@dvalue PFin)), (P (@LocalRead PInf x1) dv1 (@LocalRead
    PFin x2) dv2 (I2F_dvalue dv1 dv2)))) (l : (@LocalE PInf).I) (a : ((@LocalE PInf).O l)) (l0 :
    (@LocalE PFin).I) (b : ((@LocalE PFin).O l0)), (P l a l0 b (I2FA_Local l a l0 b))) := by
  intro P h1 h2 h3 h4 e a f b
  exact I2FA_Local_graph_rect P h1 h2 h3 h4 (I2FA_Local_graph_correct e a f b)

instance FunctionalInduction_I2FA_Local :
    (FunctionalInduction.{0, 0} I2FA_Local) := ⟨_, I2FA_Local_graph_correct⟩

instance FunctionalElimination_I2FA_Local :
    FunctionalElimination I2FA_Local (∀ (P : (∀ (e : (@LocalE PInf).I) (_ : ((@LocalE PInf).O e)) (f : (@LocalE PFin).I) (_ :
    ((@LocalE PFin).O f)) (_ : Prop), Type u)) (_ : (∀ (x1 : raw_id) (dv1 : (@dvalue PInf)) (a :
    Unit) (x2 : raw_id) (dv2 : (@dvalue PFin)) (b : Unit), (P (@LocalWrite PInf x1 dv1) a
    (@LocalWrite PFin x2 dv2) b True))) (_ : (∀ (id0 : raw_id) (dv : (@dvalue PInf)) (a : Unit) (id2
    : raw_id) (b : (@dvalue PFin)), (P (@LocalWrite PInf id0 dv) a (@LocalRead PFin id2) b False)))
    (_ : (∀ (id1 : raw_id) (a : (@dvalue PInf)) (id0 : raw_id) (dv : (@dvalue PFin)) (b : Unit), (P
    (@LocalRead PInf id1) a (@LocalWrite PFin id0 dv) b False))) (_ : (∀ (x1 : raw_id) (dv1 :
    (@dvalue PInf)) (x2 : raw_id) (dv2 : (@dvalue PFin)), (P (@LocalRead PInf x1) dv1 (@LocalRead
    PFin x2) dv2 (I2F_dvalue dv1 dv2)))) (l : (@LocalE PInf).I) (a : ((@LocalE PInf).O l)) (l0 :
    (@LocalE PFin).I) (b : ((@LocalE PFin).O l0)), (P l a l0 b (I2FA_Local l a l0 b))) 5 :=
  ⟨I2FA_Local_elim⟩

theorem I2FA_Stack_equation_1 :
    (∀ (args1 : (List (Prod raw_id (@dvalue PInf)))) (a : Unit) (args2 : (List (Prod raw_id (@dvalue
    PFin)))) (b : Unit), (Eq (I2FA_Stack (@StackPush PInf args1) a (@StackPush PFin args2) b) True)) := by intros; rfl

theorem I2FA_Stack_equation_2 :
    (∀ (args0 : (List (Prod raw_id (@dvalue PInf)))) (a b : Unit), (Eq (I2FA_Stack (@StackPush PInf
    args0) a (@StackPop PFin) b) False)) := by intros; rfl

theorem I2FA_Stack_equation_3 :
    (∀ (args0 : (List (Prod raw_id (@dvalue PInf)))) (a : Unit) (e : (@exc PFin)) (b : Unit), (Eq
    (I2FA_Stack (@StackPush PInf args0) a (@StackRaise PFin e) b) False)) := by intros; rfl

theorem I2FA_Stack_equation_4 :
    (∀ (args0 : (List (Prod raw_id (@dvalue PInf)))) (a : Unit) (b : (Option (@exc PFin))), (Eq
    (I2FA_Stack (@StackPush PInf args0) a (@StackGetExc PFin) b) False)) := by intros; rfl

theorem I2FA_Stack_equation_5 :
    (∀ (a : Unit) (args0 : (List (Prod raw_id (@dvalue PFin)))) (b : Unit), (Eq (I2FA_Stack
    (@StackPop PInf) a (@StackPush PFin args0) b) False)) := by intros; rfl

theorem I2FA_Stack_equation_6 :
    (∀ (a b : Unit), (Eq (I2FA_Stack (@StackPop PInf) a (@StackPop PFin) b) True)) := by intros; rfl

theorem I2FA_Stack_equation_7 :
    (∀ (a : Unit) (e : (@exc PFin)) (b : Unit), (Eq (I2FA_Stack (@StackPop PInf) a (@StackRaise PFin
    e) b) False)) := by intros; rfl

theorem I2FA_Stack_equation_8 :
    (∀ (a : Unit) (b : (Option (@exc PFin))), (Eq (I2FA_Stack (@StackPop PInf) a (@StackGetExc PFin)
    b) False)) := by intros; rfl

theorem I2FA_Stack_equation_9 :
    (∀ (e : (@exc PInf)) (a : Unit) (args0 : (List (Prod raw_id (@dvalue PFin)))) (b : Unit), (Eq
    (I2FA_Stack (@StackRaise PInf e) a (@StackPush PFin args0) b) False)) := by intros; rfl

theorem I2FA_Stack_equation_10 :
    (∀ (e : (@exc PInf)) (a b : Unit), (Eq (I2FA_Stack (@StackRaise PInf e) a (@StackPop PFin) b)
    False)) := by intros; rfl

theorem I2FA_Stack_equation_11 :
    (∀ (exc1 : (@exc PInf)) (a : Unit) (exc2 : (@exc PFin)) (b : Unit), (Eq (I2FA_Stack (@StackRaise
    PInf exc1) a (@StackRaise PFin exc2) b) True)) := by intros; rfl

theorem I2FA_Stack_equation_12 :
    (∀ (e : (@exc PInf)) (a : Unit) (b : (Option (@exc PFin))), (Eq (I2FA_Stack (@StackRaise PInf e)
    a (@StackGetExc PFin) b) False)) := by intros; rfl

theorem I2FA_Stack_equation_13 :
    (∀ (a : (Option (@exc PInf))) (args0 : (List (Prod raw_id (@dvalue PFin)))) (b : Unit), (Eq
    (I2FA_Stack (@StackGetExc PInf) a (@StackPush PFin args0) b) False)) := by intros; rfl

theorem I2FA_Stack_equation_14 :
    (∀ (a : (Option (@exc PInf))) (b : Unit), (Eq (I2FA_Stack (@StackGetExc PInf) a (@StackPop PFin)
    b) False)) := by intros; rfl

theorem I2FA_Stack_equation_15 :
    (∀ (a : (Option (@exc PInf))) (e : (@exc PFin)) (b : Unit), (Eq (I2FA_Stack (@StackGetExc PInf)
    a (@StackRaise PFin e) b) False)) := by intros; rfl

theorem I2FA_Stack_equation_16 :
    (∀ (oe1 : (Option (@exc PInf))) (oe2 : (Option (@exc PFin))), (Eq (I2FA_Stack (@StackGetExc
    PInf) oe1 (@StackGetExc PFin) oe2) (Numeric.Rocqlib.option_rel I2F_dvalue oe1 oe2))) := by intros; rfl

inductive I2FA_Stack_graph :
    (∀ (e : (@StackE PInf).I) (_ : ((@StackE PInf).O e)) (f : (@StackE PFin).I) (_ : ((@StackE
    PFin).O f)) (_ : Prop), Type) where
  | case1 :
      (∀ (args1 : (List (Prod raw_id (@dvalue PInf)))) (a : Unit) (args2 : (List (Prod raw_id
      (@dvalue PFin)))) (b : Unit), (I2FA_Stack_graph (@StackPush PInf args1) a (@StackPush PFin
      args2) b True))
  | case2 :
      (∀ (args0 : (List (Prod raw_id (@dvalue PInf)))) (a b : Unit), (I2FA_Stack_graph (@StackPush
      PInf args0) a (@StackPop PFin) b False))
  | case3 :
      (∀ (args0 : (List (Prod raw_id (@dvalue PInf)))) (a : Unit) (e : (@exc PFin)) (b : Unit),
      (I2FA_Stack_graph (@StackPush PInf args0) a (@StackRaise PFin e) b False))
  | case4 :
      (∀ (args0 : (List (Prod raw_id (@dvalue PInf)))) (a : Unit) (b : (Option (@exc PFin))),
      (I2FA_Stack_graph (@StackPush PInf args0) a (@StackGetExc PFin) b False))
  | case5 :
      (∀ (a : Unit) (args0 : (List (Prod raw_id (@dvalue PFin)))) (b : Unit), (I2FA_Stack_graph
      (@StackPop PInf) a (@StackPush PFin args0) b False))
  | case6 :
      (∀ (a b : Unit), (I2FA_Stack_graph (@StackPop PInf) a (@StackPop PFin) b True))
  | case7 :
      (∀ (a : Unit) (e : (@exc PFin)) (b : Unit), (I2FA_Stack_graph (@StackPop PInf) a (@StackRaise
      PFin e) b False))
  | case8 :
      (∀ (a : Unit) (b : (Option (@exc PFin))), (I2FA_Stack_graph (@StackPop PInf) a (@StackGetExc
      PFin) b False))
  | case9 :
      (∀ (e : (@exc PInf)) (a : Unit) (args0 : (List (Prod raw_id (@dvalue PFin)))) (b : Unit),
      (I2FA_Stack_graph (@StackRaise PInf e) a (@StackPush PFin args0) b False))
  | case10 :
      (∀ (e : (@exc PInf)) (a b : Unit), (I2FA_Stack_graph (@StackRaise PInf e) a (@StackPop PFin) b
      False))
  | case11 :
      (∀ (exc1 : (@exc PInf)) (a : Unit) (exc2 : (@exc PFin)) (b : Unit), (I2FA_Stack_graph
      (@StackRaise PInf exc1) a (@StackRaise PFin exc2) b True))
  | case12 :
      (∀ (e : (@exc PInf)) (a : Unit) (b : (Option (@exc PFin))), (I2FA_Stack_graph (@StackRaise
      PInf e) a (@StackGetExc PFin) b False))
  | case13 :
      (∀ (a : (Option (@exc PInf))) (args0 : (List (Prod raw_id (@dvalue PFin)))) (b : Unit),
      (I2FA_Stack_graph (@StackGetExc PInf) a (@StackPush PFin args0) b False))
  | case14 :
      (∀ (a : (Option (@exc PInf))) (b : Unit), (I2FA_Stack_graph (@StackGetExc PInf) a (@StackPop
      PFin) b False))
  | case15 :
      (∀ (a : (Option (@exc PInf))) (e : (@exc PFin)) (b : Unit), (I2FA_Stack_graph (@StackGetExc
      PInf) a (@StackRaise PFin e) b False))
  | case16 :
      (∀ (oe1 : (Option (@exc PInf))) (oe2 : (Option (@exc PFin))), (I2FA_Stack_graph (@StackGetExc
      PInf) oe1 (@StackGetExc PFin) oe2 (Numeric.Rocqlib.option_rel I2F_dvalue oe1 oe2)))

abbrev I2FA_Stack_graph_equation_1 := @I2FA_Stack_graph.case1
abbrev I2FA_Stack_graph_equation_2 := @I2FA_Stack_graph.case2
abbrev I2FA_Stack_graph_equation_3 := @I2FA_Stack_graph.case3
abbrev I2FA_Stack_graph_equation_4 := @I2FA_Stack_graph.case4
abbrev I2FA_Stack_graph_equation_5 := @I2FA_Stack_graph.case5
abbrev I2FA_Stack_graph_equation_6 := @I2FA_Stack_graph.case6
abbrev I2FA_Stack_graph_equation_7 := @I2FA_Stack_graph.case7
abbrev I2FA_Stack_graph_equation_8 := @I2FA_Stack_graph.case8
abbrev I2FA_Stack_graph_equation_9 := @I2FA_Stack_graph.case9
abbrev I2FA_Stack_graph_equation_10 := @I2FA_Stack_graph.case10
abbrev I2FA_Stack_graph_equation_11 := @I2FA_Stack_graph.case11
abbrev I2FA_Stack_graph_equation_12 := @I2FA_Stack_graph.case12
abbrev I2FA_Stack_graph_equation_13 := @I2FA_Stack_graph.case13
abbrev I2FA_Stack_graph_equation_14 := @I2FA_Stack_graph.case14
abbrev I2FA_Stack_graph_equation_15 := @I2FA_Stack_graph.case15
abbrev I2FA_Stack_graph_equation_16 := @I2FA_Stack_graph.case16

def I2FA_Stack_graph_rect :
    (∀ (P : (∀ (e : (@StackE PInf).I) (_ : ((@StackE PInf).O e)) (f : (@StackE PFin).I) (_ :
    ((@StackE PFin).O f)) (_ : Prop), Type u)) (_ : (∀ (args1 : (List (Prod raw_id (@dvalue PInf))))
    (a : Unit) (args2 : (List (Prod raw_id (@dvalue PFin)))) (b : Unit), (P (@StackPush PInf args1)
    a (@StackPush PFin args2) b True))) (_ : (∀ (args0 : (List (Prod raw_id (@dvalue PInf)))) (a b :
    Unit), (P (@StackPush PInf args0) a (@StackPop PFin) b False))) (_ : (∀ (args0 : (List (Prod
    raw_id (@dvalue PInf)))) (a : Unit) (e : (@exc PFin)) (b : Unit), (P (@StackPush PInf args0) a
    (@StackRaise PFin e) b False))) (_ : (∀ (args0 : (List (Prod raw_id (@dvalue PInf)))) (a : Unit)
    (b : (Option (@exc PFin))), (P (@StackPush PInf args0) a (@StackGetExc PFin) b False))) (_ : (∀
    (a : Unit) (args0 : (List (Prod raw_id (@dvalue PFin)))) (b : Unit), (P (@StackPop PInf) a
    (@StackPush PFin args0) b False))) (_ : (∀ (a b : Unit), (P (@StackPop PInf) a (@StackPop PFin)
    b True))) (_ : (∀ (a : Unit) (e : (@exc PFin)) (b : Unit), (P (@StackPop PInf) a (@StackRaise
    PFin e) b False))) (_ : (∀ (a : Unit) (b : (Option (@exc PFin))), (P (@StackPop PInf) a
    (@StackGetExc PFin) b False))) (_ : (∀ (e : (@exc PInf)) (a : Unit) (args0 : (List (Prod raw_id
    (@dvalue PFin)))) (b : Unit), (P (@StackRaise PInf e) a (@StackPush PFin args0) b False))) (_ :
    (∀ (e : (@exc PInf)) (a b : Unit), (P (@StackRaise PInf e) a (@StackPop PFin) b False))) (_ : (∀
    (exc1 : (@exc PInf)) (a : Unit) (exc2 : (@exc PFin)) (b : Unit), (P (@StackRaise PInf exc1) a
    (@StackRaise PFin exc2) b True))) (_ : (∀ (e : (@exc PInf)) (a : Unit) (b : (Option (@exc
    PFin))), (P (@StackRaise PInf e) a (@StackGetExc PFin) b False))) (_ : (∀ (a : (Option (@exc
    PInf))) (args0 : (List (Prod raw_id (@dvalue PFin)))) (b : Unit), (P (@StackGetExc PInf) a
    (@StackPush PFin args0) b False))) (_ : (∀ (a : (Option (@exc PInf))) (b : Unit), (P
    (@StackGetExc PInf) a (@StackPop PFin) b False))) (_ : (∀ (a : (Option (@exc PInf))) (e : (@exc
    PFin)) (b : Unit), (P (@StackGetExc PInf) a (@StackRaise PFin e) b False))) (_ : (∀ (oe1 :
    (Option (@exc PInf))) (oe2 : (Option (@exc PFin))), (P (@StackGetExc PInf) oe1 (@StackGetExc
    PFin) oe2 (Numeric.Rocqlib.option_rel I2F_dvalue oe1 oe2)))) {s : (@StackE PInf).I} {a :
    ((@StackE PInf).O s)} {s0 : (@StackE PFin).I} {b : ((@StackE PFin).O s0)} {P0 : Prop} (_ :
    (I2FA_Stack_graph s a s0 b P0)), (P s a s0 b P0)) := by
  intro P h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15 h16 e a f b p witness
  cases witness
  next => apply h1
  next => apply h2
  next => apply h3
  next => apply h4
  next => apply h5
  next => apply h6
  next => apply h7
  next => apply h8
  next => apply h9
  next => apply h10
  next => apply h11
  next => apply h12
  next => apply h13
  next => apply h14
  next => apply h15
  next => apply h16

def I2FA_Stack_graph_correct :
    (∀ (s : (@StackE PInf).I) (a : ((@StackE PInf).O s)) (s0 : (@StackE PFin).I) (b : ((@StackE
    PFin).O s0)), (I2FA_Stack_graph s a s0 b (I2FA_Stack s a s0 b))) := by
  intro e a f b
  cases e <;> cases f <;> first
    | apply I2FA_Stack_graph.case1
    | apply I2FA_Stack_graph.case2
    | apply I2FA_Stack_graph.case3
    | apply I2FA_Stack_graph.case4
    | apply I2FA_Stack_graph.case5
    | apply I2FA_Stack_graph.case6
    | apply I2FA_Stack_graph.case7
    | apply I2FA_Stack_graph.case8
    | apply I2FA_Stack_graph.case9
    | apply I2FA_Stack_graph.case10
    | apply I2FA_Stack_graph.case11
    | apply I2FA_Stack_graph.case12
    | apply I2FA_Stack_graph.case13
    | apply I2FA_Stack_graph.case14
    | apply I2FA_Stack_graph.case15
    | apply I2FA_Stack_graph.case16

def I2FA_Stack_elim :
    (∀ (P : (∀ (e : (@StackE PInf).I) (_ : ((@StackE PInf).O e)) (f : (@StackE PFin).I) (_ :
    ((@StackE PFin).O f)) (_ : Prop), Type u)) (_ : (∀ (args1 : (List (Prod raw_id (@dvalue PInf))))
    (a : Unit) (args2 : (List (Prod raw_id (@dvalue PFin)))) (b : Unit), (P (@StackPush PInf args1)
    a (@StackPush PFin args2) b True))) (_ : (∀ (args0 : (List (Prod raw_id (@dvalue PInf)))) (a b :
    Unit), (P (@StackPush PInf args0) a (@StackPop PFin) b False))) (_ : (∀ (args0 : (List (Prod
    raw_id (@dvalue PInf)))) (a : Unit) (e : (@exc PFin)) (b : Unit), (P (@StackPush PInf args0) a
    (@StackRaise PFin e) b False))) (_ : (∀ (args0 : (List (Prod raw_id (@dvalue PInf)))) (a : Unit)
    (b : (Option (@exc PFin))), (P (@StackPush PInf args0) a (@StackGetExc PFin) b False))) (_ : (∀
    (a : Unit) (args0 : (List (Prod raw_id (@dvalue PFin)))) (b : Unit), (P (@StackPop PInf) a
    (@StackPush PFin args0) b False))) (_ : (∀ (a b : Unit), (P (@StackPop PInf) a (@StackPop PFin)
    b True))) (_ : (∀ (a : Unit) (e : (@exc PFin)) (b : Unit), (P (@StackPop PInf) a (@StackRaise
    PFin e) b False))) (_ : (∀ (a : Unit) (b : (Option (@exc PFin))), (P (@StackPop PInf) a
    (@StackGetExc PFin) b False))) (_ : (∀ (e : (@exc PInf)) (a : Unit) (args0 : (List (Prod raw_id
    (@dvalue PFin)))) (b : Unit), (P (@StackRaise PInf e) a (@StackPush PFin args0) b False))) (_ :
    (∀ (e : (@exc PInf)) (a b : Unit), (P (@StackRaise PInf e) a (@StackPop PFin) b False))) (_ : (∀
    (exc1 : (@exc PInf)) (a : Unit) (exc2 : (@exc PFin)) (b : Unit), (P (@StackRaise PInf exc1) a
    (@StackRaise PFin exc2) b True))) (_ : (∀ (e : (@exc PInf)) (a : Unit) (b : (Option (@exc
    PFin))), (P (@StackRaise PInf e) a (@StackGetExc PFin) b False))) (_ : (∀ (a : (Option (@exc
    PInf))) (args0 : (List (Prod raw_id (@dvalue PFin)))) (b : Unit), (P (@StackGetExc PInf) a
    (@StackPush PFin args0) b False))) (_ : (∀ (a : (Option (@exc PInf))) (b : Unit), (P
    (@StackGetExc PInf) a (@StackPop PFin) b False))) (_ : (∀ (a : (Option (@exc PInf))) (e : (@exc
    PFin)) (b : Unit), (P (@StackGetExc PInf) a (@StackRaise PFin e) b False))) (_ : (∀ (oe1 :
    (Option (@exc PInf))) (oe2 : (Option (@exc PFin))), (P (@StackGetExc PInf) oe1 (@StackGetExc
    PFin) oe2 (Numeric.Rocqlib.option_rel I2F_dvalue oe1 oe2)))) (s : (@StackE PInf).I) (a :
    ((@StackE PInf).O s)) (s0 : (@StackE PFin).I) (b : ((@StackE PFin).O s0)), (P s a s0 b
    (I2FA_Stack s a s0 b))) := by
  intro P h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15 h16 e a f b
  exact I2FA_Stack_graph_rect P h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15 h16
    (I2FA_Stack_graph_correct e a f b)

instance FunctionalInduction_I2FA_Stack :
    (FunctionalInduction.{0, 0} I2FA_Stack) := ⟨_, I2FA_Stack_graph_correct⟩

instance FunctionalElimination_I2FA_Stack :
    FunctionalElimination I2FA_Stack (∀ (P : (∀ (e : (@StackE PInf).I) (_ : ((@StackE PInf).O e)) (f : (@StackE PFin).I) (_ :
    ((@StackE PFin).O f)) (_ : Prop), Type u)) (_ : (∀ (args1 : (List (Prod raw_id (@dvalue PInf))))
    (a : Unit) (args2 : (List (Prod raw_id (@dvalue PFin)))) (b : Unit), (P (@StackPush PInf args1)
    a (@StackPush PFin args2) b True))) (_ : (∀ (args0 : (List (Prod raw_id (@dvalue PInf)))) (a b :
    Unit), (P (@StackPush PInf args0) a (@StackPop PFin) b False))) (_ : (∀ (args0 : (List (Prod
    raw_id (@dvalue PInf)))) (a : Unit) (e : (@exc PFin)) (b : Unit), (P (@StackPush PInf args0) a
    (@StackRaise PFin e) b False))) (_ : (∀ (args0 : (List (Prod raw_id (@dvalue PInf)))) (a : Unit)
    (b : (Option (@exc PFin))), (P (@StackPush PInf args0) a (@StackGetExc PFin) b False))) (_ : (∀
    (a : Unit) (args0 : (List (Prod raw_id (@dvalue PFin)))) (b : Unit), (P (@StackPop PInf) a
    (@StackPush PFin args0) b False))) (_ : (∀ (a b : Unit), (P (@StackPop PInf) a (@StackPop PFin)
    b True))) (_ : (∀ (a : Unit) (e : (@exc PFin)) (b : Unit), (P (@StackPop PInf) a (@StackRaise
    PFin e) b False))) (_ : (∀ (a : Unit) (b : (Option (@exc PFin))), (P (@StackPop PInf) a
    (@StackGetExc PFin) b False))) (_ : (∀ (e : (@exc PInf)) (a : Unit) (args0 : (List (Prod raw_id
    (@dvalue PFin)))) (b : Unit), (P (@StackRaise PInf e) a (@StackPush PFin args0) b False))) (_ :
    (∀ (e : (@exc PInf)) (a b : Unit), (P (@StackRaise PInf e) a (@StackPop PFin) b False))) (_ : (∀
    (exc1 : (@exc PInf)) (a : Unit) (exc2 : (@exc PFin)) (b : Unit), (P (@StackRaise PInf exc1) a
    (@StackRaise PFin exc2) b True))) (_ : (∀ (e : (@exc PInf)) (a : Unit) (b : (Option (@exc
    PFin))), (P (@StackRaise PInf e) a (@StackGetExc PFin) b False))) (_ : (∀ (a : (Option (@exc
    PInf))) (args0 : (List (Prod raw_id (@dvalue PFin)))) (b : Unit), (P (@StackGetExc PInf) a
    (@StackPush PFin args0) b False))) (_ : (∀ (a : (Option (@exc PInf))) (b : Unit), (P
    (@StackGetExc PInf) a (@StackPop PFin) b False))) (_ : (∀ (a : (Option (@exc PInf))) (e : (@exc
    PFin)) (b : Unit), (P (@StackGetExc PInf) a (@StackRaise PFin e) b False))) (_ : (∀ (oe1 :
    (Option (@exc PInf))) (oe2 : (Option (@exc PFin))), (P (@StackGetExc PInf) oe1 (@StackGetExc
    PFin) oe2 (Numeric.Rocqlib.option_rel I2F_dvalue oe1 oe2)))) (s : (@StackE PInf).I) (a :
    ((@StackE PInf).O s)) (s0 : (@StackE PFin).I) (b : ((@StackE PFin).O s0)), (P s a s0 b
    (I2FA_Stack s a s0 b))) 17 :=
  ⟨I2FA_Stack_elim⟩

theorem I2FA_Memory_equation_1 :
    (∀ (a b : Unit), (Eq (I2FA_Memory (@MemPush PInf) a (@MemPush PFin) b) True)) := by intros; rfl

theorem I2FA_Memory_equation_2 :
    (∀ (a b : Unit), (Eq (I2FA_Memory (@MemPush PInf) a (@MemPop PFin) b) False)) := by intros; rfl

theorem I2FA_Memory_equation_3 :
    (∀ (a : Unit) (t : dtyp) (num_elements : Nat) (align0 : (Option Nat)) (b : (@dvalue PFin)), (Eq
    (I2FA_Memory (@MemPush PInf) a (@Alloca PFin t num_elements align0) b) False)) := by intros; rfl

theorem I2FA_Memory_equation_4 :
    (∀ (a : Unit) (t0 : dtyp) (a0 b : (@dvalue PFin)), (Eq (I2FA_Memory (@MemPush PInf) a (@Load
    PFin t0 a0) b) False)) := by intros; rfl

theorem I2FA_Memory_equation_5 :
    (∀ (a : Unit) (t1 : dtyp) (a1 v : (@dvalue PFin)) (b : Unit), (Eq (I2FA_Memory (@MemPush PInf) a
    (@Store PFin t1 a1 v) b) False)) := by intros; rfl

theorem I2FA_Memory_equation_6 :
    (∀ (a : Unit) (cv : impure_conversion) (t_from : dtyp) (v0 : (@dvalue PFin)) (t_to : dtyp) (b :
    (@dvalue PFin)), (Eq (I2FA_Memory (@MemPush PInf) a (@Conv PFin cv t_from v0 t_to) b) False)) := by intros; rfl

theorem I2FA_Memory_equation_7 :
    (∀ (a b : Unit), (Eq (I2FA_Memory (@MemPop PInf) a (@MemPush PFin) b) False)) := by intros; rfl

theorem I2FA_Memory_equation_8 :
    (∀ (a b : Unit), (Eq (I2FA_Memory (@MemPop PInf) a (@MemPop PFin) b) True)) := by intros; rfl

theorem I2FA_Memory_equation_9 :
    (∀ (a : Unit) (t : dtyp) (num_elements : Nat) (align0 : (Option Nat)) (b : (@dvalue PFin)), (Eq
    (I2FA_Memory (@MemPop PInf) a (@Alloca PFin t num_elements align0) b) False)) := by intros; rfl

theorem I2FA_Memory_equation_10 :
    (∀ (a : Unit) (t0 : dtyp) (a0 b : (@dvalue PFin)), (Eq (I2FA_Memory (@MemPop PInf) a (@Load PFin
    t0 a0) b) False)) := by intros; rfl

theorem I2FA_Memory_equation_11 :
    (∀ (a : Unit) (t1 : dtyp) (a1 v : (@dvalue PFin)) (b : Unit), (Eq (I2FA_Memory (@MemPop PInf) a
    (@Store PFin t1 a1 v) b) False)) := by intros; rfl

theorem I2FA_Memory_equation_12 :
    (∀ (a : Unit) (cv : impure_conversion) (t_from : dtyp) (v0 : (@dvalue PFin)) (t_to : dtyp) (b :
    (@dvalue PFin)), (Eq (I2FA_Memory (@MemPop PInf) a (@Conv PFin cv t_from v0 t_to) b) False)) := by intros; rfl

theorem I2FA_Memory_equation_13 :
    (∀ (t : dtyp) (num_elements : Nat) (align0 : (Option Nat)) (a : (@dvalue PInf)) (b : Unit), (Eq
    (I2FA_Memory (@Alloca PInf t num_elements align0) a (@MemPush PFin) b) False)) := by intros; rfl

theorem I2FA_Memory_equation_14 :
    (∀ (t : dtyp) (num_elements : Nat) (align0 : (Option Nat)) (a : (@dvalue PInf)) (b : Unit), (Eq
    (I2FA_Memory (@Alloca PInf t num_elements align0) a (@MemPop PFin) b) False)) := by intros; rfl

theorem I2FA_Memory_equation_15 :
    (∀ (τ1 : dtyp) (n1 : Nat) (align1 : (Option Nat)) (dv1 : (@dvalue PInf)) (τ2 : dtyp) (n2 : Nat)
    (align2 : (Option Nat)) (dv2 : (@dvalue PFin)), (Eq (I2FA_Memory (@Alloca PInf τ1 n1 align1) dv1
    (@Alloca PFin τ2 n2 align2) dv2) (I2F_dvalue dv1 dv2))) := by intros; rfl

theorem I2FA_Memory_equation_16 :
    (∀ (t : dtyp) (num_elements : Nat) (align0 : (Option Nat)) (a : (@dvalue PInf)) (t1 : dtyp) (a0
    b : (@dvalue PFin)), (Eq (I2FA_Memory (@Alloca PInf t num_elements align0) a (@Load PFin t1 a0)
    b) False)) := by intros; rfl

theorem I2FA_Memory_equation_17 :
    (∀ (t : dtyp) (num_elements : Nat) (align0 : (Option Nat)) (a : (@dvalue PInf)) (t2 : dtyp) (a1
    v : (@dvalue PFin)) (b : Unit), (Eq (I2FA_Memory (@Alloca PInf t num_elements align0) a (@Store
    PFin t2 a1 v) b) False)) := by intros; rfl

theorem I2FA_Memory_equation_18 :
    (∀ (t : dtyp) (num_elements : Nat) (align0 : (Option Nat)) (a : (@dvalue PInf)) (cv :
    impure_conversion) (t_from : dtyp) (v0 : (@dvalue PFin)) (t_to : dtyp) (b : (@dvalue PFin)), (Eq
    (I2FA_Memory (@Alloca PInf t num_elements align0) a (@Conv PFin cv t_from v0 t_to) b) False)) := by intros; rfl

theorem I2FA_Memory_equation_19 :
    (∀ (t0 : dtyp) (a0 a : (@dvalue PInf)) (b : Unit), (Eq (I2FA_Memory (@Load PInf t0 a0) a
    (@MemPush PFin) b) False)) := by intros; rfl

theorem I2FA_Memory_equation_20 :
    (∀ (t0 : dtyp) (a0 a : (@dvalue PInf)) (b : Unit), (Eq (I2FA_Memory (@Load PInf t0 a0) a
    (@MemPop PFin) b) False)) := by intros; rfl

theorem I2FA_Memory_equation_21 :
    (∀ (t0 : dtyp) (a0 a : (@dvalue PInf)) (t : dtyp) (num_elements : Nat) (align0 : (Option Nat))
    (b : (@dvalue PFin)), (Eq (I2FA_Memory (@Load PInf t0 a0) a (@Alloca PFin t num_elements align0)
    b) False)) := by intros; rfl

theorem I2FA_Memory_equation_22 :
    (∀ (τ1 : dtyp) (a1 dv1 : (@dvalue PInf)) (τ2 : dtyp) (a2 dv2 : (@dvalue PFin)), (Eq (I2FA_Memory
    (@Load PInf τ1 a1) dv1 (@Load PFin τ2 a2) dv2) (I2F_dvalue dv1 dv2))) := by intros; rfl

theorem I2FA_Memory_equation_23 :
    (∀ (t0 : dtyp) (a0 a : (@dvalue PInf)) (t2 : dtyp) (a2 v : (@dvalue PFin)) (b : Unit), (Eq
    (I2FA_Memory (@Load PInf t0 a0) a (@Store PFin t2 a2 v) b) False)) := by intros; rfl

theorem I2FA_Memory_equation_24 :
    (∀ (t0 : dtyp) (a0 a : (@dvalue PInf)) (cv : impure_conversion) (t_from : dtyp) (v0 : (@dvalue
    PFin)) (t_to : dtyp) (b : (@dvalue PFin)), (Eq (I2FA_Memory (@Load PInf t0 a0) a (@Conv PFin cv
    t_from v0 t_to) b) False)) := by intros; rfl

theorem I2FA_Memory_equation_25 :
    (∀ (t1 : dtyp) (a1 v : (@dvalue PInf)) (a b : Unit), (Eq (I2FA_Memory (@Store PInf t1 a1 v) a
    (@MemPush PFin) b) False)) := by intros; rfl

theorem I2FA_Memory_equation_26 :
    (∀ (t1 : dtyp) (a1 v : (@dvalue PInf)) (a b : Unit), (Eq (I2FA_Memory (@Store PInf t1 a1 v) a
    (@MemPop PFin) b) False)) := by intros; rfl

theorem I2FA_Memory_equation_27 :
    (∀ (t1 : dtyp) (a1 v : (@dvalue PInf)) (a : Unit) (t : dtyp) (num_elements : Nat) (align0 :
    (Option Nat)) (b : (@dvalue PFin)), (Eq (I2FA_Memory (@Store PInf t1 a1 v) a (@Alloca PFin t
    num_elements align0) b) False)) := by intros; rfl

theorem I2FA_Memory_equation_28 :
    (∀ (t1 : dtyp) (a1 v : (@dvalue PInf)) (a : Unit) (t0 : dtyp) (a0 b : (@dvalue PFin)), (Eq
    (I2FA_Memory (@Store PInf t1 a1 v) a (@Load PFin t0 a0) b) False)) := by intros; rfl

theorem I2FA_Memory_equation_29 :
    (∀ (τ1 : dtyp) (a1 v1 : (@dvalue PInf)) (a : Unit) (τ2 : dtyp) (a2 v2 : (@dvalue PFin)) (b :
    Unit), (Eq (I2FA_Memory (@Store PInf τ1 a1 v1) a (@Store PFin τ2 a2 v2) b) True)) := by intros; rfl

theorem I2FA_Memory_equation_30 :
    (∀ (t1 : dtyp) (a1 v : (@dvalue PInf)) (a : Unit) (cv : impure_conversion) (t_from : dtyp) (v1 :
    (@dvalue PFin)) (t_to : dtyp) (b : (@dvalue PFin)), (Eq (I2FA_Memory (@Store PInf t1 a1 v) a
    (@Conv PFin cv t_from v1 t_to) b) False)) := by intros; rfl

theorem I2FA_Memory_equation_31 :
    (∀ (cv : impure_conversion) (t_from : dtyp) (v0 : (@dvalue PInf)) (t_to : dtyp) (a : (@dvalue
    PInf)) (b : Unit), (Eq (I2FA_Memory (@Conv PInf cv t_from v0 t_to) a (@MemPush PFin) b) False)) := by intros; rfl

theorem I2FA_Memory_equation_32 :
    (∀ (cv : impure_conversion) (t_from : dtyp) (v0 : (@dvalue PInf)) (t_to : dtyp) (a : (@dvalue
    PInf)) (b : Unit), (Eq (I2FA_Memory (@Conv PInf cv t_from v0 t_to) a (@MemPop PFin) b) False)) := by intros; rfl

theorem I2FA_Memory_equation_33 :
    (∀ (cv : impure_conversion) (t_from : dtyp) (v0 : (@dvalue PInf)) (t_to : dtyp) (a : (@dvalue
    PInf)) (t : dtyp) (num_elements : Nat) (align0 : (Option Nat)) (b : (@dvalue PFin)), (Eq
    (I2FA_Memory (@Conv PInf cv t_from v0 t_to) a (@Alloca PFin t num_elements align0) b) False)) := by intros; rfl

theorem I2FA_Memory_equation_34 :
    (∀ (cv : impure_conversion) (t_from : dtyp) (v0 : (@dvalue PInf)) (t_to : dtyp) (a : (@dvalue
    PInf)) (t0 : dtyp) (a0 b : (@dvalue PFin)), (Eq (I2FA_Memory (@Conv PInf cv t_from v0 t_to) a
    (@Load PFin t0 a0) b) False)) := by intros; rfl

theorem I2FA_Memory_equation_35 :
    (∀ (cv : impure_conversion) (t_from : dtyp) (v0 : (@dvalue PInf)) (t_to : dtyp) (a : (@dvalue
    PInf)) (t1 : dtyp) (a1 v : (@dvalue PFin)) (b : Unit), (Eq (I2FA_Memory (@Conv PInf cv t_from v0
    t_to) a (@Store PFin t1 a1 v) b) False)) := by intros; rfl

theorem I2FA_Memory_equation_36 :
    (∀ (cv1 : impure_conversion) (tf1 : dtyp) (v1 : (@dvalue PInf)) (tt1 : dtyp) (dv1 : (@dvalue
    PInf)) (cv2 : impure_conversion) (tf2 : dtyp) (v2 : (@dvalue PFin)) (tt2 : dtyp) (dv2 : (@dvalue
    PFin)), (Eq (I2FA_Memory (@Conv PInf cv1 tf1 v1 tt1) dv1 (@Conv PFin cv2 tf2 v2 tt2) dv2)
    (I2F_dvalue dv1 dv2))) := by intros; rfl

inductive I2FA_Memory_graph :
    (∀ (e : (@MemoryE PInf).I) (_ : ((@MemoryE PInf).O e)) (f : (@MemoryE PFin).I) (_ : ((@MemoryE
    PFin).O f)) (_ : Prop), Type) where
  | case1 :
      (∀ (a b : Unit), (I2FA_Memory_graph (@MemPush PInf) a (@MemPush PFin) b True))
  | case2 :
      (∀ (a b : Unit), (I2FA_Memory_graph (@MemPush PInf) a (@MemPop PFin) b False))
  | case3 :
      (∀ (a : Unit) (t : dtyp) (num_elements : Nat) (align0 : (Option Nat)) (b : (@dvalue PFin)),
      (I2FA_Memory_graph (@MemPush PInf) a (@Alloca PFin t num_elements align0) b False))
  | case4 :
      (∀ (a : Unit) (t0 : dtyp) (a0 b : (@dvalue PFin)), (I2FA_Memory_graph (@MemPush PInf) a (@Load
      PFin t0 a0) b False))
  | case5 :
      (∀ (a : Unit) (t1 : dtyp) (a1 v : (@dvalue PFin)) (b : Unit), (I2FA_Memory_graph (@MemPush
      PInf) a (@Store PFin t1 a1 v) b False))
  | case6 :
      (∀ (a : Unit) (cv : impure_conversion) (t_from : dtyp) (v0 : (@dvalue PFin)) (t_to : dtyp) (b
      : (@dvalue PFin)), (I2FA_Memory_graph (@MemPush PInf) a (@Conv PFin cv t_from v0 t_to) b
      False))
  | case7 :
      (∀ (a b : Unit), (I2FA_Memory_graph (@MemPop PInf) a (@MemPush PFin) b False))
  | case8 :
      (∀ (a b : Unit), (I2FA_Memory_graph (@MemPop PInf) a (@MemPop PFin) b True))
  | case9 :
      (∀ (a : Unit) (t : dtyp) (num_elements : Nat) (align0 : (Option Nat)) (b : (@dvalue PFin)),
      (I2FA_Memory_graph (@MemPop PInf) a (@Alloca PFin t num_elements align0) b False))
  | case10 :
      (∀ (a : Unit) (t0 : dtyp) (a0 b : (@dvalue PFin)), (I2FA_Memory_graph (@MemPop PInf) a (@Load
      PFin t0 a0) b False))
  | case11 :
      (∀ (a : Unit) (t1 : dtyp) (a1 v : (@dvalue PFin)) (b : Unit), (I2FA_Memory_graph (@MemPop
      PInf) a (@Store PFin t1 a1 v) b False))
  | case12 :
      (∀ (a : Unit) (cv : impure_conversion) (t_from : dtyp) (v0 : (@dvalue PFin)) (t_to : dtyp) (b
      : (@dvalue PFin)), (I2FA_Memory_graph (@MemPop PInf) a (@Conv PFin cv t_from v0 t_to) b
      False))
  | case13 :
      (∀ (t : dtyp) (num_elements : Nat) (align0 : (Option Nat)) (a : (@dvalue PInf)) (b : Unit),
      (I2FA_Memory_graph (@Alloca PInf t num_elements align0) a (@MemPush PFin) b False))
  | case14 :
      (∀ (t : dtyp) (num_elements : Nat) (align0 : (Option Nat)) (a : (@dvalue PInf)) (b : Unit),
      (I2FA_Memory_graph (@Alloca PInf t num_elements align0) a (@MemPop PFin) b False))
  | case15 :
      (∀ (τ1 : dtyp) (n1 : Nat) (align1 : (Option Nat)) (dv1 : (@dvalue PInf)) (τ2 : dtyp) (n2 :
      Nat) (align2 : (Option Nat)) (dv2 : (@dvalue PFin)), (I2FA_Memory_graph (@Alloca PInf τ1 n1
      align1) dv1 (@Alloca PFin τ2 n2 align2) dv2 (I2F_dvalue dv1 dv2)))
  | case16 :
      (∀ (t : dtyp) (num_elements : Nat) (align0 : (Option Nat)) (a : (@dvalue PInf)) (t1 : dtyp)
      (a0 b : (@dvalue PFin)), (I2FA_Memory_graph (@Alloca PInf t num_elements align0) a (@Load PFin
      t1 a0) b False))
  | case17 :
      (∀ (t : dtyp) (num_elements : Nat) (align0 : (Option Nat)) (a : (@dvalue PInf)) (t2 : dtyp)
      (a1 v : (@dvalue PFin)) (b : Unit), (I2FA_Memory_graph (@Alloca PInf t num_elements align0) a
      (@Store PFin t2 a1 v) b False))
  | case18 :
      (∀ (t : dtyp) (num_elements : Nat) (align0 : (Option Nat)) (a : (@dvalue PInf)) (cv :
      impure_conversion) (t_from : dtyp) (v0 : (@dvalue PFin)) (t_to : dtyp) (b : (@dvalue PFin)),
      (I2FA_Memory_graph (@Alloca PInf t num_elements align0) a (@Conv PFin cv t_from v0 t_to) b
      False))
  | case19 :
      (∀ (t0 : dtyp) (a0 a : (@dvalue PInf)) (b : Unit), (I2FA_Memory_graph (@Load PInf t0 a0) a
      (@MemPush PFin) b False))
  | case20 :
      (∀ (t0 : dtyp) (a0 a : (@dvalue PInf)) (b : Unit), (I2FA_Memory_graph (@Load PInf t0 a0) a
      (@MemPop PFin) b False))
  | case21 :
      (∀ (t0 : dtyp) (a0 a : (@dvalue PInf)) (t : dtyp) (num_elements : Nat) (align0 : (Option Nat))
      (b : (@dvalue PFin)), (I2FA_Memory_graph (@Load PInf t0 a0) a (@Alloca PFin t num_elements
      align0) b False))
  | case22 :
      (∀ (τ1 : dtyp) (a1 dv1 : (@dvalue PInf)) (τ2 : dtyp) (a2 dv2 : (@dvalue PFin)),
      (I2FA_Memory_graph (@Load PInf τ1 a1) dv1 (@Load PFin τ2 a2) dv2 (I2F_dvalue dv1 dv2)))
  | case23 :
      (∀ (t0 : dtyp) (a0 a : (@dvalue PInf)) (t2 : dtyp) (a2 v : (@dvalue PFin)) (b : Unit),
      (I2FA_Memory_graph (@Load PInf t0 a0) a (@Store PFin t2 a2 v) b False))
  | case24 :
      (∀ (t0 : dtyp) (a0 a : (@dvalue PInf)) (cv : impure_conversion) (t_from : dtyp) (v0 : (@dvalue
      PFin)) (t_to : dtyp) (b : (@dvalue PFin)), (I2FA_Memory_graph (@Load PInf t0 a0) a (@Conv PFin
      cv t_from v0 t_to) b False))
  | case25 :
      (∀ (t1 : dtyp) (a1 v : (@dvalue PInf)) (a b : Unit), (I2FA_Memory_graph (@Store PInf t1 a1 v)
      a (@MemPush PFin) b False))
  | case26 :
      (∀ (t1 : dtyp) (a1 v : (@dvalue PInf)) (a b : Unit), (I2FA_Memory_graph (@Store PInf t1 a1 v)
      a (@MemPop PFin) b False))
  | case27 :
      (∀ (t1 : dtyp) (a1 v : (@dvalue PInf)) (a : Unit) (t : dtyp) (num_elements : Nat) (align0 :
      (Option Nat)) (b : (@dvalue PFin)), (I2FA_Memory_graph (@Store PInf t1 a1 v) a (@Alloca PFin t
      num_elements align0) b False))
  | case28 :
      (∀ (t1 : dtyp) (a1 v : (@dvalue PInf)) (a : Unit) (t0 : dtyp) (a0 b : (@dvalue PFin)),
      (I2FA_Memory_graph (@Store PInf t1 a1 v) a (@Load PFin t0 a0) b False))
  | case29 :
      (∀ (τ1 : dtyp) (a1 v1 : (@dvalue PInf)) (a : Unit) (τ2 : dtyp) (a2 v2 : (@dvalue PFin)) (b :
      Unit), (I2FA_Memory_graph (@Store PInf τ1 a1 v1) a (@Store PFin τ2 a2 v2) b True))
  | case30 :
      (∀ (t1 : dtyp) (a1 v : (@dvalue PInf)) (a : Unit) (cv : impure_conversion) (t_from : dtyp) (v1
      : (@dvalue PFin)) (t_to : dtyp) (b : (@dvalue PFin)), (I2FA_Memory_graph (@Store PInf t1 a1 v)
      a (@Conv PFin cv t_from v1 t_to) b False))
  | case31 :
      (∀ (cv : impure_conversion) (t_from : dtyp) (v0 : (@dvalue PInf)) (t_to : dtyp) (a : (@dvalue
      PInf)) (b : Unit), (I2FA_Memory_graph (@Conv PInf cv t_from v0 t_to) a (@MemPush PFin) b
      False))
  | case32 :
      (∀ (cv : impure_conversion) (t_from : dtyp) (v0 : (@dvalue PInf)) (t_to : dtyp) (a : (@dvalue
      PInf)) (b : Unit), (I2FA_Memory_graph (@Conv PInf cv t_from v0 t_to) a (@MemPop PFin) b
      False))
  | case33 :
      (∀ (cv : impure_conversion) (t_from : dtyp) (v0 : (@dvalue PInf)) (t_to : dtyp) (a : (@dvalue
      PInf)) (t : dtyp) (num_elements : Nat) (align0 : (Option Nat)) (b : (@dvalue PFin)),
      (I2FA_Memory_graph (@Conv PInf cv t_from v0 t_to) a (@Alloca PFin t num_elements align0) b
      False))
  | case34 :
      (∀ (cv : impure_conversion) (t_from : dtyp) (v0 : (@dvalue PInf)) (t_to : dtyp) (a : (@dvalue
      PInf)) (t0 : dtyp) (a0 b : (@dvalue PFin)), (I2FA_Memory_graph (@Conv PInf cv t_from v0 t_to)
      a (@Load PFin t0 a0) b False))
  | case35 :
      (∀ (cv : impure_conversion) (t_from : dtyp) (v0 : (@dvalue PInf)) (t_to : dtyp) (a : (@dvalue
      PInf)) (t1 : dtyp) (a1 v : (@dvalue PFin)) (b : Unit), (I2FA_Memory_graph (@Conv PInf cv
      t_from v0 t_to) a (@Store PFin t1 a1 v) b False))
  | case36 :
      (∀ (cv1 : impure_conversion) (tf1 : dtyp) (v1 : (@dvalue PInf)) (tt1 : dtyp) (dv1 : (@dvalue
      PInf)) (cv2 : impure_conversion) (tf2 : dtyp) (v2 : (@dvalue PFin)) (tt2 : dtyp) (dv2 :
      (@dvalue PFin)), (I2FA_Memory_graph (@Conv PInf cv1 tf1 v1 tt1) dv1 (@Conv PFin cv2 tf2 v2
      tt2) dv2 (I2F_dvalue dv1 dv2)))

abbrev I2FA_Memory_graph_equation_1 := @I2FA_Memory_graph.case1
abbrev I2FA_Memory_graph_equation_2 := @I2FA_Memory_graph.case2
abbrev I2FA_Memory_graph_equation_3 := @I2FA_Memory_graph.case3
abbrev I2FA_Memory_graph_equation_4 := @I2FA_Memory_graph.case4
abbrev I2FA_Memory_graph_equation_5 := @I2FA_Memory_graph.case5
abbrev I2FA_Memory_graph_equation_6 := @I2FA_Memory_graph.case6
abbrev I2FA_Memory_graph_equation_7 := @I2FA_Memory_graph.case7
abbrev I2FA_Memory_graph_equation_8 := @I2FA_Memory_graph.case8
abbrev I2FA_Memory_graph_equation_9 := @I2FA_Memory_graph.case9
abbrev I2FA_Memory_graph_equation_10 := @I2FA_Memory_graph.case10
abbrev I2FA_Memory_graph_equation_11 := @I2FA_Memory_graph.case11
abbrev I2FA_Memory_graph_equation_12 := @I2FA_Memory_graph.case12
abbrev I2FA_Memory_graph_equation_13 := @I2FA_Memory_graph.case13
abbrev I2FA_Memory_graph_equation_14 := @I2FA_Memory_graph.case14
abbrev I2FA_Memory_graph_equation_15 := @I2FA_Memory_graph.case15
abbrev I2FA_Memory_graph_equation_16 := @I2FA_Memory_graph.case16
abbrev I2FA_Memory_graph_equation_17 := @I2FA_Memory_graph.case17
abbrev I2FA_Memory_graph_equation_18 := @I2FA_Memory_graph.case18
abbrev I2FA_Memory_graph_equation_19 := @I2FA_Memory_graph.case19
abbrev I2FA_Memory_graph_equation_20 := @I2FA_Memory_graph.case20
abbrev I2FA_Memory_graph_equation_21 := @I2FA_Memory_graph.case21
abbrev I2FA_Memory_graph_equation_22 := @I2FA_Memory_graph.case22
abbrev I2FA_Memory_graph_equation_23 := @I2FA_Memory_graph.case23
abbrev I2FA_Memory_graph_equation_24 := @I2FA_Memory_graph.case24
abbrev I2FA_Memory_graph_equation_25 := @I2FA_Memory_graph.case25
abbrev I2FA_Memory_graph_equation_26 := @I2FA_Memory_graph.case26
abbrev I2FA_Memory_graph_equation_27 := @I2FA_Memory_graph.case27
abbrev I2FA_Memory_graph_equation_28 := @I2FA_Memory_graph.case28
abbrev I2FA_Memory_graph_equation_29 := @I2FA_Memory_graph.case29
abbrev I2FA_Memory_graph_equation_30 := @I2FA_Memory_graph.case30
abbrev I2FA_Memory_graph_equation_31 := @I2FA_Memory_graph.case31
abbrev I2FA_Memory_graph_equation_32 := @I2FA_Memory_graph.case32
abbrev I2FA_Memory_graph_equation_33 := @I2FA_Memory_graph.case33
abbrev I2FA_Memory_graph_equation_34 := @I2FA_Memory_graph.case34
abbrev I2FA_Memory_graph_equation_35 := @I2FA_Memory_graph.case35
abbrev I2FA_Memory_graph_equation_36 := @I2FA_Memory_graph.case36

def I2FA_Memory_graph_rect :
    (∀ (P : (∀ (e : (@MemoryE PInf).I) (_ : ((@MemoryE PInf).O e)) (f : (@MemoryE PFin).I) (_ :
    ((@MemoryE PFin).O f)) (_ : Prop), Type u)) (_ : (∀ (a b : Unit), (P (@MemPush PInf) a (@MemPush
    PFin) b True))) (_ : (∀ (a b : Unit), (P (@MemPush PInf) a (@MemPop PFin) b False))) (_ : (∀ (a
    : Unit) (t : dtyp) (num_elements : Nat) (align0 : (Option Nat)) (b : (@dvalue PFin)), (P
    (@MemPush PInf) a (@Alloca PFin t num_elements align0) b False))) (_ : (∀ (a : Unit) (t0 : dtyp)
    (a0 b : (@dvalue PFin)), (P (@MemPush PInf) a (@Load PFin t0 a0) b False))) (_ : (∀ (a : Unit)
    (t1 : dtyp) (a1 v : (@dvalue PFin)) (b : Unit), (P (@MemPush PInf) a (@Store PFin t1 a1 v) b
    False))) (_ : (∀ (a : Unit) (cv : impure_conversion) (t_from : dtyp) (v0 : (@dvalue PFin)) (t_to
    : dtyp) (b : (@dvalue PFin)), (P (@MemPush PInf) a (@Conv PFin cv t_from v0 t_to) b False))) (_
    : (∀ (a b : Unit), (P (@MemPop PInf) a (@MemPush PFin) b False))) (_ : (∀ (a b : Unit), (P
    (@MemPop PInf) a (@MemPop PFin) b True))) (_ : (∀ (a : Unit) (t : dtyp) (num_elements : Nat)
    (align0 : (Option Nat)) (b : (@dvalue PFin)), (P (@MemPop PInf) a (@Alloca PFin t num_elements
    align0) b False))) (_ : (∀ (a : Unit) (t0 : dtyp) (a0 b : (@dvalue PFin)), (P (@MemPop PInf) a
    (@Load PFin t0 a0) b False))) (_ : (∀ (a : Unit) (t1 : dtyp) (a1 v : (@dvalue PFin)) (b : Unit),
    (P (@MemPop PInf) a (@Store PFin t1 a1 v) b False))) (_ : (∀ (a : Unit) (cv : impure_conversion)
    (t_from : dtyp) (v0 : (@dvalue PFin)) (t_to : dtyp) (b : (@dvalue PFin)), (P (@MemPop PInf) a
    (@Conv PFin cv t_from v0 t_to) b False))) (_ : (∀ (t : dtyp) (num_elements : Nat) (align0 :
    (Option Nat)) (a : (@dvalue PInf)) (b : Unit), (P (@Alloca PInf t num_elements align0) a
    (@MemPush PFin) b False))) (_ : (∀ (t : dtyp) (num_elements : Nat) (align0 : (Option Nat)) (a :
    (@dvalue PInf)) (b : Unit), (P (@Alloca PInf t num_elements align0) a (@MemPop PFin) b False)))
    (_ : (∀ (τ1 : dtyp) (n1 : Nat) (align1 : (Option Nat)) (dv1 : (@dvalue PInf)) (τ2 : dtyp) (n2 :
    Nat) (align2 : (Option Nat)) (dv2 : (@dvalue PFin)), (P (@Alloca PInf τ1 n1 align1) dv1 (@Alloca
    PFin τ2 n2 align2) dv2 (I2F_dvalue dv1 dv2)))) (_ : (∀ (t : dtyp) (num_elements : Nat) (align0 :
    (Option Nat)) (a : (@dvalue PInf)) (t1 : dtyp) (a0 b : (@dvalue PFin)), (P (@Alloca PInf t
    num_elements align0) a (@Load PFin t1 a0) b False))) (_ : (∀ (t : dtyp) (num_elements : Nat)
    (align0 : (Option Nat)) (a : (@dvalue PInf)) (t2 : dtyp) (a1 v : (@dvalue PFin)) (b : Unit), (P
    (@Alloca PInf t num_elements align0) a (@Store PFin t2 a1 v) b False))) (_ : (∀ (t : dtyp)
    (num_elements : Nat) (align0 : (Option Nat)) (a : (@dvalue PInf)) (cv : impure_conversion)
    (t_from : dtyp) (v0 : (@dvalue PFin)) (t_to : dtyp) (b : (@dvalue PFin)), (P (@Alloca PInf t
    num_elements align0) a (@Conv PFin cv t_from v0 t_to) b False))) (_ : (∀ (t0 : dtyp) (a0 a :
    (@dvalue PInf)) (b : Unit), (P (@Load PInf t0 a0) a (@MemPush PFin) b False))) (_ : (∀ (t0 :
    dtyp) (a0 a : (@dvalue PInf)) (b : Unit), (P (@Load PInf t0 a0) a (@MemPop PFin) b False))) (_ :
    (∀ (t0 : dtyp) (a0 a : (@dvalue PInf)) (t : dtyp) (num_elements : Nat) (align0 : (Option Nat))
    (b : (@dvalue PFin)), (P (@Load PInf t0 a0) a (@Alloca PFin t num_elements align0) b False))) (_
    : (∀ (τ1 : dtyp) (a1 dv1 : (@dvalue PInf)) (τ2 : dtyp) (a2 dv2 : (@dvalue PFin)), (P (@Load PInf
    τ1 a1) dv1 (@Load PFin τ2 a2) dv2 (I2F_dvalue dv1 dv2)))) (_ : (∀ (t0 : dtyp) (a0 a : (@dvalue
    PInf)) (t2 : dtyp) (a2 v : (@dvalue PFin)) (b : Unit), (P (@Load PInf t0 a0) a (@Store PFin t2
    a2 v) b False))) (_ : (∀ (t0 : dtyp) (a0 a : (@dvalue PInf)) (cv : impure_conversion) (t_from :
    dtyp) (v0 : (@dvalue PFin)) (t_to : dtyp) (b : (@dvalue PFin)), (P (@Load PInf t0 a0) a (@Conv
    PFin cv t_from v0 t_to) b False))) (_ : (∀ (t1 : dtyp) (a1 v : (@dvalue PInf)) (a b : Unit), (P
    (@Store PInf t1 a1 v) a (@MemPush PFin) b False))) (_ : (∀ (t1 : dtyp) (a1 v : (@dvalue PInf))
    (a b : Unit), (P (@Store PInf t1 a1 v) a (@MemPop PFin) b False))) (_ : (∀ (t1 : dtyp) (a1 v :
    (@dvalue PInf)) (a : Unit) (t : dtyp) (num_elements : Nat) (align0 : (Option Nat)) (b : (@dvalue
    PFin)), (P (@Store PInf t1 a1 v) a (@Alloca PFin t num_elements align0) b False))) (_ : (∀ (t1 :
    dtyp) (a1 v : (@dvalue PInf)) (a : Unit) (t0 : dtyp) (a0 b : (@dvalue PFin)), (P (@Store PInf t1
    a1 v) a (@Load PFin t0 a0) b False))) (_ : (∀ (τ1 : dtyp) (a1 v1 : (@dvalue PInf)) (a : Unit)
    (τ2 : dtyp) (a2 v2 : (@dvalue PFin)) (b : Unit), (P (@Store PInf τ1 a1 v1) a (@Store PFin τ2 a2
    v2) b True))) (_ : (∀ (t1 : dtyp) (a1 v : (@dvalue PInf)) (a : Unit) (cv : impure_conversion)
    (t_from : dtyp) (v1 : (@dvalue PFin)) (t_to : dtyp) (b : (@dvalue PFin)), (P (@Store PInf t1 a1
    v) a (@Conv PFin cv t_from v1 t_to) b False))) (_ : (∀ (cv : impure_conversion) (t_from : dtyp)
    (v0 : (@dvalue PInf)) (t_to : dtyp) (a : (@dvalue PInf)) (b : Unit), (P (@Conv PInf cv t_from v0
    t_to) a (@MemPush PFin) b False))) (_ : (∀ (cv : impure_conversion) (t_from : dtyp) (v0 :
    (@dvalue PInf)) (t_to : dtyp) (a : (@dvalue PInf)) (b : Unit), (P (@Conv PInf cv t_from v0 t_to)
    a (@MemPop PFin) b False))) (_ : (∀ (cv : impure_conversion) (t_from : dtyp) (v0 : (@dvalue
    PInf)) (t_to : dtyp) (a : (@dvalue PInf)) (t : dtyp) (num_elements : Nat) (align0 : (Option
    Nat)) (b : (@dvalue PFin)), (P (@Conv PInf cv t_from v0 t_to) a (@Alloca PFin t num_elements
    align0) b False))) (_ : (∀ (cv : impure_conversion) (t_from : dtyp) (v0 : (@dvalue PInf)) (t_to
    : dtyp) (a : (@dvalue PInf)) (t0 : dtyp) (a0 b : (@dvalue PFin)), (P (@Conv PInf cv t_from v0
    t_to) a (@Load PFin t0 a0) b False))) (_ : (∀ (cv : impure_conversion) (t_from : dtyp) (v0 :
    (@dvalue PInf)) (t_to : dtyp) (a : (@dvalue PInf)) (t1 : dtyp) (a1 v : (@dvalue PFin)) (b :
    Unit), (P (@Conv PInf cv t_from v0 t_to) a (@Store PFin t1 a1 v) b False))) (_ : (∀ (cv1 :
    impure_conversion) (tf1 : dtyp) (v1 : (@dvalue PInf)) (tt1 : dtyp) (dv1 : (@dvalue PInf)) (cv2 :
    impure_conversion) (tf2 : dtyp) (v2 : (@dvalue PFin)) (tt2 : dtyp) (dv2 : (@dvalue PFin)), (P
    (@Conv PInf cv1 tf1 v1 tt1) dv1 (@Conv PFin cv2 tf2 v2 tt2) dv2 (I2F_dvalue dv1 dv2)))) {m :
    (@MemoryE PInf).I} {a : ((@MemoryE PInf).O m)} {m0 : (@MemoryE PFin).I} {b : ((@MemoryE PFin).O
    m0)} {P0 : Prop} (_ : (I2FA_Memory_graph m a m0 b P0)), (P m a m0 b P0)) := by
  intro P h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15 h16 h17 h18 h19 h20 h21 h22 h23 h24 h25 h26 h27 h28 h29 h30 h31 h32 h33 h34 h35 h36 e a f b p witness
  cases witness
  next => apply h1
  next => apply h2
  next => apply h3
  next => apply h4
  next => apply h5
  next => apply h6
  next => apply h7
  next => apply h8
  next => apply h9
  next => apply h10
  next => apply h11
  next => apply h12
  next => apply h13
  next => apply h14
  next => apply h15
  next => apply h16
  next => apply h17
  next => apply h18
  next => apply h19
  next => apply h20
  next => apply h21
  next => apply h22
  next => apply h23
  next => apply h24
  next => apply h25
  next => apply h26
  next => apply h27
  next => apply h28
  next => apply h29
  next => apply h30
  next => apply h31
  next => apply h32
  next => apply h33
  next => apply h34
  next => apply h35
  next => apply h36

def I2FA_Memory_graph_correct :
    (∀ (m : (@MemoryE PInf).I) (a : ((@MemoryE PInf).O m)) (m0 : (@MemoryE PFin).I) (b : ((@MemoryE
    PFin).O m0)), (I2FA_Memory_graph m a m0 b (I2FA_Memory m a m0 b))) := by
  intro e a f b
  cases e <;> cases f <;> first
    | apply I2FA_Memory_graph.case1
    | apply I2FA_Memory_graph.case2
    | apply I2FA_Memory_graph.case3
    | apply I2FA_Memory_graph.case4
    | apply I2FA_Memory_graph.case5
    | apply I2FA_Memory_graph.case6
    | apply I2FA_Memory_graph.case7
    | apply I2FA_Memory_graph.case8
    | apply I2FA_Memory_graph.case9
    | apply I2FA_Memory_graph.case10
    | apply I2FA_Memory_graph.case11
    | apply I2FA_Memory_graph.case12
    | apply I2FA_Memory_graph.case13
    | apply I2FA_Memory_graph.case14
    | apply I2FA_Memory_graph.case15
    | apply I2FA_Memory_graph.case16
    | apply I2FA_Memory_graph.case17
    | apply I2FA_Memory_graph.case18
    | apply I2FA_Memory_graph.case19
    | apply I2FA_Memory_graph.case20
    | apply I2FA_Memory_graph.case21
    | apply I2FA_Memory_graph.case22
    | apply I2FA_Memory_graph.case23
    | apply I2FA_Memory_graph.case24
    | apply I2FA_Memory_graph.case25
    | apply I2FA_Memory_graph.case26
    | apply I2FA_Memory_graph.case27
    | apply I2FA_Memory_graph.case28
    | apply I2FA_Memory_graph.case29
    | apply I2FA_Memory_graph.case30
    | apply I2FA_Memory_graph.case31
    | apply I2FA_Memory_graph.case32
    | apply I2FA_Memory_graph.case33
    | apply I2FA_Memory_graph.case34
    | apply I2FA_Memory_graph.case35
    | apply I2FA_Memory_graph.case36

def I2FA_Memory_elim :
    (∀ (P : (∀ (e : (@MemoryE PInf).I) (_ : ((@MemoryE PInf).O e)) (f : (@MemoryE PFin).I) (_ :
    ((@MemoryE PFin).O f)) (_ : Prop), Type u)) (_ : (∀ (a b : Unit), (P (@MemPush PInf) a (@MemPush
    PFin) b True))) (_ : (∀ (a b : Unit), (P (@MemPush PInf) a (@MemPop PFin) b False))) (_ : (∀ (a
    : Unit) (t : dtyp) (num_elements : Nat) (align0 : (Option Nat)) (b : (@dvalue PFin)), (P
    (@MemPush PInf) a (@Alloca PFin t num_elements align0) b False))) (_ : (∀ (a : Unit) (t0 : dtyp)
    (a0 b : (@dvalue PFin)), (P (@MemPush PInf) a (@Load PFin t0 a0) b False))) (_ : (∀ (a : Unit)
    (t1 : dtyp) (a1 v : (@dvalue PFin)) (b : Unit), (P (@MemPush PInf) a (@Store PFin t1 a1 v) b
    False))) (_ : (∀ (a : Unit) (cv : impure_conversion) (t_from : dtyp) (v0 : (@dvalue PFin)) (t_to
    : dtyp) (b : (@dvalue PFin)), (P (@MemPush PInf) a (@Conv PFin cv t_from v0 t_to) b False))) (_
    : (∀ (a b : Unit), (P (@MemPop PInf) a (@MemPush PFin) b False))) (_ : (∀ (a b : Unit), (P
    (@MemPop PInf) a (@MemPop PFin) b True))) (_ : (∀ (a : Unit) (t : dtyp) (num_elements : Nat)
    (align0 : (Option Nat)) (b : (@dvalue PFin)), (P (@MemPop PInf) a (@Alloca PFin t num_elements
    align0) b False))) (_ : (∀ (a : Unit) (t0 : dtyp) (a0 b : (@dvalue PFin)), (P (@MemPop PInf) a
    (@Load PFin t0 a0) b False))) (_ : (∀ (a : Unit) (t1 : dtyp) (a1 v : (@dvalue PFin)) (b : Unit),
    (P (@MemPop PInf) a (@Store PFin t1 a1 v) b False))) (_ : (∀ (a : Unit) (cv : impure_conversion)
    (t_from : dtyp) (v0 : (@dvalue PFin)) (t_to : dtyp) (b : (@dvalue PFin)), (P (@MemPop PInf) a
    (@Conv PFin cv t_from v0 t_to) b False))) (_ : (∀ (t : dtyp) (num_elements : Nat) (align0 :
    (Option Nat)) (a : (@dvalue PInf)) (b : Unit), (P (@Alloca PInf t num_elements align0) a
    (@MemPush PFin) b False))) (_ : (∀ (t : dtyp) (num_elements : Nat) (align0 : (Option Nat)) (a :
    (@dvalue PInf)) (b : Unit), (P (@Alloca PInf t num_elements align0) a (@MemPop PFin) b False)))
    (_ : (∀ (τ1 : dtyp) (n1 : Nat) (align1 : (Option Nat)) (dv1 : (@dvalue PInf)) (τ2 : dtyp) (n2 :
    Nat) (align2 : (Option Nat)) (dv2 : (@dvalue PFin)), (P (@Alloca PInf τ1 n1 align1) dv1 (@Alloca
    PFin τ2 n2 align2) dv2 (I2F_dvalue dv1 dv2)))) (_ : (∀ (t : dtyp) (num_elements : Nat) (align0 :
    (Option Nat)) (a : (@dvalue PInf)) (t1 : dtyp) (a0 b : (@dvalue PFin)), (P (@Alloca PInf t
    num_elements align0) a (@Load PFin t1 a0) b False))) (_ : (∀ (t : dtyp) (num_elements : Nat)
    (align0 : (Option Nat)) (a : (@dvalue PInf)) (t2 : dtyp) (a1 v : (@dvalue PFin)) (b : Unit), (P
    (@Alloca PInf t num_elements align0) a (@Store PFin t2 a1 v) b False))) (_ : (∀ (t : dtyp)
    (num_elements : Nat) (align0 : (Option Nat)) (a : (@dvalue PInf)) (cv : impure_conversion)
    (t_from : dtyp) (v0 : (@dvalue PFin)) (t_to : dtyp) (b : (@dvalue PFin)), (P (@Alloca PInf t
    num_elements align0) a (@Conv PFin cv t_from v0 t_to) b False))) (_ : (∀ (t0 : dtyp) (a0 a :
    (@dvalue PInf)) (b : Unit), (P (@Load PInf t0 a0) a (@MemPush PFin) b False))) (_ : (∀ (t0 :
    dtyp) (a0 a : (@dvalue PInf)) (b : Unit), (P (@Load PInf t0 a0) a (@MemPop PFin) b False))) (_ :
    (∀ (t0 : dtyp) (a0 a : (@dvalue PInf)) (t : dtyp) (num_elements : Nat) (align0 : (Option Nat))
    (b : (@dvalue PFin)), (P (@Load PInf t0 a0) a (@Alloca PFin t num_elements align0) b False))) (_
    : (∀ (τ1 : dtyp) (a1 dv1 : (@dvalue PInf)) (τ2 : dtyp) (a2 dv2 : (@dvalue PFin)), (P (@Load PInf
    τ1 a1) dv1 (@Load PFin τ2 a2) dv2 (I2F_dvalue dv1 dv2)))) (_ : (∀ (t0 : dtyp) (a0 a : (@dvalue
    PInf)) (t2 : dtyp) (a2 v : (@dvalue PFin)) (b : Unit), (P (@Load PInf t0 a0) a (@Store PFin t2
    a2 v) b False))) (_ : (∀ (t0 : dtyp) (a0 a : (@dvalue PInf)) (cv : impure_conversion) (t_from :
    dtyp) (v0 : (@dvalue PFin)) (t_to : dtyp) (b : (@dvalue PFin)), (P (@Load PInf t0 a0) a (@Conv
    PFin cv t_from v0 t_to) b False))) (_ : (∀ (t1 : dtyp) (a1 v : (@dvalue PInf)) (a b : Unit), (P
    (@Store PInf t1 a1 v) a (@MemPush PFin) b False))) (_ : (∀ (t1 : dtyp) (a1 v : (@dvalue PInf))
    (a b : Unit), (P (@Store PInf t1 a1 v) a (@MemPop PFin) b False))) (_ : (∀ (t1 : dtyp) (a1 v :
    (@dvalue PInf)) (a : Unit) (t : dtyp) (num_elements : Nat) (align0 : (Option Nat)) (b : (@dvalue
    PFin)), (P (@Store PInf t1 a1 v) a (@Alloca PFin t num_elements align0) b False))) (_ : (∀ (t1 :
    dtyp) (a1 v : (@dvalue PInf)) (a : Unit) (t0 : dtyp) (a0 b : (@dvalue PFin)), (P (@Store PInf t1
    a1 v) a (@Load PFin t0 a0) b False))) (_ : (∀ (τ1 : dtyp) (a1 v1 : (@dvalue PInf)) (a : Unit)
    (τ2 : dtyp) (a2 v2 : (@dvalue PFin)) (b : Unit), (P (@Store PInf τ1 a1 v1) a (@Store PFin τ2 a2
    v2) b True))) (_ : (∀ (t1 : dtyp) (a1 v : (@dvalue PInf)) (a : Unit) (cv : impure_conversion)
    (t_from : dtyp) (v1 : (@dvalue PFin)) (t_to : dtyp) (b : (@dvalue PFin)), (P (@Store PInf t1 a1
    v) a (@Conv PFin cv t_from v1 t_to) b False))) (_ : (∀ (cv : impure_conversion) (t_from : dtyp)
    (v0 : (@dvalue PInf)) (t_to : dtyp) (a : (@dvalue PInf)) (b : Unit), (P (@Conv PInf cv t_from v0
    t_to) a (@MemPush PFin) b False))) (_ : (∀ (cv : impure_conversion) (t_from : dtyp) (v0 :
    (@dvalue PInf)) (t_to : dtyp) (a : (@dvalue PInf)) (b : Unit), (P (@Conv PInf cv t_from v0 t_to)
    a (@MemPop PFin) b False))) (_ : (∀ (cv : impure_conversion) (t_from : dtyp) (v0 : (@dvalue
    PInf)) (t_to : dtyp) (a : (@dvalue PInf)) (t : dtyp) (num_elements : Nat) (align0 : (Option
    Nat)) (b : (@dvalue PFin)), (P (@Conv PInf cv t_from v0 t_to) a (@Alloca PFin t num_elements
    align0) b False))) (_ : (∀ (cv : impure_conversion) (t_from : dtyp) (v0 : (@dvalue PInf)) (t_to
    : dtyp) (a : (@dvalue PInf)) (t0 : dtyp) (a0 b : (@dvalue PFin)), (P (@Conv PInf cv t_from v0
    t_to) a (@Load PFin t0 a0) b False))) (_ : (∀ (cv : impure_conversion) (t_from : dtyp) (v0 :
    (@dvalue PInf)) (t_to : dtyp) (a : (@dvalue PInf)) (t1 : dtyp) (a1 v : (@dvalue PFin)) (b :
    Unit), (P (@Conv PInf cv t_from v0 t_to) a (@Store PFin t1 a1 v) b False))) (_ : (∀ (cv1 :
    impure_conversion) (tf1 : dtyp) (v1 : (@dvalue PInf)) (tt1 : dtyp) (dv1 : (@dvalue PInf)) (cv2 :
    impure_conversion) (tf2 : dtyp) (v2 : (@dvalue PFin)) (tt2 : dtyp) (dv2 : (@dvalue PFin)), (P
    (@Conv PInf cv1 tf1 v1 tt1) dv1 (@Conv PFin cv2 tf2 v2 tt2) dv2 (I2F_dvalue dv1 dv2)))) (m :
    (@MemoryE PInf).I) (a : ((@MemoryE PInf).O m)) (m0 : (@MemoryE PFin).I) (b : ((@MemoryE PFin).O
    m0)), (P m a m0 b (I2FA_Memory m a m0 b))) := by
  intro P h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15 h16 h17 h18 h19 h20 h21 h22 h23 h24 h25 h26 h27 h28 h29 h30 h31 h32 h33 h34 h35 h36 e a f b
  exact I2FA_Memory_graph_rect P h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15 h16 h17 h18 h19 h20
    h21 h22 h23 h24 h25 h26 h27 h28 h29 h30 h31 h32 h33 h34 h35 h36 (I2FA_Memory_graph_correct e a f
    b)

instance FunctionalInduction_I2FA_Memory :
    (FunctionalInduction.{0, 0} I2FA_Memory) := ⟨_, I2FA_Memory_graph_correct⟩

instance FunctionalElimination_I2FA_Memory :
    FunctionalElimination I2FA_Memory (∀ (P : (∀ (e : (@MemoryE PInf).I) (_ : ((@MemoryE PInf).O e)) (f : (@MemoryE PFin).I) (_ :
    ((@MemoryE PFin).O f)) (_ : Prop), Type u)) (_ : (∀ (a b : Unit), (P (@MemPush PInf) a (@MemPush
    PFin) b True))) (_ : (∀ (a b : Unit), (P (@MemPush PInf) a (@MemPop PFin) b False))) (_ : (∀ (a
    : Unit) (t : dtyp) (num_elements : Nat) (align0 : (Option Nat)) (b : (@dvalue PFin)), (P
    (@MemPush PInf) a (@Alloca PFin t num_elements align0) b False))) (_ : (∀ (a : Unit) (t0 : dtyp)
    (a0 b : (@dvalue PFin)), (P (@MemPush PInf) a (@Load PFin t0 a0) b False))) (_ : (∀ (a : Unit)
    (t1 : dtyp) (a1 v : (@dvalue PFin)) (b : Unit), (P (@MemPush PInf) a (@Store PFin t1 a1 v) b
    False))) (_ : (∀ (a : Unit) (cv : impure_conversion) (t_from : dtyp) (v0 : (@dvalue PFin)) (t_to
    : dtyp) (b : (@dvalue PFin)), (P (@MemPush PInf) a (@Conv PFin cv t_from v0 t_to) b False))) (_
    : (∀ (a b : Unit), (P (@MemPop PInf) a (@MemPush PFin) b False))) (_ : (∀ (a b : Unit), (P
    (@MemPop PInf) a (@MemPop PFin) b True))) (_ : (∀ (a : Unit) (t : dtyp) (num_elements : Nat)
    (align0 : (Option Nat)) (b : (@dvalue PFin)), (P (@MemPop PInf) a (@Alloca PFin t num_elements
    align0) b False))) (_ : (∀ (a : Unit) (t0 : dtyp) (a0 b : (@dvalue PFin)), (P (@MemPop PInf) a
    (@Load PFin t0 a0) b False))) (_ : (∀ (a : Unit) (t1 : dtyp) (a1 v : (@dvalue PFin)) (b : Unit),
    (P (@MemPop PInf) a (@Store PFin t1 a1 v) b False))) (_ : (∀ (a : Unit) (cv : impure_conversion)
    (t_from : dtyp) (v0 : (@dvalue PFin)) (t_to : dtyp) (b : (@dvalue PFin)), (P (@MemPop PInf) a
    (@Conv PFin cv t_from v0 t_to) b False))) (_ : (∀ (t : dtyp) (num_elements : Nat) (align0 :
    (Option Nat)) (a : (@dvalue PInf)) (b : Unit), (P (@Alloca PInf t num_elements align0) a
    (@MemPush PFin) b False))) (_ : (∀ (t : dtyp) (num_elements : Nat) (align0 : (Option Nat)) (a :
    (@dvalue PInf)) (b : Unit), (P (@Alloca PInf t num_elements align0) a (@MemPop PFin) b False)))
    (_ : (∀ (τ1 : dtyp) (n1 : Nat) (align1 : (Option Nat)) (dv1 : (@dvalue PInf)) (τ2 : dtyp) (n2 :
    Nat) (align2 : (Option Nat)) (dv2 : (@dvalue PFin)), (P (@Alloca PInf τ1 n1 align1) dv1 (@Alloca
    PFin τ2 n2 align2) dv2 (I2F_dvalue dv1 dv2)))) (_ : (∀ (t : dtyp) (num_elements : Nat) (align0 :
    (Option Nat)) (a : (@dvalue PInf)) (t1 : dtyp) (a0 b : (@dvalue PFin)), (P (@Alloca PInf t
    num_elements align0) a (@Load PFin t1 a0) b False))) (_ : (∀ (t : dtyp) (num_elements : Nat)
    (align0 : (Option Nat)) (a : (@dvalue PInf)) (t2 : dtyp) (a1 v : (@dvalue PFin)) (b : Unit), (P
    (@Alloca PInf t num_elements align0) a (@Store PFin t2 a1 v) b False))) (_ : (∀ (t : dtyp)
    (num_elements : Nat) (align0 : (Option Nat)) (a : (@dvalue PInf)) (cv : impure_conversion)
    (t_from : dtyp) (v0 : (@dvalue PFin)) (t_to : dtyp) (b : (@dvalue PFin)), (P (@Alloca PInf t
    num_elements align0) a (@Conv PFin cv t_from v0 t_to) b False))) (_ : (∀ (t0 : dtyp) (a0 a :
    (@dvalue PInf)) (b : Unit), (P (@Load PInf t0 a0) a (@MemPush PFin) b False))) (_ : (∀ (t0 :
    dtyp) (a0 a : (@dvalue PInf)) (b : Unit), (P (@Load PInf t0 a0) a (@MemPop PFin) b False))) (_ :
    (∀ (t0 : dtyp) (a0 a : (@dvalue PInf)) (t : dtyp) (num_elements : Nat) (align0 : (Option Nat))
    (b : (@dvalue PFin)), (P (@Load PInf t0 a0) a (@Alloca PFin t num_elements align0) b False))) (_
    : (∀ (τ1 : dtyp) (a1 dv1 : (@dvalue PInf)) (τ2 : dtyp) (a2 dv2 : (@dvalue PFin)), (P (@Load PInf
    τ1 a1) dv1 (@Load PFin τ2 a2) dv2 (I2F_dvalue dv1 dv2)))) (_ : (∀ (t0 : dtyp) (a0 a : (@dvalue
    PInf)) (t2 : dtyp) (a2 v : (@dvalue PFin)) (b : Unit), (P (@Load PInf t0 a0) a (@Store PFin t2
    a2 v) b False))) (_ : (∀ (t0 : dtyp) (a0 a : (@dvalue PInf)) (cv : impure_conversion) (t_from :
    dtyp) (v0 : (@dvalue PFin)) (t_to : dtyp) (b : (@dvalue PFin)), (P (@Load PInf t0 a0) a (@Conv
    PFin cv t_from v0 t_to) b False))) (_ : (∀ (t1 : dtyp) (a1 v : (@dvalue PInf)) (a b : Unit), (P
    (@Store PInf t1 a1 v) a (@MemPush PFin) b False))) (_ : (∀ (t1 : dtyp) (a1 v : (@dvalue PInf))
    (a b : Unit), (P (@Store PInf t1 a1 v) a (@MemPop PFin) b False))) (_ : (∀ (t1 : dtyp) (a1 v :
    (@dvalue PInf)) (a : Unit) (t : dtyp) (num_elements : Nat) (align0 : (Option Nat)) (b : (@dvalue
    PFin)), (P (@Store PInf t1 a1 v) a (@Alloca PFin t num_elements align0) b False))) (_ : (∀ (t1 :
    dtyp) (a1 v : (@dvalue PInf)) (a : Unit) (t0 : dtyp) (a0 b : (@dvalue PFin)), (P (@Store PInf t1
    a1 v) a (@Load PFin t0 a0) b False))) (_ : (∀ (τ1 : dtyp) (a1 v1 : (@dvalue PInf)) (a : Unit)
    (τ2 : dtyp) (a2 v2 : (@dvalue PFin)) (b : Unit), (P (@Store PInf τ1 a1 v1) a (@Store PFin τ2 a2
    v2) b True))) (_ : (∀ (t1 : dtyp) (a1 v : (@dvalue PInf)) (a : Unit) (cv : impure_conversion)
    (t_from : dtyp) (v1 : (@dvalue PFin)) (t_to : dtyp) (b : (@dvalue PFin)), (P (@Store PInf t1 a1
    v) a (@Conv PFin cv t_from v1 t_to) b False))) (_ : (∀ (cv : impure_conversion) (t_from : dtyp)
    (v0 : (@dvalue PInf)) (t_to : dtyp) (a : (@dvalue PInf)) (b : Unit), (P (@Conv PInf cv t_from v0
    t_to) a (@MemPush PFin) b False))) (_ : (∀ (cv : impure_conversion) (t_from : dtyp) (v0 :
    (@dvalue PInf)) (t_to : dtyp) (a : (@dvalue PInf)) (b : Unit), (P (@Conv PInf cv t_from v0 t_to)
    a (@MemPop PFin) b False))) (_ : (∀ (cv : impure_conversion) (t_from : dtyp) (v0 : (@dvalue
    PInf)) (t_to : dtyp) (a : (@dvalue PInf)) (t : dtyp) (num_elements : Nat) (align0 : (Option
    Nat)) (b : (@dvalue PFin)), (P (@Conv PInf cv t_from v0 t_to) a (@Alloca PFin t num_elements
    align0) b False))) (_ : (∀ (cv : impure_conversion) (t_from : dtyp) (v0 : (@dvalue PInf)) (t_to
    : dtyp) (a : (@dvalue PInf)) (t0 : dtyp) (a0 b : (@dvalue PFin)), (P (@Conv PInf cv t_from v0
    t_to) a (@Load PFin t0 a0) b False))) (_ : (∀ (cv : impure_conversion) (t_from : dtyp) (v0 :
    (@dvalue PInf)) (t_to : dtyp) (a : (@dvalue PInf)) (t1 : dtyp) (a1 v : (@dvalue PFin)) (b :
    Unit), (P (@Conv PInf cv t_from v0 t_to) a (@Store PFin t1 a1 v) b False))) (_ : (∀ (cv1 :
    impure_conversion) (tf1 : dtyp) (v1 : (@dvalue PInf)) (tt1 : dtyp) (dv1 : (@dvalue PInf)) (cv2 :
    impure_conversion) (tf2 : dtyp) (v2 : (@dvalue PFin)) (tt2 : dtyp) (dv2 : (@dvalue PFin)), (P
    (@Conv PInf cv1 tf1 v1 tt1) dv1 (@Conv PFin cv2 tf2 v2 tt2) dv2 (I2F_dvalue dv1 dv2)))) (m :
    (@MemoryE PInf).I) (a : ((@MemoryE PInf).O m)) (m0 : (@MemoryE PFin).I) (b : ((@MemoryE PFin).O
    m0)), (P m a m0 b (I2FA_Memory m a m0 b))) 37 :=
  ⟨I2FA_Memory_elim⟩

theorem I2FA_Draw_equation_1 :
    (∀ (τ1 : dtyp) (dv1 : (@dvalue PInf)) (τ2 : dtyp) (dv2 : (@dvalue PFin)), (Eq (I2FA_Draw (Draw
    τ1) dv1 (Draw τ2) dv2) (I2F_dvalue dv1 dv2))) := by intros; rfl

inductive I2FA_Draw_graph :
    (∀ (e : (@DrawE PInf).I) (_ : ((@DrawE PInf).O e)) (f : (@DrawE PFin).I) (_ : ((@DrawE PFin).O
    f)) (_ : Prop), Type) where
  | case1 :
      (∀ (τ1 : dtyp) (dv1 : (@dvalue PInf)) (τ2 : dtyp) (dv2 : (@dvalue PFin)), (I2FA_Draw_graph
      (Draw τ1) dv1 (Draw τ2) dv2 (I2F_dvalue dv1 dv2)))

abbrev I2FA_Draw_graph_equation_1 := @I2FA_Draw_graph.case1

def I2FA_Draw_graph_rect :
    (∀ (P : (∀ (e : (@DrawE PInf).I) (_ : ((@DrawE PInf).O e)) (f : (@DrawE PFin).I) (_ : ((@DrawE
    PFin).O f)) (_ : Prop), Type u)) (_ : (∀ (τ1 : dtyp) (dv1 : (@dvalue PInf)) (τ2 : dtyp) (dv2 :
    (@dvalue PFin)), (P (Draw τ1) dv1 (Draw τ2) dv2 (I2F_dvalue dv1 dv2)))) {d : (@DrawE PInf).I} {a
    : ((@DrawE PInf).O d)} {d0 : (@DrawE PFin).I} {b : ((@DrawE PFin).O d0)} {P0 : Prop} (_ :
    (I2FA_Draw_graph d a d0 b P0)), (P d a d0 b P0)) := by
  intro P h1 e a f b p witness
  cases witness
  next => apply h1

def I2FA_Draw_graph_correct :
    (∀ (d : (@DrawE PInf).I) (a : ((@DrawE PInf).O d)) (d0 : (@DrawE PFin).I) (b : ((@DrawE PFin).O
    d0)), (I2FA_Draw_graph d a d0 b (I2FA_Draw d a d0 b))) := by
  intro e a f b
  cases e <;> cases f <;> first
    | apply I2FA_Draw_graph.case1

def I2FA_Draw_elim :
    (∀ (P : (∀ (e : (@DrawE PInf).I) (_ : ((@DrawE PInf).O e)) (f : (@DrawE PFin).I) (_ : ((@DrawE
    PFin).O f)) (_ : Prop), Type u)) (_ : (∀ (τ1 : dtyp) (dv1 : (@dvalue PInf)) (τ2 : dtyp) (dv2 :
    (@dvalue PFin)), (P (Draw τ1) dv1 (Draw τ2) dv2 (I2F_dvalue dv1 dv2)))) (d : (@DrawE PInf).I) (a
    : ((@DrawE PInf).O d)) (d0 : (@DrawE PFin).I) (b : ((@DrawE PFin).O d0)), (P d a d0 b (I2FA_Draw
    d a d0 b))) := by
  intro P h1 e a f b
  exact I2FA_Draw_graph_rect P h1 (I2FA_Draw_graph_correct e a f b)

instance FunctionalInduction_I2FA_Draw :
    (FunctionalInduction.{0, 0} I2FA_Draw) := ⟨_, I2FA_Draw_graph_correct⟩

instance FunctionalElimination_I2FA_Draw :
    FunctionalElimination I2FA_Draw (∀ (P : (∀ (e : (@DrawE PInf).I) (_ : ((@DrawE PInf).O e)) (f : (@DrawE PFin).I) (_ : ((@DrawE
    PFin).O f)) (_ : Prop), Type u)) (_ : (∀ (τ1 : dtyp) (dv1 : (@dvalue PInf)) (τ2 : dtyp) (dv2 :
    (@dvalue PFin)), (P (Draw τ1) dv1 (Draw τ2) dv2 (I2F_dvalue dv1 dv2)))) (d : (@DrawE PInf).I) (a
    : ((@DrawE PInf).O d)) (d0 : (@DrawE PFin).I) (b : ((@DrawE PFin).O d0)), (P d a d0 b (I2FA_Draw
    d a d0 b))) 2 :=
  ⟨I2FA_Draw_elim⟩

theorem I2FA_Exc_equation_1 :
    (∀ (exc1 : (@exc PInf)) (a : Empty) (exc2 : (@exc PFin)) (b : Empty), (Eq (I2FA_Exc (@LLVMExc
    PInf exc1) a (@LLVMExc PFin exc2) b) False)) := by intros; rfl

inductive I2FA_Exc_graph :
    (∀ (e : (@LLVMExcE PInf).I) (_ : ((@LLVMExcE PInf).O e)) (f : (@LLVMExcE PFin).I) (_ :
    ((@LLVMExcE PFin).O f)) (_ : Prop), Type) where
  | case1 :
      (∀ (exc1 : (@exc PInf)) (a : Empty) (exc2 : (@exc PFin)) (b : Empty), (I2FA_Exc_graph
      (@LLVMExc PInf exc1) a (@LLVMExc PFin exc2) b False))

abbrev I2FA_Exc_graph_equation_1 := @I2FA_Exc_graph.case1

def I2FA_Exc_graph_rect :
    (∀ (P : (∀ (e : (@LLVMExcE PInf).I) (_ : ((@LLVMExcE PInf).O e)) (f : (@LLVMExcE PFin).I) (_ :
    ((@LLVMExcE PFin).O f)) (_ : Prop), Type u)) (_ : (∀ (exc1 : (@exc PInf)) (a : Empty) (exc2 :
    (@exc PFin)) (b : Empty), (P (@LLVMExc PInf exc1) a (@LLVMExc PFin exc2) b False))) {l :
    (@LLVMExcE PInf).I} {a : ((@LLVMExcE PInf).O l)} {l0 : (@LLVMExcE PFin).I} {b : ((@LLVMExcE
    PFin).O l0)} {P0 : Prop} (_ : (I2FA_Exc_graph l a l0 b P0)), (P l a l0 b P0)) := by
  intro P h1 e a f b p witness
  cases witness
  next => apply h1

def I2FA_Exc_graph_correct :
    (∀ (l : (@LLVMExcE PInf).I) (a : ((@LLVMExcE PInf).O l)) (l0 : (@LLVMExcE PFin).I) (b :
    ((@LLVMExcE PFin).O l0)), (I2FA_Exc_graph l a l0 b (I2FA_Exc l a l0 b))) := by
  intro e a f b
  cases e <;> cases f <;> first
    | apply I2FA_Exc_graph.case1

def I2FA_Exc_elim :
    (∀ (P : (∀ (e : (@LLVMExcE PInf).I) (_ : ((@LLVMExcE PInf).O e)) (f : (@LLVMExcE PFin).I) (_ :
    ((@LLVMExcE PFin).O f)) (_ : Prop), Type u)) (_ : (∀ (exc1 : (@exc PInf)) (a : Empty) (exc2 :
    (@exc PFin)) (b : Empty), (P (@LLVMExc PInf exc1) a (@LLVMExc PFin exc2) b False))) (l :
    (@LLVMExcE PInf).I) (a : ((@LLVMExcE PInf).O l)) (l0 : (@LLVMExcE PFin).I) (b : ((@LLVMExcE
    PFin).O l0)), (P l a l0 b (I2FA_Exc l a l0 b))) := by
  intro P h1 e a f b
  exact I2FA_Exc_graph_rect P h1 (I2FA_Exc_graph_correct e a f b)

instance FunctionalInduction_I2FA_Exc :
    (FunctionalInduction.{0, 0} I2FA_Exc) := ⟨_, I2FA_Exc_graph_correct⟩

instance FunctionalElimination_I2FA_Exc :
    FunctionalElimination I2FA_Exc (∀ (P : (∀ (e : (@LLVMExcE PInf).I) (_ : ((@LLVMExcE PInf).O e)) (f : (@LLVMExcE PFin).I) (_ :
    ((@LLVMExcE PFin).O f)) (_ : Prop), Type u)) (_ : (∀ (exc1 : (@exc PInf)) (a : Empty) (exc2 :
    (@exc PFin)) (b : Empty), (P (@LLVMExc PInf exc1) a (@LLVMExc PFin exc2) b False))) (l :
    (@LLVMExcE PInf).I) (a : ((@LLVMExcE PInf).O l)) (l0 : (@LLVMExcE PFin).I) (b : ((@LLVMExcE
    PFin).O l0)), (P l a l0 b (I2FA_Exc l a l0 b))) 2 :=
  ⟨I2FA_Exc_elim⟩

theorem I2FA_OOM_equation_1 :
    (∀ (u1 : Unit) (a : Empty) (u2 : Unit) (b : Empty), (Eq (I2FA_OOM (ThrowOOM u1) a (ThrowOOM u2)
    b) False)) := by intros; rfl

inductive I2FA_OOM_graph :
    (∀ (e : OOME.I) (_ : (OOME.O e)) (f : OOME.I) (_ : (OOME.O f)) (_ : Prop), Type) where
  | case1 :
      (∀ (u1 : Unit) (a : Empty) (u2 : Unit) (b : Empty), (I2FA_OOM_graph (ThrowOOM u1) a (ThrowOOM
      u2) b False))

abbrev I2FA_OOM_graph_equation_1 := @I2FA_OOM_graph.case1

def I2FA_OOM_graph_rect :
    (∀ (P : (∀ (e : OOME.I) (_ : (OOME.O e)) (f : OOME.I) (_ : (OOME.O f)) (_ : Prop), Type u)) (_ :
    (∀ (u1 : Unit) (a : Empty) (u2 : Unit) (b : Empty), (P (ThrowOOM u1) a (ThrowOOM u2) b False)))
    {o : OOME.I} {a : (OOME.O o)} {o0 : OOME.I} {b : (OOME.O o0)} {P0 : Prop} (_ : (I2FA_OOM_graph o
    a o0 b P0)), (P o a o0 b P0)) := by
  intro P h1 e a f b p witness
  cases witness
  next => apply h1

def I2FA_OOM_graph_correct :
    (∀ (o : OOME.I) (a : (OOME.O o)) (o0 : OOME.I) (b : (OOME.O o0)), (I2FA_OOM_graph o a o0 b
    (I2FA_OOM o a o0 b))) := by
  intro e a f b
  cases e <;> cases f <;> first
    | apply I2FA_OOM_graph.case1

def I2FA_OOM_elim :
    (∀ (P : (∀ (e : OOME.I) (_ : (OOME.O e)) (f : OOME.I) (_ : (OOME.O f)) (_ : Prop), Type u)) (_ :
    (∀ (u1 : Unit) (a : Empty) (u2 : Unit) (b : Empty), (P (ThrowOOM u1) a (ThrowOOM u2) b False)))
    (o : OOME.I) (a : (OOME.O o)) (o0 : OOME.I) (b : (OOME.O o0)), (P o a o0 b (I2FA_OOM o a o0 b))) := by
  intro P h1 e a f b
  exact I2FA_OOM_graph_rect P h1 (I2FA_OOM_graph_correct e a f b)

instance FunctionalInduction_I2FA_OOM :
    (FunctionalInduction.{0, 0} I2FA_OOM) := ⟨_, I2FA_OOM_graph_correct⟩

instance FunctionalElimination_I2FA_OOM :
    FunctionalElimination I2FA_OOM (∀ (P : (∀ (e : OOME.I) (_ : (OOME.O e)) (f : OOME.I) (_ : (OOME.O f)) (_ : Prop), Type u)) (_ :
    (∀ (u1 : Unit) (a : Empty) (u2 : Unit) (b : Empty), (P (ThrowOOM u1) a (ThrowOOM u2) b False)))
    (o : OOME.I) (a : (OOME.O o)) (o0 : OOME.I) (b : (OOME.O o0)), (P o a o0 b (I2FA_OOM o a o0 b))) 2 :=
  ⟨I2FA_OOM_elim⟩

theorem I2FA_UB_equation_1 :
    (∀ (u1 : Unit) (a : Empty) (u2 : Unit) (b : Empty), (Eq (I2FA_UB (ThrowUB u1) a (ThrowUB u2) b)
    False)) := by intros; rfl

inductive I2FA_UB_graph :
    (∀ (e : UBE.I) (_ : (UBE.O e)) (f : UBE.I) (_ : (UBE.O f)) (_ : Prop), Type) where
  | case1 :
      (∀ (u1 : Unit) (a : Empty) (u2 : Unit) (b : Empty), (I2FA_UB_graph (ThrowUB u1) a (ThrowUB u2)
      b False))

abbrev I2FA_UB_graph_equation_1 := @I2FA_UB_graph.case1

def I2FA_UB_graph_rect :
    (∀ (P : (∀ (e : UBE.I) (_ : (UBE.O e)) (f : UBE.I) (_ : (UBE.O f)) (_ : Prop), Type u)) (_ : (∀
    (u1 : Unit) (a : Empty) (u2 : Unit) (b : Empty), (P (ThrowUB u1) a (ThrowUB u2) b False))) {u :
    UBE.I} {a : (UBE.O u)} {u0 : UBE.I} {b : (UBE.O u0)} {P0 : Prop} (_ : (I2FA_UB_graph u a u0 b
    P0)), (P u a u0 b P0)) := by
  intro P h1 e a f b p witness
  cases witness
  next => apply h1

def I2FA_UB_graph_correct :
    (∀ (u : UBE.I) (a : (UBE.O u)) (u0 : UBE.I) (b : (UBE.O u0)), (I2FA_UB_graph u a u0 b (I2FA_UB u
    a u0 b))) := by
  intro e a f b
  cases e <;> cases f <;> first
    | apply I2FA_UB_graph.case1

def I2FA_UB_elim :
    (∀ (P : (∀ (e : UBE.I) (_ : (UBE.O e)) (f : UBE.I) (_ : (UBE.O f)) (_ : Prop), Type u)) (_ : (∀
    (u1 : Unit) (a : Empty) (u2 : Unit) (b : Empty), (P (ThrowUB u1) a (ThrowUB u2) b False))) (u :
    UBE.I) (a : (UBE.O u)) (u0 : UBE.I) (b : (UBE.O u0)), (P u a u0 b (I2FA_UB u a u0 b))) := by
  intro P h1 e a f b
  exact I2FA_UB_graph_rect P h1 (I2FA_UB_graph_correct e a f b)

instance FunctionalInduction_I2FA_UB :
    (FunctionalInduction.{0, 0} I2FA_UB) := ⟨_, I2FA_UB_graph_correct⟩

instance FunctionalElimination_I2FA_UB :
    FunctionalElimination I2FA_UB (∀ (P : (∀ (e : UBE.I) (_ : (UBE.O e)) (f : UBE.I) (_ : (UBE.O f)) (_ : Prop), Type u)) (_ : (∀
    (u1 : Unit) (a : Empty) (u2 : Unit) (b : Empty), (P (ThrowUB u1) a (ThrowUB u2) b False))) (u :
    UBE.I) (a : (UBE.O u)) (u0 : UBE.I) (b : (UBE.O u0)), (P u a u0 b (I2FA_UB u a u0 b))) 2 :=
  ⟨I2FA_UB_elim⟩

theorem I2FA_Debug_equation_1 :
    (∀ (u1 a u2 b : Unit), (Eq (I2FA_Debug (Debug u1) a (Debug u2) b) True)) := by intros; rfl

inductive I2FA_Debug_graph :
    (∀ (e : DebugE.I) (_ : (DebugE.O e)) (f : DebugE.I) (_ : (DebugE.O f)) (_ : Prop), Type) where
  | case1 :
      (∀ (u1 a u2 b : Unit), (I2FA_Debug_graph (Debug u1) a (Debug u2) b True))

abbrev I2FA_Debug_graph_equation_1 := @I2FA_Debug_graph.case1

def I2FA_Debug_graph_rect :
    (∀ (P : (∀ (e : DebugE.I) (_ : (DebugE.O e)) (f : DebugE.I) (_ : (DebugE.O f)) (_ : Prop), Type
    u)) (_ : (∀ (u1 a u2 b : Unit), (P (Debug u1) a (Debug u2) b True))) {d : DebugE.I} {a :
    (DebugE.O d)} {d0 : DebugE.I} {b : (DebugE.O d0)} {P0 : Prop} (_ : (I2FA_Debug_graph d a d0 b
    P0)), (P d a d0 b P0)) := by
  intro P h1 e a f b p witness
  cases witness
  next => apply h1

def I2FA_Debug_graph_correct :
    (∀ (d : DebugE.I) (a : (DebugE.O d)) (d0 : DebugE.I) (b : (DebugE.O d0)), (I2FA_Debug_graph d a
    d0 b (I2FA_Debug d a d0 b))) := by
  intro e a f b
  cases e <;> cases f <;> first
    | apply I2FA_Debug_graph.case1

def I2FA_Debug_elim :
    (∀ (P : (∀ (e : DebugE.I) (_ : (DebugE.O e)) (f : DebugE.I) (_ : (DebugE.O f)) (_ : Prop), Type
    u)) (_ : (∀ (u1 a u2 b : Unit), (P (Debug u1) a (Debug u2) b True))) (d : DebugE.I) (a :
    (DebugE.O d)) (d0 : DebugE.I) (b : (DebugE.O d0)), (P d a d0 b (I2FA_Debug d a d0 b))) := by
  intro P h1 e a f b
  exact I2FA_Debug_graph_rect P h1 (I2FA_Debug_graph_correct e a f b)

instance FunctionalInduction_I2FA_Debug :
    (FunctionalInduction.{0, 0} I2FA_Debug) := ⟨_, I2FA_Debug_graph_correct⟩

instance FunctionalElimination_I2FA_Debug :
    FunctionalElimination I2FA_Debug (∀ (P : (∀ (e : DebugE.I) (_ : (DebugE.O e)) (f : DebugE.I) (_ : (DebugE.O f)) (_ : Prop), Type
    u)) (_ : (∀ (u1 a u2 b : Unit), (P (Debug u1) a (Debug u2) b True))) (d : DebugE.I) (a :
    (DebugE.O d)) (d0 : DebugE.I) (b : (DebugE.O d0)), (P d a d0 b (I2FA_Debug d a d0 b))) 2 :=
  ⟨I2FA_Debug_elim⟩

theorem I2FA_Failure_equation_1 :
    (∀ (u1 : Unit) (a : Empty) (u2 : Unit) (b : Empty), (Eq (I2FA_Failure (Throw u1) a (Throw u2) b)
    False)) := by intros; rfl

inductive I2FA_Failure_graph :
    (∀ (e : FailureE.I) (_ : (FailureE.O e)) (f : FailureE.I) (_ : (FailureE.O f)) (_ : Prop), Type) where
  | case1 :
      (∀ (u1 : Unit) (a : Empty) (u2 : Unit) (b : Empty), (I2FA_Failure_graph (Throw u1) a (Throw
      u2) b False))

abbrev I2FA_Failure_graph_equation_1 := @I2FA_Failure_graph.case1

def I2FA_Failure_graph_rect :
    (∀ (P : (∀ (e : FailureE.I) (_ : (FailureE.O e)) (f : FailureE.I) (_ : (FailureE.O f)) (_ :
    Prop), Type u)) (_ : (∀ (u1 : Unit) (a : Empty) (u2 : Unit) (b : Empty), (P (Throw u1) a (Throw
    u2) b False))) {f : FailureE.I} {a : (FailureE.O f)} {f0 : FailureE.I} {b : (FailureE.O f0)} {P0
    : Prop} (_ : (I2FA_Failure_graph f a f0 b P0)), (P f a f0 b P0)) := by
  intro P h1 e a f b p witness
  cases witness
  next => apply h1

def I2FA_Failure_graph_correct :
    (∀ (f : FailureE.I) (a : (FailureE.O f)) (f0 : FailureE.I) (b : (FailureE.O f0)),
    (I2FA_Failure_graph f a f0 b (I2FA_Failure f a f0 b))) := by
  intro e a f b
  cases e <;> cases f <;> first
    | apply I2FA_Failure_graph.case1

def I2FA_Failure_elim :
    (∀ (P : (∀ (e : FailureE.I) (_ : (FailureE.O e)) (f : FailureE.I) (_ : (FailureE.O f)) (_ :
    Prop), Type u)) (_ : (∀ (u1 : Unit) (a : Empty) (u2 : Unit) (b : Empty), (P (Throw u1) a (Throw
    u2) b False))) (f : FailureE.I) (a : (FailureE.O f)) (f0 : FailureE.I) (b : (FailureE.O f0)), (P
    f a f0 b (I2FA_Failure f a f0 b))) := by
  intro P h1 e a f b
  exact I2FA_Failure_graph_rect P h1 (I2FA_Failure_graph_correct e a f b)

instance FunctionalInduction_I2FA_Failure :
    (FunctionalInduction.{0, 0} I2FA_Failure) := ⟨_, I2FA_Failure_graph_correct⟩

instance FunctionalElimination_I2FA_Failure :
    FunctionalElimination I2FA_Failure (∀ (P : (∀ (e : FailureE.I) (_ : (FailureE.O e)) (f : FailureE.I) (_ : (FailureE.O f)) (_ :
    Prop), Type u)) (_ : (∀ (u1 : Unit) (a : Empty) (u2 : Unit) (b : Empty), (P (Throw u1) a (Throw
    u2) b False))) (f : FailureE.I) (a : (FailureE.O f)) (f0 : FailureE.I) (b : (FailureE.O f0)), (P
    f a f0 b (I2FA_Failure f a f0 b))) 2 :=
  ⟨I2FA_Failure_elim⟩

end Vellvm.Theory.I2F.Refinement
