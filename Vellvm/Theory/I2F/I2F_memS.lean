module

public import Vellvm.Semantics.Interfaces.Memory
public import Vellvm.Theory.I2F.Refinement.EOU

@[expose] public section
namespace Vellvm.Theory.I2F.I2F_memS
open Semantics.Interfaces.Memory Semantics.EOU Utils.ListUtil Refinement
universe u v w x y z p q

variable {S1 : Type u} {S2 : Type v} {A1 : Type w} {A2 : Type x} {P : Type}
  {X1 : Type y} {X2 : Type z} {Y1 : Type p} {Y2 : Type q}

/-- A finite simulation of memory syntax. Choices match at every raw answer; only a left UB
or a right OOM allows the other computation to be ignored. -/
inductive I2F_memS (RS : S1 → S2 → Prop) (RR : X1 → X2 → Prop) :
    memS S1 A1 P X1 → memS S2 A2 P X2 → Prop where
  | I2F_Mret (x1 x2) : RR x1 x2 → I2F_memS RS RR (Mret x1) (Mret x2)
  | I2F_Merr (s1 s2) : I2F_memS RS RR (Merr s1) (Merr s2)
  | I2F_Mub_l (s m2) : I2F_memS RS RR (Mub s) m2
  | I2F_Moom_r (m1 s) : I2F_memS RS RR m1 (Moom s)
  | I2F_Mget (k1 k2) : (∀ s1 s2, RS s1 s2 → I2F_memS RS RR (k1 s1) (k2 s2)) →
      I2F_memS RS RR (Mget k1) (Mget k2)
  | I2F_Mput (s1 s2 k1 k2) : RS s1 s2 → I2F_memS RS RR (k1 ()) (k2 ()) →
      I2F_memS RS RR (Mput s1 k1) (Mput s2 k2)
  | I2F_Mchoose (c k1 k2) : (∀ a, I2F_memS RS RR (k1 a) (k2 a)) →
      I2F_memS RS RR (Mchoose c k1) (Mchoose c k2)

export I2F_memS (I2F_Mret I2F_Merr I2F_Mub_l I2F_Moom_r I2F_Mget I2F_Mput I2F_Mchoose)

@[elab_as_elim] theorem I2F_memS_ind {RS : S1 → S2 → Prop} {RR : X1 → X2 → Prop}
    (Q : memS S1 A1 P X1 → memS S2 A2 P X2 → Prop)
    (ret : ∀ a b, RR a b → Q (Mret a) (Mret b)) (err : ∀ s t, Q (Merr s) (Merr t))
    (ub : ∀ s m, Q (Mub s) m) (oom : ∀ m s, Q m (Moom s))
    (get : ∀ k l, (∀ a b, RS a b → I2F_memS RS RR (k a) (l b)) →
      (∀ a b, RS a b → Q (k a) (l b)) → Q (Mget k) (Mget l))
    (put : ∀ a b k l, RS a b → I2F_memS RS RR (k ()) (l ()) → Q (k ()) (l ()) →
      Q (Mput a k) (Mput b l))
    (choose : ∀ c k l, (∀ a, I2F_memS RS RR (k a) (l a)) → (∀ a, Q (k a) (l a)) →
      Q (Mchoose c k) (Mchoose c l)) {m n} (h : I2F_memS RS RR m n) : Q m n := by
  induction h <;> solve | apply_assumption <;> assumption

@[elab_as_elim] alias I2F_memS_sind := I2F_memS_ind

theorem I2F_memS_mono (RS : S1 → S2 → Prop) (RR RR' : X1 → X2 → Prop)
    (m1 : memS S1 A1 P X1) (m2 : memS S2 A2 P X2) (sub : ∀ a b, RR a b → RR' a b)
    (h : I2F_memS RS RR m1 m2) : I2F_memS RS RR' m1 m2 := by
  induction h with
  | I2F_Mret a b hab => exact .I2F_Mret a b (sub a b hab)
  | I2F_Merr s t => exact .I2F_Merr s t
  | I2F_Mub_l s m => exact .I2F_Mub_l s m
  | I2F_Moom_r m s => exact .I2F_Moom_r m s
  | I2F_Mget k l _ ih => exact .I2F_Mget k l ih
  | I2F_Mput a b k l hab _ ih => exact .I2F_Mput a b k l hab ih
  | I2F_Mchoose c k l _ ih => exact .I2F_Mchoose c k l ih

theorem I2F_memS_lift (RS : S1 → S2 → Prop) (RR : X1 → X2 → Prop) (m1 : EOU X1) (m2 : EOU X2)
    (h : I2F_EOU RR m1 m2) : I2F_memS (A1 := A1) (A2 := A2) (P := P) RS RR (lift m1) (lift m2) := by
  cases h with
  | I2F_EOU_ret a b h => exact .I2F_Mret a b h
  | I2F_EOU_error s t => exact .I2F_Merr s t
  | I2F_EOU_ub s m => exact .I2F_Mub_l s _
  | I2F_EOU_oom m s => exact .I2F_Moom_r _ s

theorem I2F_memS_bind (RS : S1 → S2 → Prop) (RX : X1 → X2 → Prop) (RY : Y1 → Y2 → Prop)
    (m1 : memS S1 A1 P X1) (m2 : memS S2 A2 P X2)
    (k1 : X1 → memS S1 A1 P Y1) (k2 : X2 → memS S2 A2 P Y2)
    (h : I2F_memS RS RX m1 m2) (hk : ∀ a b, RX a b → I2F_memS RS RY (k1 a) (k2 b)) :
    I2F_memS RS RY (memS_bind m1 k1) (memS_bind m2 k2) := by
  induction h with
  | I2F_Mret a b hab => exact hk a b hab
  | I2F_Merr s t => exact .I2F_Merr s t
  | I2F_Mub_l s _ => exact .I2F_Mub_l s _
  | I2F_Moom_r _ s => exact .I2F_Moom_r _ s
  | I2F_Mget _ _ _ ih => exact .I2F_Mget _ _ ih
  | I2F_Mput a b _ _ hab _ ih => exact .I2F_Mput a b _ _ hab ih
  | I2F_Mchoose c _ _ _ ih => exact .I2F_Mchoose c _ _ ih

theorem I2F_memS_get (RS : S1 → S2 → Prop) :
    I2F_memS (A1 := A1) (A2 := A2) (P := P) RS RS Semantics.Interfaces.Memory.get Semantics.Interfaces.Memory.get :=
  .I2F_Mget _ _ fun a b h ↦ .I2F_Mret a b h

theorem I2F_memS_put (RS : S1 → S2 → Prop) (s1 : S1) (s2 : S2) (h : RS s1 s2) :
    I2F_memS (A1 := A1) (A2 := A2) (P := P) RS (fun _ _ ↦ True) (put s1) (put s2) :=
  .I2F_Mput s1 s2 _ _ h (.I2F_Mret () () trivial)

theorem I2F_memS_next_key (RS : S1 → S2 → Prop) (size align : Nat) :
    I2F_memS (A1 := A1) (A2 := A2) (P := P) RS Eq (next_key size align) (next_key size align) :=
  .I2F_Mchoose _ _ _ fun a ↦ .I2F_Mret a a rfl

theorem I2F_memS_fresh_prov (RS : S1 → S2 → Prop) :
    I2F_memS (A1 := A1) (A2 := A2) (P := P) RS Eq (fresh_prov ()) (fresh_prov ()) :=
  .I2F_Mchoose _ _ _ fun a ↦ .I2F_Mret a a rfl

theorem I2F_memS_exposed_prov (RS : S1 → S2 → Prop) :
    I2F_memS (A1 := A1) (A2 := A2) (P := P) RS Eq (exposed_prov ()) (exposed_prov ()) :=
  .I2F_Mchoose _ _ _ fun a ↦ .I2F_Mret a a rfl

theorem I2F_memS_map_monad2 (RS : S1 → S2 → Prop) (RX : X1 → X2 → Prop) (RY : Y1 → Y2 → Prop)
    (f1 : X1 → memS S1 A1 P Y1) (f2 : X2 → memS S2 A2 P Y2) :
    ∀ l1 l2, List.Forall₂ RX l1 l2 → (∀ a b, RX a b → I2F_memS RS RY (f1 a) (f2 b)) →
      I2F_memS RS (List.Forall₂ RY) (map_monad f1 l1) (map_monad f2 l2) := by
  intro l1 l2 h hf
  induction h with
  | nil => exact .I2F_Mret [] [] .nil
  | @cons a b _ _ hab _ ih =>
    exact I2F_memS_bind RS RY _ _ _ _ _ (hf a b hab) fun y z hy ↦
      I2F_memS_bind RS _ _ _ _ _ _ ih fun ys zs hys ↦ .I2F_Mret _ _ (.cons hy hys)

theorem I2F_memS_map_monad_acc2 (RS : S1 → S2 → Prop) (RX : X1 → X2 → Prop) (RY : Y1 → Y2 → Prop)
    (f1 : X1 → memS S1 A1 P Y1) (f2 : X2 → memS S2 A2 P Y2) :
    ∀ l1 l2, List.Forall₂ RX l1 l2 → (∀ a b, RX a b → I2F_memS RS RY (f1 a) (f2 b)) →
      I2F_memS RS (List.Forall₂ RY) (map_monad_acc f1 l1) (map_monad_acc f2 l2) := by
  intro l1 l2 h hf
  suffices go : ∀ acc1 acc2, List.Forall₂ RY acc1 acc2 → I2F_memS RS (List.Forall₂ RY)
      (map_monad_acc.go f1 acc1 l1) (map_monad_acc.go f2 acc2 l2) from go [] [] .nil
  induction h with
  | nil => intro _ _ h; exact .I2F_Mret _ _ (List.forall₂_reverse_iff.mpr h)
  | @cons a b _ _ hab _ ih =>
    intro acc1 acc2 hacc
    exact I2F_memS_bind RS RY _ _ _ _ _ (hf a b hab) fun y z hy ↦ ih _ _ (.cons hy hacc)

theorem I2F_memS_loop_monad2 (RS : S1 → S2 → Prop) (RX : X1 → X2 → Prop)
    (f1 : X1 → memS S1 A1 P Unit) (f2 : X2 → memS S2 A2 P Unit) :
    ∀ l1 l2, List.Forall₂ RX l1 l2 → (∀ a b, RX a b → I2F_memS RS (fun _ _ ↦ True) (f1 a) (f2 b)) →
      I2F_memS RS (fun (_ _ : Unit) ↦ True) (loop_monad f1 l1) (loop_monad f2 l2) := by
  intro l1 l2 h hf
  induction h with
  | nil => exact .I2F_Mret () () trivial
  | @cons a b _ _ hab _ ih =>
    exact I2F_memS_bind RS _ _ _ _ _ _ (hf a b hab) fun _ _ _ ↦ ih

end Vellvm.Theory.I2F.I2F_memS
