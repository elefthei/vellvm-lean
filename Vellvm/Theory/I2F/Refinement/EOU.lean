module

public import Vellvm.Semantics.EOU

@[expose] public section
namespace Vellvm.Theory.I2F.Refinement

open Vellvm.Semantics.EOU Vellvm.Utils.ListUtil
open Vellvm.Utils.RelationsUtil (prod_rel)
universe u v w x y z

/-- Left UB and right OOM cut off the comparison, irrespective of the other outcome. -/
inductive I2F_EOU {A : Type u} {B : Type v} (R : A → B → Prop) : EOU A → EOU B → Prop where
  | I2F_EOU_ret (a : A) (b : B) : R a b → I2F_EOU R (raise_ret a) (raise_ret b)
  | I2F_EOU_error (s t : IRString) : I2F_EOU R (raise_error s) (raise_error t)
  | I2F_EOU_ub (s : IRString) (m : EOU B) : I2F_EOU R (raise_ub s) m
  | I2F_EOU_oom (m : EOU A) (s : IRString) : I2F_EOU R m (raise_oom s)

export I2F_EOU (I2F_EOU_ret I2F_EOU_error I2F_EOU_ub I2F_EOU_oom)

inductive MaybePoisonRel {A : Type u} {B : Type v} (R : A → B → Prop) :
    MaybePoison A → MaybePoison B → Prop where
  | MaybePoison_NoPois (a : A) (b : B) : R a b → MaybePoisonRel R (NoPois a) (NoPois b)
  | MaybePoison_Pois : MaybePoisonRel R Pois Pois

export MaybePoisonRel (MaybePoison_NoPois MaybePoison_Pois)

inductive I2F_EOUP {A : Type u} {B : Type v} (R : A → B → Prop) : EOUP A → EOUP B → Prop where
  | I2F_EOUP_ret (a : A) (b : B) : R a b → I2F_EOUP R (raise_ret (NoPois a)) (raise_ret (NoPois b))
  | I2F_EOUP_poison : I2F_EOUP R (raise_ret Pois) (raise_ret Pois)
  | I2F_EOUP_error (s t : IRString) : I2F_EOUP R (raise_error s) (raise_error t)
  | I2F_EOUP_ub (s : IRString) (m : EOUP B) : I2F_EOUP R (raise_ub s) m
  | I2F_EOUP_oom (m : EOUP A) (s : IRString) : I2F_EOUP R m (raise_oom s)

export I2F_EOUP (I2F_EOUP_ret I2F_EOUP_poison I2F_EOUP_error I2F_EOUP_ub I2F_EOUP_oom)

theorem I2F_EOUP_EOU {A : Type u} {B : Type v} {R : A → B → Prop} {m : EOUP A} {n : EOUP B}
    (h : I2F_EOUP R m n) : I2F_EOU (MaybePoisonRel R) m n := by
  cases h with
  | I2F_EOUP_ret a b hr => exact .I2F_EOU_ret _ _ (.MaybePoison_NoPois a b hr)
  | I2F_EOUP_poison => exact .I2F_EOU_ret _ _ .MaybePoison_Pois
  | I2F_EOUP_error s t => exact .I2F_EOU_error s t
  | I2F_EOUP_ub s n => exact .I2F_EOU_ub s n
  | I2F_EOUP_oom m s => exact .I2F_EOU_oom m s

theorem I2F_EOU_refl {A : Type u} (m : EOU A) : I2F_EOU Eq m m := by
  cases m with
  | raise_ret a => exact .I2F_EOU_ret a a rfl
  | raise_error s => exact .I2F_EOU_error s s
  | raise_ub s => exact .I2F_EOU_ub s _
  | raise_oom s => exact .I2F_EOU_oom _ s

theorem I2F_EOU_bind {A₁ : Type u} {A₂ : Type v} {B₁ : Type w} {B₂ : Type x}
    {R : A₁ → A₂ → Prop} {S : B₁ → B₂ → Prop} {m : EOU A₁} {n : EOU A₂}
    (f : A₁ → EOU B₁) (g : A₂ → EOU B₂) (h : I2F_EOU R m n)
    (hk : ∀ a b, R a b → I2F_EOU S (f a) (g b)) : I2F_EOU S (EOU.bind m f) (EOU.bind n g) := by
  cases h with
  | I2F_EOU_ret a b hr => exact hk a b hr
  | I2F_EOU_error s t => exact .I2F_EOU_error s t
  | I2F_EOU_ub s _ => exact .I2F_EOU_ub s _
  | I2F_EOU_oom _ s => exact .I2F_EOU_oom _ s

/-- `catch_pois none` is EOUP bind, also when the continuation changes universe. -/
theorem I2F_EOUP_bind {A₁ : Type u} {A₂ : Type v} {B₁ : Type w} {B₂ : Type x}
    {R : A₁ → A₂ → Prop} {S : B₁ → B₂ → Prop} {m : EOUP A₁} {n : EOUP A₂}
    (f : A₁ → EOUP B₁) (g : A₂ → EOUP B₂) (h : I2F_EOUP R m n)
    (hk : ∀ a b, R a b → I2F_EOUP S (f a) (g b)) :
    I2F_EOUP S (catch_pois none m f) (catch_pois none n g) := by
  cases h with
  | I2F_EOUP_ret a b hr => exact hk a b hr
  | I2F_EOUP_poison => exact .I2F_EOUP_poison
  | I2F_EOUP_error s t => exact .I2F_EOUP_error s t
  | I2F_EOUP_ub s _ => exact .I2F_EOUP_ub s _
  | I2F_EOUP_oom _ s => exact .I2F_EOUP_oom _ s

theorem I2F_EOU_map_monad {A : Type u} {B₁ : Type v} {B₂ : Type w} {R : B₁ → B₂ → Prop}
    (f : A → EOU B₁) (g : A → EOU B₂) (l : List A)
    (hf : ∀ a, a ∈ l → I2F_EOU R (f a) (g a)) :
    I2F_EOU (List.Forall₂ R) (map_monad f l) (map_monad g l) := by
  induction l with
  | nil => exact .I2F_EOU_ret [] [] .nil
  | cons a xs ih =>
    simp only [map_monad]
    refine I2F_EOU_bind _ _ (hf a (by simp)) fun b c hbc ↦ ?_
    refine I2F_EOU_bind _ _ (ih fun x hx ↦ hf x (List.mem_cons_of_mem _ hx)) fun bs cs hbs ↦ ?_
    exact .I2F_EOU_ret _ _ (.cons hbc hbs)

theorem I2F_EOU_vec_loop {A₁ : Type u} {A₂ : Type v} {B₁ : Type w} {B₂ : Type x}
    {C₁ : Type y} {C₂ : Type z} {P : A₁ → A₂ → Prop} {Q : B₁ → B₂ → Prop} {R : C₁ → C₂ → Prop}
    (f : A₁ → B₁ → EOU C₁) (g : A₂ → B₂ → EOU C₂) {l₁ l₂} (hl : List.Forall₂ (prod_rel P Q) l₁ l₂)
    (hf : ∀ a b a' b', P a a' → Q b b' → I2F_EOU R (f a b) (g a' b')) :
    I2F_EOU (List.Forall₂ R) (vec_loop f l₁) (vec_loop g l₂) := by
  induction hl with
  | nil => exact .I2F_EOU_ret [] [] .nil
  | @cons ab cd xs ys hab _ ih =>
    refine I2F_EOU_bind (fun bs ↦ f ab.1 ab.2 >>= fun b ↦ pure (b :: bs))
      (fun cs ↦ g cd.1 cd.2 >>= fun c ↦ pure (c :: cs)) ih fun bs cs hbs ↦ ?_
    refine I2F_EOU_bind _ _ (hf _ _ _ _ hab.1 hab.2) fun b c hbc ↦ ?_
    exact .I2F_EOU_ret _ _ (.cons hbc hbs)

theorem I2F_EOU_map_monad2 {A₁ : Type u} {A₂ : Type v} {B₁ : Type w} {B₂ : Type x}
    {R : A₁ → A₂ → Prop} {S : B₁ → B₂ → Prop} (f : A₁ → EOU B₁) (g : A₂ → EOU B₂)
    {l₁ l₂} (hl : List.Forall₂ R l₁ l₂) (hf : ∀ a b, R a b → I2F_EOU S (f a) (g b)) :
    I2F_EOU (List.Forall₂ S) (map_monad f l₁) (map_monad g l₂) := by
  induction hl with
  | nil => exact .I2F_EOU_ret [] [] .nil
  | cons h _ ih =>
    simp only [map_monad]
    refine I2F_EOU_bind _ _ (hf _ _ h) fun b c hbc ↦ ?_
    refine I2F_EOU_bind _ _ ih fun bs cs hbs ↦ ?_
    exact .I2F_EOU_ret _ _ (.cons hbc hbs)

theorem I2F_EOUP_map_monad2 {A₁ : Type u} {A₂ : Type v} {B₁ : Type w} {B₂ : Type x}
    {R : A₁ → A₂ → Prop} {S : B₁ → B₂ → Prop} (f : A₁ → EOUP B₁) (g : A₂ → EOUP B₂)
    {l₁ l₂} (hl : List.Forall₂ R l₁ l₂) (hf : ∀ a b, R a b → I2F_EOUP S (f a) (g b)) :
    I2F_EOUP (List.Forall₂ S) (map_monad (m := EOUP) f l₁) (map_monad (m := EOUP) g l₂) := by
  induction hl with
  | nil => exact .I2F_EOUP_ret [] [] .nil
  | @cons a b xs ys h _ ih =>
    refine I2F_EOUP_bind (fun c ↦ map_monad (m := EOUP) f xs >>= fun cs ↦ pure (c :: cs))
      (fun d ↦ map_monad (m := EOUP) g ys >>= fun ds ↦ pure (d :: ds)) (hf a b h) fun c d hcd ↦ ?_
    exact I2F_EOUP_bind (fun cs ↦ pure (c :: cs)) (fun ds ↦ pure (d :: ds)) ih
      fun cs ds hcs ↦ .I2F_EOUP_ret _ _ (.cons hcd hcs)

theorem I2F_EOU_mono {A : Type u} {B : Type v} {R : A → B → Prop} (S : A → B → Prop)
    {m : EOU A} {n : EOU B} (hs : ∀ a b, R a b → S a b) (h : I2F_EOU R m n) : I2F_EOU S m n := by
  cases h with
  | I2F_EOU_ret a b hr => exact .I2F_EOU_ret a b (hs a b hr)
  | I2F_EOU_error s t => exact .I2F_EOU_error s t
  | I2F_EOU_ub s n => exact .I2F_EOU_ub s n
  | I2F_EOU_oom m s => exact .I2F_EOU_oom m s

theorem I2F_EOU_map_monad_acc2 {A₁ : Type u} {A₂ : Type v} {B₁ : Type w} {B₂ : Type x}
    {R : A₁ → A₂ → Prop} {S : B₁ → B₂ → Prop} (f : A₁ → EOU B₁) (g : A₂ → EOU B₂)
    {l₁ l₂} (hl : List.Forall₂ R l₁ l₂) (hf : ∀ a b, R a b → I2F_EOU S (f a) (g b)) :
    I2F_EOU (List.Forall₂ S) (map_monad_acc f l₁) (map_monad_acc g l₂) := by
  suffices ∀ acc₁ acc₂, List.Forall₂ S acc₁ acc₂ → I2F_EOU (List.Forall₂ S)
      (map_monad_acc.go f acc₁ l₁) (map_monad_acc.go g acc₂ l₂) from this [] [] .nil
  induction hl with
  | nil =>
    intro acc₁ acc₂ ha
    exact .I2F_EOU_ret _ _ (Forall2_rev_append S _ _ ha [] [] .nil)
  | cons h _ ih =>
    intro acc₁ acc₂ ha
    simp only [map_monad_acc.go]
    refine I2F_EOU_bind _ _ (hf _ _ h) fun b c hbc ↦ ?_
    exact ih (b :: acc₁) (c :: acc₂) (.cons hbc ha)

end Vellvm.Theory.I2F.Refinement
