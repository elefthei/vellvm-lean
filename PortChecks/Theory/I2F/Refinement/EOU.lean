import PortChecks.SourceType
import Vellvm.Theory.I2F.Refinement.EOU

open Vellvm Vellvm.Semantics.EOU Vellvm.Theory.I2F.Refinement Vellvm.Utils.ListUtil
open Vellvm.Utils.RelationsUtil (prod_rel)
universe u v w x y z

#source_check "src/rocq/Theory/I2F/Refinement.v|Vellvm.Theory.I2F.Refinement|I2F_EOU"
  I2F_EOU : ∀ {A : Type u} {B : Type v}, (A → B → Prop) → EOU A → EOU B → Prop

#source_check "src/rocq/Theory/I2F/Refinement.v|Vellvm.Theory.I2F.Refinement|I2F_EOU_ret"
  I2F_EOU_ret : ∀ {A : Type u} {B : Type v} {R : A → B → Prop} (a : A) (b : B),
    R a b → I2F_EOU R (raise_ret a) (raise_ret b)

#source_check "src/rocq/Theory/I2F/Refinement.v|Vellvm.Theory.I2F.Refinement|I2F_EOU_error"
  I2F_EOU_error : ∀ {A : Type u} {B : Type v} {R : A → B → Prop} (s t : IRString),
    I2F_EOU R (raise_error s) (raise_error t)

#source_check "src/rocq/Theory/I2F/Refinement.v|Vellvm.Theory.I2F.Refinement|I2F_EOU_ub"
  I2F_EOU_ub : ∀ {A : Type u} {B : Type v} {R : A → B → Prop} (s : IRString) (m : EOU B),
    I2F_EOU R (raise_ub s) m

#source_check "src/rocq/Theory/I2F/Refinement.v|Vellvm.Theory.I2F.Refinement|I2F_EOU_oom"
  I2F_EOU_oom : ∀ {A : Type u} {B : Type v} {R : A → B → Prop} (m : EOU A) (s : IRString),
    I2F_EOU R m (raise_oom s)

#source_check "src/rocq/Theory/I2F/Refinement.v|Vellvm.Theory.I2F.Refinement|MaybePoisonRel"
  MaybePoisonRel : ∀ {A : Type u} {B : Type v}, (A → B → Prop) → Option A → Option B → Prop

#source_check "src/rocq/Theory/I2F/Refinement.v|Vellvm.Theory.I2F.Refinement|MaybePoison_NoPois"
  MaybePoison_NoPois : ∀ {A : Type u} {B : Type v} {R : A → B → Prop} (a : A) (b : B),
    R a b → MaybePoisonRel R (some a) (some b)

#source_check "src/rocq/Theory/I2F/Refinement.v|Vellvm.Theory.I2F.Refinement|MaybePoison_Pois"
  MaybePoison_Pois : ∀ {A : Type u} {B : Type v} {R : A → B → Prop}, MaybePoisonRel R none none

#source_check "src/rocq/Theory/I2F/Refinement.v|Vellvm.Theory.I2F.Refinement|I2F_EOUP"
  I2F_EOUP : ∀ {A : Type u} {B : Type v}, (A → B → Prop) → EOUP A → EOUP B → Prop

#source_check "src/rocq/Theory/I2F/Refinement.v|Vellvm.Theory.I2F.Refinement|I2F_EOUP_ret"
  I2F_EOUP_ret : ∀ {A : Type u} {B : Type v} {R : A → B → Prop} (a : A) (b : B),
    R a b → I2F_EOUP R (raise_ret (some a)) (raise_ret (some b))

#source_check "src/rocq/Theory/I2F/Refinement.v|Vellvm.Theory.I2F.Refinement|I2F_EOUP_poison"
  I2F_EOUP_poison : ∀ {A : Type u} {B : Type v} {R : A → B → Prop},
    I2F_EOUP R (raise_ret none) (raise_ret none)

#source_check "src/rocq/Theory/I2F/Refinement.v|Vellvm.Theory.I2F.Refinement|I2F_EOUP_error"
  I2F_EOUP_error : ∀ {A : Type u} {B : Type v} {R : A → B → Prop} (s t : IRString),
    I2F_EOUP R (raise_error s) (raise_error t)

#source_check "src/rocq/Theory/I2F/Refinement.v|Vellvm.Theory.I2F.Refinement|I2F_EOUP_ub"
  I2F_EOUP_ub : ∀ {A : Type u} {B : Type v} {R : A → B → Prop} (s : IRString) (m : EOUP B),
    I2F_EOUP R (raise_ub s) m

#source_check "src/rocq/Theory/I2F/Refinement.v|Vellvm.Theory.I2F.Refinement|I2F_EOUP_oom"
  I2F_EOUP_oom : ∀ {A : Type u} {B : Type v} {R : A → B → Prop} (m : EOUP A) (s : IRString),
    I2F_EOUP R m (raise_oom s)

#source_check "src/rocq/Theory/I2F/Refinement.v|Vellvm.Theory.I2F.Refinement|I2F_EOUP_EOU"
  I2F_EOUP_EOU : ∀ {A : Type u} {B : Type v} {R : A → B → Prop} {p : EOUP A} {q : EOUP B},
    I2F_EOUP R p q → I2F_EOU (MaybePoisonRel R) p q

#source_check "src/rocq/Theory/I2F/Refinement.v|Vellvm.Theory.I2F.Refinement|I2F_EOU_refl"
  I2F_EOU_refl : ∀ {A : Type u} (m : EOU A), I2F_EOU Eq m m

#source_check "src/rocq/Theory/I2F/Refinement.v|Vellvm.Theory.I2F.Refinement|I2F_EOU_bind"
  I2F_EOU_bind : ∀ {A : Type u} {B : Type v} {C : Type w} {D : Type x}
    {R : A → B → Prop} {S : C → D → Prop} {p : EOU A} {q : EOU B}
    (f : A → EOU C) (g : B → EOU D), I2F_EOU R p q →
    (∀ a b, R a b → I2F_EOU S (f a) (g b)) → I2F_EOU S (EOU.bind p f) (EOU.bind q g)

#source_check "src/rocq/Theory/I2F/Refinement.v|Vellvm.Theory.I2F.Refinement|I2F_EOUP_bind"
  I2F_EOUP_bind : ∀ {A : Type u} {B : Type v} {C : Type w} {D : Type x}
    {R : A → B → Prop} {S : C → D → Prop} {p : EOUP A} {q : EOUP B}
    (f : A → EOUP C) (g : B → EOUP D), I2F_EOUP R p q →
    (∀ a b, R a b → I2F_EOUP S (f a) (g b)) →
    I2F_EOUP S (catch_pois none p f) (catch_pois none q g)

#source_check "src/rocq/Theory/I2F/Refinement.v|Vellvm.Theory.I2F.Refinement|I2F_EOU_map_monad"
  I2F_EOU_map_monad : ∀ {A : Type u} {B : Type v} {C : Type w} {R : B → C → Prop}
    (f : A → EOU B) (g : A → EOU C) (xs : List A),
    (∀ a, a ∈ xs → I2F_EOU R (f a) (g a)) →
    I2F_EOU (List.Forall₂ R) (map_monad f xs) (map_monad g xs)

#source_check "src/rocq/Theory/I2F/Refinement.v|Vellvm.Theory.I2F.Refinement|I2F_EOU_vec_loop"
  I2F_EOU_vec_loop : ∀ {A : Type u} {A' : Type v} {B : Type w} {B' : Type x}
    {C : Type y} {C' : Type z} {P : A → A' → Prop} {Q : B → B' → Prop} {R : C → C' → Prop}
    (f : A → B → EOU C) (g : A' → B' → EOU C') {xs ys}, List.Forall₂ (prod_rel P Q) xs ys →
    (∀ a b a' b', P a a' → Q b b' → I2F_EOU R (f a b) (g a' b')) →
    I2F_EOU (List.Forall₂ R) (vec_loop f xs) (vec_loop g ys)

#source_check "src/rocq/Theory/I2F/Refinement.v|Vellvm.Theory.I2F.Refinement|I2F_EOU_map_monad2"
  I2F_EOU_map_monad2 : ∀ {A : Type u} {B : Type v} {C : Type w} {D : Type x}
    {P : A → B → Prop} {Q : C → D → Prop} (f : A → EOU C) (g : B → EOU D) {xs ys},
    List.Forall₂ P xs ys → (∀ a b, P a b → I2F_EOU Q (f a) (g b)) →
    I2F_EOU (List.Forall₂ Q) (map_monad f xs) (map_monad g ys)

#source_check "src/rocq/Theory/I2F/Refinement.v|Vellvm.Theory.I2F.Refinement|I2F_EOUP_map_monad2"
  I2F_EOUP_map_monad2 : ∀ {A : Type u} {B : Type v} {C : Type w} {D : Type x}
    {P : A → B → Prop} {Q : C → D → Prop} (f : A → EOUP C) (g : B → EOUP D) {xs ys},
    List.Forall₂ P xs ys → (∀ a b, P a b → I2F_EOUP Q (f a) (g b)) →
    I2F_EOUP (List.Forall₂ Q) (map_monad (m := EOUP) f xs) (map_monad (m := EOUP) g ys)

#source_check "src/rocq/Theory/I2F/Refinement.v|Vellvm.Theory.I2F.Refinement|I2F_EOU_mono"
  I2F_EOU_mono : ∀ {A : Type u} {B : Type v} {R : A → B → Prop} (S : A → B → Prop)
    {m : EOU A} {n : EOU B}, (∀ a b, R a b → S a b) → I2F_EOU R m n → I2F_EOU S m n

#source_check "src/rocq/Theory/I2F/Refinement.v|Vellvm.Theory.I2F.Refinement|I2F_EOU_map_monad_acc2"
  I2F_EOU_map_monad_acc2 : ∀ {A : Type u} {B : Type v} {C : Type w} {D : Type x}
    {P : A → B → Prop} {Q : C → D → Prop} (f : A → EOU C) (g : B → EOU D) {xs ys},
    List.Forall₂ P xs ys → (∀ a b, P a b → I2F_EOU Q (f a) (g b)) →
    I2F_EOU (List.Forall₂ Q) (map_monad_acc f xs) (map_monad_acc g ys)
