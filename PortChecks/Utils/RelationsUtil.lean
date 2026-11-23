import PortChecks.SourceType
import Vellvm.Utils.RelationsUtil

open Relation Vellvm.Utils.RelationsUtil
universe u

#source_check "src/rocq/Utils/RelationsUtil.v|Vellvm.Utils.RelationsUtil|clos_t_rt"
  clos_t_rt : ∀ {A : Type u} {R : A → A → Prop} {x y : A},
    TransGen R x y → ReflTransGen R x y

#source_check "src/rocq/Utils/RelationsUtil.v|Vellvm.Utils.RelationsUtil|clos_t_rt_inv"
  clos_t_rt_inv : ∀ {A : Type u} {R : A → A → Prop} {x y : A},
    TransGen R x y → ∃ z, R z y ∧ ReflTransGen R x z

#source_check "src/rocq/Utils/RelationsUtil.v|Vellvm.Utils.RelationsUtil|clos_rt_t_inv"
  clos_rt_t_inv : ∀ {A : Type u} {R : A → A → Prop} {x y : A},
    ReflTransGen R x y → x = y ∨ R x y ∨ TransGen R x y

#source_check "src/rocq/Utils/RelationsUtil.v|Vellvm.Utils.RelationsUtil|clos_rt_inv"
  clos_rt_inv : ∀ {A : Type u} {R : A → A → Prop} {x y : A},
    ReflTransGen R x y → x = y ∨ ∃ z, R z y ∧ ReflTransGen R x z

#source_check "src/rocq/Utils/RelationsUtil.v|Vellvm.Utils.RelationsUtil|clos_trans_measure"
  clos_trans_measure : ∀ {A : Type u} {R : A → A → Prop} (m : A → Nat),
    (∀ a b, R a b → m a < m b) → ∀ a b, TransGen R a b → m a < m b

#source_check "src/rocq/Utils/RelationsUtil.v|Vellvm.Utils.RelationsUtil|clos_trans_not_sym"
  clos_trans_not_sym : ∀ {A : Type u} {R : A → A → Prop} (m : A → Nat),
    (∀ a b, R a b → m a < m b) → ∀ a b, TransGen R a b → ¬ TransGen R b a

#source_check "src/rocq/Utils/RelationsUtil.v|Vellvm.Utils.RelationsUtil|clos_refl_trans_antisymmetric"
  clos_refl_trans_antisymmetric : ∀ {A : Type u} {R : A → A → Prop} (m : A → Nat),
    (∀ a b, R a b → m a < m b) → ∀ a b, ReflTransGen R a b → ReflTransGen R b a → a = b
