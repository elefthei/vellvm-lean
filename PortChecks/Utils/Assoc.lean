import PortChecks.SourceType
import Vellvm.Utils.Assoc

open Vellvm.Utils.Assoc
universe u v

#source_check "src/rocq/Utils/Assoc.v|Vellvm.Utils.Assoc|eq_dec_eq"
  eq_dec_eq : ∀ {A : Type u} [BEq A] [LawfulBEq A] (a : A), (a == a) = true

#source_check "src/rocq/Utils/Assoc.v|Vellvm.Utils.Assoc|eq_dec_neq"
  eq_dec_neq : ∀ {A : Type u} [BEq A] [LawfulBEq A] (a b : A), a ≠ b → (a == b) = false

#source_check "src/rocq/Utils/Assoc.v|Vellvm.Utils.Assoc|assoc_hd"
  assoc_hd : ∀ {A : Type u} {B : Type v} [BEq A] [LawfulBEq A]
    (a : A) (b : B) (tl : List (A × B)), assoc a ((a, b) :: tl) = some b

#source_check "src/rocq/Utils/Assoc.v|Vellvm.Utils.Assoc|assoc_tl"
  assoc_tl : ∀ {A : Type u} {B : Type v} [BEq A] [LawfulBEq A]
    (a c : A) (b : B) (l : List (A × B)), a ≠ c → assoc a ((c, b) :: l) = assoc a l
