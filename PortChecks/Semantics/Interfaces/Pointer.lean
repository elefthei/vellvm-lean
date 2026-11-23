import PortChecks.SourceType
import Vellvm.Semantics.Interfaces.Pointer

open Vellvm Vellvm.Numeric.Rocqlib Vellvm.Syntax.DynamicTypes Vellvm.Semantics.EOU
open Vellvm.Semantics.Interfaces.Provenance Vellvm.Semantics.Interfaces.Pointer
open Vellvm.Semantics.Interfaces.Sizeof

#source_check "src/rocq/Semantics/Interfaces/Pointer.v|Vellvm.Semantics.Interfaces.Pointer|Pointer"
  Pointer : ∀ [P : Provenance], Type 1
#source_check "src/rocq/Semantics/Interfaces/Pointer.v|Vellvm.Semantics.Interfaces.Pointer|Build_Pointer"
  Build_Pointer : ∀ [P : Provenance] (Addr : Type), Addr → EqDecision Addr →
    (Addr → P.prov) → (Addr → IRString) → @Pointer P
#source_check "src/rocq/Semantics/Interfaces/Pointer.v|Vellvm.Semantics.Interfaces.Pointer|ptr"
  ptr : ∀ [P : Provenance] [A : @Pointer P], Type
#source_check "src/rocq/Semantics/Interfaces/Pointer.v|Vellvm.Semantics.Interfaces.Pointer|null"
  null : ∀ [P : Provenance] [A : @Pointer P], A.ptr
#source_check "src/rocq/Semantics/Interfaces/Pointer.v|Vellvm.Semantics.Interfaces.Pointer|eq_dec_ptr"
  eq_dec_ptr : ∀ [P : Provenance] [A : @Pointer P], EqDecision A.ptr
#source_check "src/rocq/Semantics/Interfaces/Pointer.v|Vellvm.Semantics.Interfaces.Pointer|ptr_provenance"
  ptr_provenance : ∀ [P : Provenance] [A : @Pointer P], A.ptr → P.prov
#source_check "src/rocq/Semantics/Interfaces/Pointer.v|Vellvm.Semantics.Interfaces.Pointer|show_ptr"
  show_ptr : ∀ [P : Provenance] [A : @Pointer P], A.ptr → IRString
#source_check "src/rocq/Semantics/Interfaces/Pointer.v|Vellvm.Semantics.Interfaces.Pointer|Overlaps"
  Overlaps : ∀ [P : Provenance] [A : @Pointer P], Type
#source_check "src/rocq/Semantics/Interfaces/Pointer.v|Vellvm.Semantics.Interfaces.Pointer|Build_Overlaps"
  Build_Overlaps : ∀ [P : Provenance] [A : @Pointer P],
    (A.ptr → Nat → A.ptr → Nat → Bool) → @Overlaps P A
#source_check "src/rocq/Semantics/Interfaces/Pointer.v|Vellvm.Semantics.Interfaces.Pointer|overlaps"
  overlaps : ∀ [P : Provenance] [A : @Pointer P] [@Overlaps P A], A.ptr → Nat → A.ptr → Nat → Bool
#source_check "src/rocq/Semantics/Interfaces/Pointer.v|Vellvm.Semantics.Interfaces.Pointer|PI"
  PI : ∀ [P : Provenance] [A : @Pointer P], Type
#source_check "src/rocq/Semantics/Interfaces/Pointer.v|Vellvm.Semantics.Interfaces.Pointer|Build_PI"
  Build_PI : ∀ [P : Provenance] [A : @Pointer P], (A.ptr → Int) →
    (Int → P.prov → EOU A.ptr) → @PI P A
#source_check "src/rocq/Semantics/Interfaces/Pointer.v|Vellvm.Semantics.Interfaces.Pointer|ptr_to_int"
  ptr_to_int : ∀ [P : Provenance] [A : @Pointer P] [@PI P A], A.ptr → Int
#source_check "src/rocq/Semantics/Interfaces/Pointer.v|Vellvm.Semantics.Interfaces.Pointer|int_to_ptr"
  int_to_ptr : ∀ [P : Provenance] [A : @Pointer P] [@PI P A], Int → P.prov → EOU A.ptr
#source_check "src/rocq/Semantics/Interfaces/Pointer.v|Vellvm.Semantics.Interfaces.Pointer|PITheory"
  PITheory : ∀ [P : Provenance] [A : @Pointer P] [C : @PI P A], Prop
#source_check "src/rocq/Semantics/Interfaces/Pointer.v|Vellvm.Semantics.Interfaces.Pointer|Build_PITheory"
  Build_PITheory : ∀ [P : Provenance] [A : @Pointer P] [C : @PI P A],
    (∀ x p {a}, C.int_to_ptr x p = raise_ret a → A.ptr_provenance a = p) →
    (∀ a {p}, A.ptr_provenance a = p → C.int_to_ptr (C.ptr_to_int a) p = raise_ret a) →
    (∀ a p, ∃ a', C.int_to_ptr (C.ptr_to_int a) p = raise_ret a' ∧
      C.ptr_to_int a' = C.ptr_to_int a ∧ A.ptr_provenance a' = p) →
    (∀ x p {a}, C.int_to_ptr x p = raise_ret a → C.ptr_to_int a = x) → @PITheory P A C
#source_check "src/rocq/Semantics/Interfaces/Pointer.v|Vellvm.Semantics.Interfaces.Pointer|int_to_ptr_provenance"
  int_to_ptr_provenance : ∀ [P : Provenance] [A : @Pointer P] [C : @PI P A] [@PITheory P A C]
    x p {a}, C.int_to_ptr x p = raise_ret a → A.ptr_provenance a = p
#source_check "src/rocq/Semantics/Interfaces/Pointer.v|Vellvm.Semantics.Interfaces.Pointer|int_to_ptr_ptr_to_int"
  int_to_ptr_ptr_to_int : ∀ [P : Provenance] [A : @Pointer P] [C : @PI P A] [@PITheory P A C]
    a {p}, A.ptr_provenance a = p → C.int_to_ptr (C.ptr_to_int a) p = raise_ret a
#source_check "src/rocq/Semantics/Interfaces/Pointer.v|Vellvm.Semantics.Interfaces.Pointer|int_to_ptr_ptr_to_int_exists"
  int_to_ptr_ptr_to_int_exists : ∀ [P : Provenance] [A : @Pointer P] [C : @PI P A] [@PITheory P A C]
    a p, ∃ a', C.int_to_ptr (C.ptr_to_int a) p = raise_ret a' ∧
      C.ptr_to_int a' = C.ptr_to_int a ∧ A.ptr_provenance a' = p
#source_check "src/rocq/Semantics/Interfaces/Pointer.v|Vellvm.Semantics.Interfaces.Pointer|ptr_to_int_int_to_ptr"
  ptr_to_int_int_to_ptr : ∀ [P : Provenance] [A : @Pointer P] [C : @PI P A] [@PITheory P A C]
    x p {a}, C.int_to_ptr x p = raise_ret a → C.ptr_to_int a = x
#source_check "src/rocq/Semantics/Interfaces/Pointer.v|Vellvm.Semantics.Interfaces.Pointer|overlaps_ptoi"
  overlaps_ptoi : ∀ [P : Provenance] [A : @Pointer P] [@PI P A], @Overlaps P A
#source_check "src/rocq/Semantics/Interfaces/Pointer.v|Vellvm.Semantics.Interfaces.Pointer|overlaps_dtyp"
  overlaps_dtyp : ∀ [P : Provenance] [A : @Pointer P] [Sizeof] [@Overlaps P A],
    A.ptr → dtyp → A.ptr → dtyp → Bool
#source_check "src/rocq/Semantics/Interfaces/Pointer.v|Vellvm.Semantics.Interfaces.Pointer|no_overlap"
  no_overlap : ∀ [P : Provenance] [A : @Pointer P] [@Overlaps P A], A.ptr → Nat → A.ptr → Nat → Bool
#source_check "src/rocq/Semantics/Interfaces/Pointer.v|Vellvm.Semantics.Interfaces.Pointer|no_overlap_dtyp"
  no_overlap_dtyp : ∀ [P : Provenance] [A : @Pointer P] [Sizeof] [@Overlaps P A],
    A.ptr → dtyp → A.ptr → dtyp → Bool
#source_check "src/rocq/Semantics/Interfaces/Pointer.v|Vellvm.Semantics.Interfaces.Pointer|ptr_aligned_to"
  ptr_aligned_to : ∀ [P : Provenance] [A : @Pointer P] [@PI P A], A.ptr → Nat → Bool
