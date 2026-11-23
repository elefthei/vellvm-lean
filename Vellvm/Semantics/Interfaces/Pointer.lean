module

public import Vellvm.Semantics.EOU
public import Vellvm.Semantics.Interfaces.Provenance
public import Vellvm.Semantics.Interfaces.Sizeof

@[expose] public section
namespace Vellvm.Semantics.Interfaces.Pointer
open Numeric.Rocqlib Syntax.DynamicTypes Semantics.EOU Interfaces.Provenance Interfaces.Sizeof

class Pointer [P : Provenance] where
  Build_Pointer ::
  ptr : Type
  null : ptr
  eq_dec_ptr : EqDecision ptr
  ptr_provenance : ptr → P.prov
  show_ptr : ptr → IRString
export Pointer (Build_Pointer ptr null eq_dec_ptr ptr_provenance show_ptr)

class Overlaps [P : Provenance] [A : @Pointer P] : Type where
  Build_Overlaps ::
  overlaps : A.ptr → Nat → A.ptr → Nat → Bool
export Overlaps (Build_Overlaps overlaps)

class PI [P : Provenance] [A : @Pointer P] : Type where
  Build_PI ::
  ptr_to_int : A.ptr → Int
  int_to_ptr : Int → P.prov → EOU A.ptr
export PI (Build_PI ptr_to_int int_to_ptr)

class PITheory [P : Provenance] [A : @Pointer P] [C : @PI P A] : Prop where
  Build_PITheory ::
  int_to_ptr_provenance (x : Int) (p : P.prov) {a : A.ptr} :
    C.int_to_ptr x p = raise_ret a → A.ptr_provenance a = p
  int_to_ptr_ptr_to_int (a : A.ptr) {p : P.prov} :
    A.ptr_provenance a = p → C.int_to_ptr (C.ptr_to_int a) p = raise_ret a
  int_to_ptr_ptr_to_int_exists (a : A.ptr) (p : P.prov) :
    ∃ a', C.int_to_ptr (C.ptr_to_int a) p = raise_ret a' ∧
      C.ptr_to_int a' = C.ptr_to_int a ∧ A.ptr_provenance a' = p
  ptr_to_int_int_to_ptr (x : Int) (p : P.prov) {a : A.ptr} :
    C.int_to_ptr x p = raise_ret a → C.ptr_to_int a = x
export PITheory (Build_PITheory int_to_ptr_provenance int_to_ptr_ptr_to_int
  int_to_ptr_ptr_to_int_exists ptr_to_int_int_to_ptr)

variable [P : Provenance] [A : @Pointer P]

instance overlaps_ptoi [C : @PI P A] : @Overlaps P A where
  overlaps a₁ sz₁ a₂ sz₂ :=
    let i₁ := C.ptr_to_int a₁
    let i₂ := C.ptr_to_int a₂
    decide (i₁ ≤ i₂ + Int.ofNat sz₂ - 1) && decide (i₂ ≤ i₁ + Int.ofNat sz₁ - 1)

def overlaps_dtyp [Sizeof] [O : @Overlaps P A] (a₁ : A.ptr) (τ₁ : dtyp) (a₂ : A.ptr) (τ₂ : dtyp) :
    Bool := O.overlaps a₁ (store_size_dtyp τ₁) a₂ (store_size_dtyp τ₂)

def no_overlap [O : @Overlaps P A] (a₁ : A.ptr) (sz₁ : Nat) (a₂ : A.ptr) (sz₂ : Nat) : Bool :=
  !(O.overlaps a₁ sz₁ a₂ sz₂)

def no_overlap_dtyp [Sizeof] [O : @Overlaps P A] (a₁ : A.ptr) (τ₁ : dtyp) (a₂ : A.ptr) (τ₂ : dtyp) :
    Bool := !(overlaps_dtyp a₁ τ₁ a₂ τ₂)

def ptr_aligned_to [C : @PI P A] (a : A.ptr) (align : Nat) : Bool :=
  align == 0 || C.ptr_to_int a % Int.ofNat align == 0

end Vellvm.Semantics.Interfaces.Pointer
