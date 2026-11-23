module

public import Vellvm.Semantics.VellvmIntegers

@[expose] public section
namespace Vellvm.Semantics.Interfaces.IPtr
open Vellvm.Numeric.Rocqlib Vellvm.Syntax.DynamicTypes Vellvm.Utils.ListUtil
open Vellvm.Semantics.EOU Vellvm.Semantics.VellvmIntegers

class IPtr where
  Build_IPtr ::
  iptr : Type
  zero_iptr : iptr
  VMemInt_iptr : VMemInt iptr
  eq_dec_iptr : EqDecision iptr
  eqb_iptr : iptr → iptr → Bool
  to_Z : iptr → Int
  to_unsigned : iptr → Int
  from_Z : Int → EOU iptr
  show_iptr : iptr → IRString

export IPtr (Build_IPtr iptr zero_iptr VMemInt_iptr eq_dec_iptr eqb_iptr to_Z to_unsigned
  from_Z show_iptr)

class IPtrTheory [P : IPtr] : Prop where
  Build_IPtrTheory ::
  from_Z_to_Z (z : Int) {i : P.iptr} : P.from_Z z = raise_ret i → P.to_Z i = z
  from_Z_injective (z₁ z₂ : Int) {i : P.iptr} :
    P.from_Z z₁ = raise_ret i → P.from_Z z₂ = raise_ret i → z₁ = z₂
  to_Z_from_Z (i : P.iptr) : P.from_Z (P.to_Z i) = raise_ret i
  from_Z_0 : P.from_Z 0 = raise_ret P.zero_iptr
  to_Z_0 : P.to_Z P.zero_iptr = 0
  to_Z_inj (x y : P.iptr) : P.to_Z x = P.to_Z y → x = y
  VMemInt_iptr_dtyp : P.VMemInt_iptr.mdtyp_of_int = DTYPE_Iptr
  VMemInt_iptr_mrepr_from_Z (x : Int) : P.VMemInt_iptr.mrepr x = P.from_Z x
  to_Z_to_unsigned (x : P.iptr) : P.to_Z x = P.to_unsigned x

export IPtrTheory (Build_IPtrTheory from_Z_to_Z from_Z_injective to_Z_from_Z from_Z_0 to_Z_0
  to_Z_inj VMemInt_iptr_dtyp VMemInt_iptr_mrepr_from_Z to_Z_to_unsigned)

def intptr_seq [P : IPtr] (start size : Nat) : EOU (List P.iptr) :=
  seq_map_monad_acc (P.from_Z ∘ Int.ofNat) start (N_to_nat_safe size)

end Vellvm.Semantics.Interfaces.IPtr
