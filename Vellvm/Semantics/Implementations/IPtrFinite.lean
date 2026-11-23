module

public import Vellvm.Semantics.Interfaces.IPtr
public import Vellvm.Utils.StringUtil

@[expose] public section
namespace Vellvm.Semantics.Implementations.IPtrFinite
open Numeric Interfaces.IPtr VellvmIntegers EOU Syntax.DynamicTypes

variable {sz : Positive}

def from_Z_bits (x : Int) : EOU (Integers.bit_int sz) :=
  if 0 ≤ x ∧ x ≤ @Integers.max_unsigned sz then raise_ret (Integers.repr x)
  else raise_oom "IPBit from_Z oom.".toUTF8

local instance VMemInt_intptr_ix : VMemInt (Integers.bit_int sz) where
  mequ := Integers.eq
  mcmp := Integers.cmp
  mcmpu := Integers.cmpu
  msamesign _ _ := true
  mbitwidth := some sz
  mzero := Integers.zero
  mone := Integers.one
  madd x y :=
    if Integers.eq (Integers.add_carry x y Integers.zero) Integers.one then
      raise_oom "IPBit addition overflow.".toUTF8
    else raise_ret (Integers.add x y)
  madd_carry _ _ _ := Integers.zero
  madd_overflow _ _ _ := Integers.zero
  msub x y :=
    if Integers.unsigned y > Integers.unsigned x then raise_oom "IPBit subtraction underflow.".toUTF8
    else raise_ret (Integers.sub x y)
  msub_borrow _ _ _ := Integers.zero
  msub_overflow _ _ _ := Integers.zero
  mmul x y :=
    let z := Integers.unsigned x * Integers.unsigned y
    -- The source uses the 64-bit bound even for other widths.
    if z > @Integers.max_unsigned Integers.w64 then raise_oom "IPBit multiplication overflow.".toUTF8
    else raise_ret (Integers.repr z)
  mdivu := Integers.divu
  mdivs _ _ := raise_oom "IPBit signed division.".toUTF8
  mmodu := Integers.modu
  mmods _ _ := raise_oom "IPBit signed modulo.".toUTF8
  mshl x y :=
    -- Test the shifted top bit without allocating an integer with up to 2^sz bits.
    if x.bits.toNat = 0 then raise_ret x
    else if x.bits.toNat.log2 + y.bits.toNat < sz.val then raise_ret (Integers.shl x y)
    else raise_oom "IP64Bit left shift overflow.".toUTF8
  mshr := Integers.shr
  mshru := Integers.shru
  mnegative _ := raise_oom "IP64Bit taking negative of a number.".toUTF8
  mand := Integers.and
  mor := Integers.or
  mxor := Integers.xor
  mmin_signed := some (@Integers.min_signed sz)
  mmax_signed := some (@Integers.max_signed sz)
  mmax_unsigned := some (@Integers.max_unsigned sz)
  munsigned := Integers.unsigned
  msigned := Integers.signed
  mrepr := from_Z_bits
  mdtyp_of_int := DTYPE_Iptr

abbrev IP64Bit : IPtr where
  iptr := int64
  zero_iptr := Integers.zero
  VMemInt_iptr := @VMemInt_intptr_ix Integers.w64
  eq_dec_iptr := Integers.eq_dec
  eqb_iptr := Integers.eq
  to_Z := Integers.unsigned
  to_unsigned := Integers.unsigned
  from_Z := from_Z_bits
  show_iptr p := Utils.StringUtil.show_Z (Integers.unsigned p)

attribute [local instance] IP64Bit

private theorem unsigned_of_from_Z {z : Int} {i : Integers.bit_int sz}
    (h : from_Z_bits z = raise_ret i) : Integers.unsigned i = z := by
  unfold from_Z_bits at h
  split at h
  · cases h
    exact Integers.unsigned_repr z (by assumption)
  · cases h

instance IP64BitTheory : @IPtrTheory IP64Bit where
  from_Z_to_Z _ _ h := unsigned_of_from_Z h
  from_Z_injective _ _ _ h₁ h₂ := (unsigned_of_from_Z h₁).symm.trans (unsigned_of_from_Z h₂)
  to_Z_from_Z i := by
    change from_Z_bits (Integers.unsigned i) = raise_ret i
    rw [from_Z_bits, ite_eq_left (Integers.unsigned_range_2 i), Integers.repr_unsigned]
  from_Z_0 := rfl
  to_Z_0 := rfl
  to_Z_inj _ _ := Integers.bit_int.ext_unsigned
  VMemInt_iptr_dtyp := rfl
  VMemInt_iptr_mrepr_from_Z _ := rfl
  to_Z_to_unsigned _ := rfl

end Vellvm.Semantics.Implementations.IPtrFinite
