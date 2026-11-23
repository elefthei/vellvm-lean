import PortChecks.SourceType
import Vellvm.Theory.I2F.I2F_exp.Words

open Vellvm Vellvm.Numeric Vellvm.Numeric.Integers
open Vellvm.Semantics.VellvmIntegers (mcmpu_Z mcmp_Z msamesign_Z)
open Vellvm.Theory.I2F.I2F_exp

#source_check "src/rocq/Theory/I2F/I2F_exp.v|Vellvm.Theory.I2F.I2F_exp|unsigned_add_bounded"
  unsigned_add_bounded : ∀ {sz : Positive} (x y : bit_int sz), unsigned x + unsigned y < @modulus sz →
    unsigned (add x y) = unsigned x + unsigned y

#source_check "src/rocq/Theory/I2F/I2F_exp.v|Vellvm.Theory.I2F.I2F_exp|unsigned_sub_bounded"
  unsigned_sub_bounded : ∀ {sz : Positive} (x y : bit_int sz), unsigned y ≤ unsigned x →
    unsigned (sub x y) = unsigned x - unsigned y

#source_check "src/rocq/Theory/I2F/I2F_exp.v|Vellvm.Theory.I2F.I2F_exp|unsigned_divu"
  unsigned_divu : ∀ {sz : Positive} (x y : bit_int sz), unsigned y ≠ 0 →
    unsigned (divu x y) = (unsigned x).fdiv (unsigned y)

#source_check "src/rocq/Theory/I2F/I2F_exp.v|Vellvm.Theory.I2F.I2F_exp|unsigned_modu"
  unsigned_modu : ∀ {sz : Positive} (x y : bit_int sz), unsigned y ≠ 0 →
    unsigned (modu x y) = (unsigned x).fmod (unsigned y)

#source_check "src/rocq/Theory/I2F/I2F_exp.v|Vellvm.Theory.I2F.I2F_exp|unsigned_shru"
  unsigned_shru : ∀ {sz : Positive} (x y : bit_int sz),
    unsigned (shru x y) = unsigned x >>> unsigned y

#source_check "src/rocq/Theory/I2F/I2F_exp.v|Vellvm.Theory.I2F.I2F_exp|unsigned_testbit_above"
  unsigned_testbit_above : ∀ {sz : Positive} (x : bit_int sz) (i : Int), (sz.val : Int) ≤ i →
    Zbits.testbit (unsigned x) i = false

#source_check "src/rocq/Theory/I2F/I2F_exp.v|Vellvm.Theory.I2F.I2F_exp|max_unsigned_ones"
  max_unsigned_ones : ∀ {sz : Positive}, @max_unsigned sz = Int.ofNat (2 ^ sz.val - 1)

#source_check "src/rocq/Theory/I2F/I2F_exp.v|Vellvm.Theory.I2F.I2F_exp|Z_bits_range"
  Z_bits_range : ∀ {sz : Positive} (z : Int), 0 ≤ z →
    (∀ i : Int, (sz.val : Int) ≤ i → Zbits.testbit z i = false) → 0 ≤ z ∧ z ≤ @max_unsigned sz

#source_check "src/rocq/Theory/I2F/I2F_exp.v|Vellvm.Theory.I2F.I2F_exp|unsigned_and_land"
  unsigned_and_land : ∀ {sz : Positive} (x y : bit_int sz),
    unsigned (and x y) = Int.land (unsigned x) (unsigned y)

#source_check "src/rocq/Theory/I2F/I2F_exp.v|Vellvm.Theory.I2F.I2F_exp|unsigned_or_lor"
  unsigned_or_lor : ∀ {sz : Positive} (x y : bit_int sz),
    unsigned (or x y) = Int.lor (unsigned x) (unsigned y)

#source_check "src/rocq/Theory/I2F/I2F_exp.v|Vellvm.Theory.I2F.I2F_exp|unsigned_xor_lxor"
  unsigned_xor_lxor : ∀ {sz : Positive} (x y : bit_int sz),
    unsigned (xor x y) = Int.xor (unsigned x) (unsigned y)

#source_check "src/rocq/Theory/I2F/I2F_exp.v|Vellvm.Theory.I2F.I2F_exp|eq_unsigned_eqb"
  eq_unsigned_eqb : ∀ {sz : Positive} (x y : bit_int sz), eq x y = (unsigned x == unsigned y)

#source_check "src/rocq/Theory/I2F/I2F_exp.v|Vellvm.Theory.I2F.I2F_exp|eq_zero_one_false"
  eq_zero_one_false : ∀ {sz : Positive}, @eq sz zero one = false

#source_check "src/rocq/Theory/I2F/I2F_exp.v|Vellvm.Theory.I2F.I2F_exp|unsigned_add_no_carry"
  unsigned_add_no_carry : ∀ {sz : Positive} (x y : bit_int sz), eq (add_carry x y zero) one = false →
    unsigned (add x y) = unsigned x + unsigned y

#source_check "src/rocq/Theory/I2F/I2F_exp.v|Vellvm.Theory.I2F.I2F_exp|ltu_unsigned_ltb"
  ltu_unsigned_ltb : ∀ {sz : Positive} (x y : bit_int sz), ltu x y = decide (unsigned x < unsigned y)

#source_check "src/rocq/Theory/I2F/I2F_exp.v|Vellvm.Theory.I2F.I2F_exp|cmpu_unsigned"
  cmpu_unsigned : ∀ {sz : Positive} (c : comparison) (x y : bit_int sz),
    cmpu c x y = mcmpu_Z c (unsigned x) (unsigned y)

#source_check "src/rocq/Theory/I2F/I2F_exp.v|Vellvm.Theory.I2F.I2F_exp|msamesign_Z_nonneg"
  msamesign_Z_nonneg : ∀ x y : Int, 0 ≤ x → 0 ≤ y → msamesign_Z x y = true
