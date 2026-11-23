import Vellvm.Theory.I2F.I2F_exp.Words
import Vellvm.Theory.I2F.Refinement.Values
import Vellvm.Theory.I2F.Refinement.EOU
import Vellvm.Semantics.Operations.Compare

namespace Vellvm.Theory.I2F.I2F_exp
open Vellvm Vellvm.Numeric Vellvm.Semantics Vellvm.Syntax
open DynamicValues VellvmIntegers Operations.Compare LLVMAst DynamicTypes
open Vellvm.Theory.I2F.Refinement

open Semantics.EOU
open Semantics.Implementations

private theorem shift_value (x y : int64) :
    Flocq.shiftl (Integers.unsigned x) (Integers.unsigned y) =
      Integers.unsigned x <<< Integers.unsigned y := by
  change Flocq.shiftl (Int.ofNat x.bits.toNat) (Int.ofNat y.bits.toNat) = _
  rw [show Integers.unsigned x <<< Integers.unsigned y =
    Int.ofNat (x.bits.toNat <<< y.bits.toNat) from Int.shiftLeft_natCast ..]
  cases h : y.bits.toNat with
  | zero => simp [Flocq.shiftl, Flocq.shiftr, Flocq.pow2, Flocq.zpowNat, h]
  | succ n => simp [Flocq.shiftl, Flocq.shiftr, Flocq.pow2, Flocq.zpowNat, Nat.shiftLeft_eq,
      show (-1 : Int) < n by omega, show ¬ (n : Int) + 1 < 0 by omega]

private theorem unsigned_shl_le (x y : int64) :
    Integers.unsigned (Integers.shl x y) ≤ Integers.unsigned x <<< Integers.unsigned y := by
  rw [show Integers.unsigned x <<< Integers.unsigned y =
    Int.ofNat (x.bits.toNat <<< y.bits.toNat) from Int.shiftLeft_natCast ..]
  apply Int.ofNat_le.mpr
  simp only [Integers.shl, BitVec.toNat_shiftLeft]
  exact Nat.mod_le _ _

local macro "base_leaf" : tactic => `(tactic| first
  | exact I2F_EOU_error _ _
  | exact I2F_EOU_ub _ _
  | exact I2F_EOU_oom _ _
  | exact I2F_EOU_ret _ _ I2F_dvalue_Poison
  | exact I2F_EOU_ret _ _ (I2F_dvalue_Int _)
  | exact I2F_EOU_ret _ _ (I2F_dvalue_Float _)
  | exact I2F_EOU_ret _ _ (I2F_dvalue_Double _))

private theorem addInf (u v : int64) (q r : Bool) :
    @eval_int_op PInf Int VMemInt_Z (@ToDvalue_iptr PInf) (.Add q r)
        (Integers.unsigned u) (Integers.unsigned v) =
      raise_ret (@DVALUE_Iptr PInf (Integers.unsigned u + Integers.unsigned v)) := by
  cases q <;> cases r <;> rfl

private theorem addFin (u v : int64) (q r : Bool) :
    @eval_int_op PFin int64 IPtrFinite.VMemInt_intptr_ix (@ToDvalue_iptr PFin) (.Add q r) u v =
      if Integers.eq (Integers.add_carry u v Integers.zero) Integers.one then
        raise_oom "IPBit addition overflow.".toUTF8
      else raise_ret (@DVALUE_Iptr PFin (Integers.add u v)) := by
  have hf : (q && Integers.eq (@Integers.zero Integers.w64) Integers.one ||
      r && Integers.eq (@Integers.zero Integers.w64) Integers.one) = false := by
    rw [eq_zero_one_false]; simp
  change (if (q && Integers.eq (@Integers.zero Integers.w64) Integers.one ||
      r && Integers.eq (@Integers.zero Integers.w64) Integers.one) = true then _
    else EOU.bind (if Integers.eq (Integers.add_carry u v Integers.zero) Integers.one then _
                   else _) _) = _
  rw [hf]
  simp only [Bool.false_eq_true, ite_false]
  by_cases carry : Integers.eq (Integers.add_carry u v Integers.zero) Integers.one = true
  · rw [if_pos carry, if_pos carry]; rfl
  · rw [if_neg carry, if_neg carry]; rfl

theorem I2F_eval_int_op_iptr : ∀ (op : ibinop) ⦃x y : PInf.IPTR.iptr⦄ ⦃u v : PFin.IPTR.iptr⦄,
    I2F_Iptr x u → I2F_Iptr y v →
    I2F_EOU I2F_dvalue_base
      (@eval_int_op PInf _ PInf.IPTR.VMemInt_iptr (@ToDvalue_iptr PInf) op x y)
      (@eval_int_op PFin _ PFin.IPTR.VMemInt_iptr (@ToDvalue_iptr PFin) op u v) := by
  rintro op _ _ u v (rfl : _ = _) (rfl : _ = _)
  change I2F_EOU I2F_dvalue_base
    (@eval_int_op PInf Int VMemInt_Z (@ToDvalue_iptr PInf) op (Integers.unsigned u) (Integers.unsigned v))
    (@eval_int_op PFin int64 IPtrFinite.VMemInt_intptr_ix (@ToDvalue_iptr PFin) op u v)
  have hx := (Integers.unsigned_range u).1
  have hy := (Integers.unsigned_range v).1
  have shiftBound := unsigned_shl_le u v
  have zeroShift (h : u.bits.toNat = 0) : Integers.unsigned u <<< Integers.unsigned v = 0 := by
    simpa [Integers.unsigned, Integers.intval, h] using Int.shiftLeft_natCast u.bits.toNat v.bits.toNat
  cases op
  case Add =>
    rw [addInf, addFin]
    split
    · exact I2F_EOU_oom _ _
    · exact I2F_EOU_ret _ _ (I2F_dvalue_Ptr
        (unsigned_add_no_carry u v (Bool.eq_false_of_ne_true (by assumption))).symm)
  all_goals
    dsimp only [eval_int_op, bind, pure, EOU_monad, EOU.bind, VMemInt_Z, IPtrFinite.VMemInt_intptr_ix,
      madd, msub, mmul, mshl, mdivu, mmodu, mshru, mand, mor, mxor,
      mzero, mone, mequ, munsigned, msigned, madd_carry, madd_overflow,
      msub_overflow, msub_borrow, mdtyp_of_int, mbitwidth, mmin_signed, mmax_signed,
      mequ_Z, ToDvalue_iptr, tdb, id_eq, dvp, Function.comp_apply] <;>
    try simp only [eq_zero_one_false, show ((0 : Int) == 1) = false from rfl,
      show (DTYPE_Iptr == DTYPE_Iptr) = true from rfl, Bool.and_false, Bool.false_and,
      Bool.false_or, Bool.or_false, Bool.not_true, Bool.true_and, Bool.and_true,
      Bool.false_eq_true, ite_false, ite_true, shift_value, lt_self_iff_false,
      decide_false, eq_unsigned_eqb (Integers.or u v) (Integers.xor u v),
      unsigned_or_lor, unsigned_xor_lxor, bne]
  all_goals try split_ifs
  all_goals try simp only [*, ite_true, ite_false]
  all_goals try split_ifs
  all_goals try simp only [*, ite_true, ite_false]
  all_goals first
    | exact I2F_EOU_error _ _
    | exact I2F_EOU_oom _ _
    | exact I2F_EOU_ub _ _
    | exact I2F_EOU_ret _ _ I2F_dvalue_Poison
    | apply I2F_EOU_ret _ _ (I2F_dvalue_Ptr ?_); unfold I2F_Iptr
    | (exfalso; simp_all)
  · exact (unsigned_sub_bounded u v (by omega)).symm
  · exact (Integers.unsigned_repr _ ⟨mul_nonneg hx hy, by omega⟩).symm
  · change 0 = Int.ofNat u.bits.toNat
    simp [‹u.bits.toNat = 0›]
  · apply Int.le_antisymm _ shiftBound
    apply Int.le_of_not_gt
    simpa only [decide_eq_true_eq] using
      ‹¬ decide (Integers.unsigned u <<< Integers.unsigned v >
        Integers.unsigned (Integers.shl u v)) = true›
  · exact (unsigned_divu u v (by simpa using ‹¬ (Integers.unsigned v == 0) = true›)).symm
  · exact (unsigned_shru u v).symm
  · exact (unsigned_modu u v (by simpa using ‹¬ (Integers.unsigned v == 0) = true›)).symm
  · exact (unsigned_and_land u v).symm
  · exact (unsigned_or_lor u v).symm
  · exact (unsigned_or_lor u v).symm
  · exact (unsigned_xor_lxor u v).symm

theorem I2F_eval_int_op_bit_int : ∀ ⦃w : Positive⦄ (op : ibinop) (x y : Integers.bit_int w),
    I2F_EOU I2F_dvalue_base
      (@eval_int_op PInf _ (VIntVMemInt (v := VInt_Bounded w)) (@ToDvalue_Int PInf w) op x y)
      (@eval_int_op PFin _ (VIntVMemInt (v := VInt_Bounded w)) (@ToDvalue_Int PFin w) op x y) := by
  intro w op x y
  cases op <;> dsimp only [eval_int_op, VIntVMemInt, VInt_Bounded, bind, pure, EOU_monad,
    EOU.bind, madd, msub, mmul, mdivs, mmods, mshl, mnegative, ToDvalue_Int, tdb,
    Function.comp_apply, dvp, mbitwidth, mdtyp_of_int, Option.any] <;>
    repeat first | base_leaf | split

theorem I2F_eval_iop_integer_base : ∀ (op : ibinop) ⦃a b : @dvalue_base PInf⦄ ⦃c d : @dvalue_base PFin⦄,
    I2F_dvalue_base a c → I2F_dvalue_base b d →
    I2F_EOU I2F_dvalue_base (@eval_iop_integer_base PInf op a b) (@eval_iop_integer_base PFin op c d) := by
  intro op a b c d ha hb
  cases ha <;> cases hb <;> simp only [eval_iop_integer_base] <;>
    first | base_leaf | exact I2F_eval_int_op_iptr op (by assumption) (by assumption) | skip
  all_goals first
    | (split <;> first | base_leaf | (subst_vars; exact I2F_eval_int_op_bit_int op _ _))
    | (cases op <;> (try dsimp only [AstLib.iop_is_div, bind, pure, EOU_monad, EOU.bind]) <;>
        (try simp_all only [I2F_Iptr, Interfaces.IPtr.IPtr.to_Z, PInf, PFin, ParamsV.ParamsV,
          IPtrInfinite.IPZ, IPtrFinite.IP64Bit, id_eq, Bool.false_and, Bool.true_and,
          Bool.false_eq_true, ite_true, ite_false]) <;> repeat first | base_leaf | split)

theorem I2F_eval_int_icmp_iptr : ∀ (ss : Bool) (op : icmp) ⦃x y : PInf.IPTR.iptr⦄ ⦃u v : PFin.IPTR.iptr⦄,
    I2F_Iptr x u → I2F_Iptr y v →
    I2F_EOU I2F_dvalue_base
      (@eval_int_icmp PInf _ PInf.IPTR.VMemInt_iptr ss op x y)
      (@eval_int_icmp PFin _ PFin.IPTR.VMemInt_iptr ss op u v) := by
  rintro ss op _ _ u v (rfl : _ = _) (rfl : _ = _)
  have hx := (Integers.unsigned_range u).1
  have hy := (Integers.unsigned_range v).1
  cases op <;>
    dsimp only [eval_int_icmp, mcmpu, msamesign, mdtyp_of_int, pure, bind, PInf, PFin,
      ParamsV.ParamsV, IPtrInfinite.IPZ, IPtrFinite.IP64Bit, VMemInt_Z,
      IPtrFinite.VMemInt_intptr_ix, EOU_monad, EOU.bind] <;>
    try simp only [cmpu_unsigned, msamesign_Z_nonneg _ _ hx hy, Bool.not_true,
      Bool.and_false, Bool.false_eq_true, ite_false]
  all_goals base_leaf

theorem I2F_ptr_to_addr : ∀ (a : PInf.PTR.ptr) (b : PFin.PTR.ptr), I2F_Addr a b →
    I2F_EOU I2F_dvalue_base (@ptr_to_addr PInf a) (@ptr_to_addr PFin b) := by
  rintro ⟨z,p⟩ ⟨i,q⟩ ⟨h,_⟩
  change z = Integers.unsigned i at h
  subst z
  have sz : PInf.SIZE.bit_sizeof_dtyp (DTYPE_Base DTYPE_Pointer) = 64 := by
    change Sizeof.Bit_sizeof_dtyp _ = 64
    rw [Sizeof.Bit_sizeof_dtyp]
    rfl
  simp only [ptr_to_addr, sz]
  exact I2F_EOU_ret _ _ (I2F_dvalue_Int _)

theorem I2F_eval_fneg_base : ∀ ⦃a : @dvalue_base PInf⦄ ⦃b : @dvalue_base PFin⦄, I2F_dvalue_base a b →
    I2F_EOU I2F_dvalue_base (@eval_fneg_base PInf a) (@eval_fneg_base PFin b) := by
  intro a b h
  cases h <;> base_leaf

theorem I2F_eval_fop_base : ∀ (op : fbinop) ⦃a b : @dvalue_base PInf⦄ ⦃c d : @dvalue_base PFin⦄,
    I2F_dvalue_base a c → I2F_dvalue_base b d →
    I2F_EOU I2F_dvalue_base (@eval_fop_base PInf op a b) (@eval_fop_base PFin op c d) := by
  intro op a b c d ha hb
  cases ha <;> cases hb <;> first | base_leaf | cases op <;> base_leaf

theorem I2F_eval_fcmp_base : ∀ (op : fcmp) ⦃a b : @dvalue_base PInf⦄ ⦃c d : @dvalue_base PFin⦄,
    I2F_dvalue_base a c → I2F_dvalue_base b d →
    I2F_EOU I2F_dvalue_base (@eval_fcmp_base PInf op a b) (@eval_fcmp_base PFin op c d) := by
  intro op a b c d ha hb
  cases ha <;> cases hb <;> base_leaf

theorem I2F_eval_icmp_int_base : ∀ (ss : Bool) (op : icmp) ⦃a b : @dvalue_base PInf⦄ ⦃c d : @dvalue_base PFin⦄,
    I2F_dvalue_base a c → I2F_dvalue_base b d →
    I2F_EOU I2F_dvalue_base (@eval_icmp_int_base PInf ss op a b) (@eval_icmp_int_base PFin ss op c d) := by
  intro ss op a b c d ha hb
  cases ha <;> cases hb <;> simp only [eval_icmp_int_base, is_icmp_operand] <;>
    first | base_leaf | apply I2F_eval_int_icmp_iptr <;> assumption | skip
  split
  · subst_vars
    cases op <;> simp only [eval_int_icmp, VIntVMemInt, VInt_Bounded, EOU_monad, EOU.bind, dvp] <;>
      repeat first | base_leaf | split
  · base_leaf

theorem I2F_eval_icmp_base : ∀ (ss : Bool) (op : icmp) ⦃a b : @dvalue_base PInf⦄ ⦃c d : @dvalue_base PFin⦄,
    I2F_dvalue_base a c → I2F_dvalue_base b d →
    I2F_EOU I2F_dvalue_base (@eval_icmp_base PInf ss op a b) (@eval_icmp_base PFin ss op c d) := by
  intro ss op a b c d ha hb
  have h := I2F_eval_icmp_int_base ss op ha hb
  cases ha <;> cases hb <;> first | exact h | skip
  apply I2F_EOU_bind _ _ (I2F_ptr_to_addr _ _ (by assumption))
  intro x y hxy
  apply I2F_EOU_bind _ _ (I2F_ptr_to_addr _ _ (by assumption))
  exact fun a b hab ↦ I2F_eval_icmp_int_base ss op hxy hab

end Vellvm.Theory.I2F.I2F_exp
