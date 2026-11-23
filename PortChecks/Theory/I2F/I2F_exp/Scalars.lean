import PortChecks.SourceType
import Vellvm.Theory.I2F.I2F_exp.Scalars

open Vellvm Vellvm.Numeric Vellvm.Semantics Vellvm.Syntax
open DynamicValues VellvmIntegers Operations.Compare LLVMAst DynamicTypes
open Vellvm.Theory.I2F.Refinement
open Vellvm.Theory.I2F.I2F_exp

#source_check "src/rocq/Theory/I2F/I2F_exp.v|Vellvm.Theory.I2F.I2F_exp|I2F_eval_int_op_iptr"
  I2F_eval_int_op_iptr : ∀ (op : ibinop) ⦃x y : PInf.IPTR.iptr⦄ ⦃u v : PFin.IPTR.iptr⦄,
    I2F_Iptr x u → I2F_Iptr y v →
    I2F_EOU I2F_dvalue_base
      (@eval_int_op PInf _ PInf.IPTR.VMemInt_iptr (@ToDvalue_iptr PInf) op x y)
      (@eval_int_op PFin _ PFin.IPTR.VMemInt_iptr (@ToDvalue_iptr PFin) op u v)

#source_check "src/rocq/Theory/I2F/I2F_exp.v|Vellvm.Theory.I2F.I2F_exp|I2F_eval_int_op_bit_int"
  I2F_eval_int_op_bit_int : ∀ ⦃w : Positive⦄ (op : ibinop) (x y : Integers.bit_int w),
    I2F_EOU I2F_dvalue_base
      (@eval_int_op PInf _ (VIntVMemInt (v := VInt_Bounded w)) (@ToDvalue_Int PInf w) op x y)
      (@eval_int_op PFin _ (VIntVMemInt (v := VInt_Bounded w)) (@ToDvalue_Int PFin w) op x y)

#source_check "src/rocq/Theory/I2F/I2F_exp.v|Vellvm.Theory.I2F.I2F_exp|I2F_eval_iop_integer_base"
  I2F_eval_iop_integer_base : ∀ (op : ibinop) ⦃a b : @dvalue_base PInf⦄ ⦃c d : @dvalue_base PFin⦄,
    I2F_dvalue_base a c → I2F_dvalue_base b d →
    I2F_EOU I2F_dvalue_base (@eval_iop_integer_base PInf op a b) (@eval_iop_integer_base PFin op c d)

#source_check "src/rocq/Theory/I2F/I2F_exp.v|Vellvm.Theory.I2F.I2F_exp|I2F_eval_int_icmp_iptr"
  I2F_eval_int_icmp_iptr : ∀ (ss : Bool) (op : icmp) ⦃x y : PInf.IPTR.iptr⦄ ⦃u v : PFin.IPTR.iptr⦄,
    I2F_Iptr x u → I2F_Iptr y v →
    I2F_EOU I2F_dvalue_base
      (@eval_int_icmp PInf _ PInf.IPTR.VMemInt_iptr ss op x y)
      (@eval_int_icmp PFin _ PFin.IPTR.VMemInt_iptr ss op u v)

#source_check "src/rocq/Theory/I2F/I2F_exp.v|Vellvm.Theory.I2F.I2F_exp|I2F_ptr_to_addr"
  I2F_ptr_to_addr : ∀ (a : PInf.PTR.ptr) (b : PFin.PTR.ptr), I2F_Addr a b →
    I2F_EOU I2F_dvalue_base (@ptr_to_addr PInf a) (@ptr_to_addr PFin b)

#source_check "src/rocq/Theory/I2F/I2F_exp.v|Vellvm.Theory.I2F.I2F_exp|I2F_eval_fneg_base"
  I2F_eval_fneg_base : ∀ ⦃a : @dvalue_base PInf⦄ ⦃b : @dvalue_base PFin⦄, I2F_dvalue_base a b →
    I2F_EOU I2F_dvalue_base (@eval_fneg_base PInf a) (@eval_fneg_base PFin b)

#source_check "src/rocq/Theory/I2F/I2F_exp.v|Vellvm.Theory.I2F.I2F_exp|I2F_eval_fop_base"
  I2F_eval_fop_base : ∀ (op : fbinop) ⦃a b : @dvalue_base PInf⦄ ⦃c d : @dvalue_base PFin⦄,
    I2F_dvalue_base a c → I2F_dvalue_base b d →
    I2F_EOU I2F_dvalue_base (@eval_fop_base PInf op a b) (@eval_fop_base PFin op c d)

#source_check "src/rocq/Theory/I2F/I2F_exp.v|Vellvm.Theory.I2F.I2F_exp|I2F_eval_fcmp_base"
  I2F_eval_fcmp_base : ∀ (op : fcmp) ⦃a b : @dvalue_base PInf⦄ ⦃c d : @dvalue_base PFin⦄,
    I2F_dvalue_base a c → I2F_dvalue_base b d →
    I2F_EOU I2F_dvalue_base (@eval_fcmp_base PInf op a b) (@eval_fcmp_base PFin op c d)

#source_check "src/rocq/Theory/I2F/I2F_exp.v|Vellvm.Theory.I2F.I2F_exp|I2F_eval_icmp_int_base"
  I2F_eval_icmp_int_base : ∀ (ss : Bool) (op : icmp) ⦃a b : @dvalue_base PInf⦄ ⦃c d : @dvalue_base PFin⦄,
    I2F_dvalue_base a c → I2F_dvalue_base b d →
    I2F_EOU I2F_dvalue_base (@eval_icmp_int_base PInf ss op a b) (@eval_icmp_int_base PFin ss op c d)

#source_check "src/rocq/Theory/I2F/I2F_exp.v|Vellvm.Theory.I2F.I2F_exp|I2F_eval_icmp_base"
  I2F_eval_icmp_base : ∀ (ss : Bool) (op : icmp) ⦃a b : @dvalue_base PInf⦄ ⦃c d : @dvalue_base PFin⦄,
    I2F_dvalue_base a c → I2F_dvalue_base b d →
    I2F_EOU I2F_dvalue_base (@eval_icmp_base PInf ss op a b) (@eval_icmp_base PFin ss op c d)
