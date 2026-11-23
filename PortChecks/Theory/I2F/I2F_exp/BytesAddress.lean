import PortChecks.SourceType
import Vellvm.Theory.I2F.I2F_exp.BytesAddress

open Vellvm Vellvm.Semantics Vellvm.Semantics.EOU Vellvm.Numeric.Integers
open Vellvm.Theory.I2F.Refinement
open Vellvm.Theory.I2F.I2F_exp

#source_check "src/rocq/Theory/I2F/I2F_exp.v|Vellvm.Theory.I2F.I2F_exp|I2F_from_Z"
  I2F_from_Z : ∀ z : Int, I2F_EOU I2F_Iptr (PInf.IPTR.from_Z z) (PFin.IPTR.from_Z z)

#source_check "src/rocq/Theory/I2F/I2F_exp.v|Vellvm.Theory.I2F.I2F_exp|I2F_int_to_ptr"
  I2F_int_to_ptr : ∀ z pr, I2F_EOU I2F_Addr (PInf.P2I.int_to_ptr z pr) (PFin.P2I.int_to_ptr z pr)
