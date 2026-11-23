import PortChecks.SourceType
import Vellvm.Theory.I2F.I2F_exp.Arithmetic

open Vellvm Vellvm.Numeric Vellvm.Semantics Vellvm.Syntax
open DynamicValues VellvmIntegers Operations.Compare LLVMAst DynamicTypes
open Vellvm.Theory.I2F.Refinement
open Vellvm.Theory.I2F.I2F_exp

#source_check "src/rocq/Theory/I2F/I2F_exp.v|Vellvm.Theory.I2F.I2F_exp|I2F_eval_iop"
  I2F_eval_iop : ∀ ⦃a b : @dvalue PInf⦄ ⦃c d : @dvalue PFin⦄ (op : ibinop) (dt : dtyp),
    I2F_dvalue a c → I2F_dvalue b d →
    I2F_EOU I2F_dvalue (@eval_iop PInf op dt a b) (@eval_iop PFin op dt c d)

#source_check "src/rocq/Theory/I2F/I2F_exp.v|Vellvm.Theory.I2F.I2F_exp|I2F_eval_icmp"
  I2F_eval_icmp : ∀ ⦃a b : @dvalue PInf⦄ ⦃c d : @dvalue PFin⦄ (ss : Bool) (op : icmp) (dt : dtyp),
    I2F_dvalue a c → I2F_dvalue b d →
    I2F_EOU I2F_dvalue (@eval_icmp PInf ss op dt a b) (@eval_icmp PFin ss op dt c d)

#source_check "src/rocq/Theory/I2F/I2F_exp.v|Vellvm.Theory.I2F.I2F_exp|I2F_eval_fop"
  I2F_eval_fop : ∀ ⦃a b : @dvalue PInf⦄ ⦃c d : @dvalue PFin⦄ (op : fbinop) (dt : dtyp),
    I2F_dvalue a c → I2F_dvalue b d →
    I2F_EOU I2F_dvalue (@eval_fop PInf op dt a b) (@eval_fop PFin op dt c d)

#source_check "src/rocq/Theory/I2F/I2F_exp.v|Vellvm.Theory.I2F.I2F_exp|I2F_eval_fcmp"
  I2F_eval_fcmp : ∀ ⦃a b : @dvalue PInf⦄ ⦃c d : @dvalue PFin⦄ (op : fcmp) (dt : dtyp),
    I2F_dvalue a c → I2F_dvalue b d →
    I2F_EOU I2F_dvalue (@eval_fcmp PInf op dt a b) (@eval_fcmp PFin op dt c d)

#source_check "src/rocq/Theory/I2F/I2F_exp.v|Vellvm.Theory.I2F.I2F_exp|I2F_eval_fneg"
  I2F_eval_fneg : ∀ (dt : dtyp) ⦃a : @dvalue PInf⦄ ⦃b : @dvalue PFin⦄, I2F_dvalue a b →
    I2F_EOU I2F_dvalue (@eval_fneg PInf dt a) (@eval_fneg PFin dt b)
