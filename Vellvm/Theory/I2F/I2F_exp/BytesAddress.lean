import Vellvm.Theory.I2F.Refinement.Values
import Vellvm.Theory.I2F.Refinement.EOU

namespace Vellvm.Theory.I2F.I2F_exp
open Vellvm Vellvm.Semantics Vellvm.Semantics.EOU Vellvm.Numeric.Integers
open Vellvm.Theory.I2F.Refinement

theorem I2F_from_Z : ∀ z : Int, I2F_EOU I2F_Iptr (PInf.IPTR.from_Z z) (PFin.IPTR.from_Z z) := by
  intro z
  change I2F_EOU I2F_Iptr (raise_ret z) (Implementations.IPtrFinite.from_Z_bits z)
  unfold Implementations.IPtrFinite.from_Z_bits
  split
  · exact .I2F_EOU_ret _ _ (unsigned_repr z (by assumption)).symm
  · exact .I2F_EOU_oom _ _

theorem I2F_int_to_ptr : ∀ z pr, I2F_EOU I2F_Addr (PInf.P2I.int_to_ptr z pr) (PFin.P2I.int_to_ptr z pr) := by
  intro z pr
  exact I2F_EOU_bind (fun a ↦ raise_ret (a, pr)) (fun b ↦ raise_ret (b, pr)) (I2F_from_Z z)
    fun _ _ h ↦ .I2F_EOU_ret _ _ ⟨h, rfl⟩

end Vellvm.Theory.I2F.I2F_exp
