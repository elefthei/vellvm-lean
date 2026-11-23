import Vellvm.Theory.I2F.I2F_exp.BytesReader
import Vellvm.Theory.I2F.I2F_exp.BytesWriter

namespace Vellvm.Theory.I2F.I2F_exp
open Vellvm Vellvm.Semantics Vellvm.Semantics.Interfaces.Params Vellvm.Semantics.EOU
open Vellvm.Semantics.MemoryBytes Vellvm.Semantics.DynamicValues Vellvm.Utils.ListUtil
open Vellvm.Theory.I2F.Refinement Vellvm.Syntax.DynamicTypes Vellvm.Numeric.Integers
universe u
open Vellvm.Semantics.Interfaces.Sizeof

theorem I2F_bitcast_bytes : ∀ {x y} src dst, I2F_dvalue x y → I2F_EOU I2F_dvalue
    (@dvalue_to_memory_bytes PInf src x none >>= fun bs ↦ @memory_bytes_to_dvalue PInf bs dst)
    (@dvalue_to_memory_bytes PFin src y none >>= fun bs ↦ @memory_bytes_to_dvalue PFin bs dst) := by
  intro x y src dst h
  exact I2F_EOU_bind _ _ (I2F_memory_dvalue_to_memory_bytes src h none)
    fun _ _ hb ↦ I2F_memory_bytes_to_dvalue dst hb

end Vellvm.Theory.I2F.I2F_exp
