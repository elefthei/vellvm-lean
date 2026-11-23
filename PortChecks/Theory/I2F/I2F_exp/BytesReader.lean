import PortChecks.SourceType
import Vellvm.Theory.I2F.I2F_exp.BytesReader

open Vellvm Vellvm.Semantics Vellvm.Semantics.Interfaces.Params Vellvm.Semantics.EOU
open Vellvm.Semantics.MemoryBytes Vellvm.Semantics.DynamicValues Vellvm.Utils.ListUtil
open Vellvm.Theory.I2F.Refinement Vellvm.Syntax.DynamicTypes Vellvm.Numeric.Integers
universe u
open Vellvm.Semantics.Interfaces.Sizeof
open Vellvm.Theory.I2F.I2F_exp

#source_check "src/rocq/Theory/I2F/I2F_exp.v|Vellvm.Theory.I2F.I2F_exp|I2F_memory_bytes_to_dvalue"
  I2F_memory_bytes_to_dvalue : ∀ t, ∀ {bs cs}, List.Forall₂ I2F_memory_byte bs cs → I2F_EOU I2F_dvalue (@memory_bytes_to_dvalue PInf bs t) (@memory_bytes_to_dvalue PFin cs t)
