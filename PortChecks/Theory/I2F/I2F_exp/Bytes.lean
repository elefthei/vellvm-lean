import PortChecks.SourceType
import Vellvm.Theory.I2F.I2F_exp.Bytes
import PortChecks.Theory.I2F.I2F_exp.MemoryByte
import PortChecks.Theory.I2F.I2F_exp.BytesBasic
import PortChecks.Theory.I2F.I2F_exp.BytesBits
import PortChecks.Theory.I2F.I2F_exp.BytesNoCut
import PortChecks.Theory.I2F.I2F_exp.BytesAddress
import PortChecks.Theory.I2F.I2F_exp.BytesDigits
import PortChecks.Theory.I2F.I2F_exp.BytesPointer
import PortChecks.Theory.I2F.I2F_exp.BytesValidPointer
import PortChecks.Theory.I2F.I2F_exp.BytesSlice
import PortChecks.Theory.I2F.I2F_exp.BytesByteValue
import PortChecks.Theory.I2F.I2F_exp.BytesPack
import PortChecks.Theory.I2F.I2F_exp.BytesWriterBase
import PortChecks.Theory.I2F.I2F_exp.BytesWriterEquations
import PortChecks.Theory.I2F.I2F_exp.BytesWriter
import PortChecks.Theory.I2F.I2F_exp.BytesReaderBase
import PortChecks.Theory.I2F.I2F_exp.BytesReader

open Vellvm Vellvm.Semantics Vellvm.Semantics.Interfaces.Params Vellvm.Semantics.EOU
open Vellvm.Semantics.MemoryBytes Vellvm.Semantics.DynamicValues Vellvm.Utils.ListUtil
open Vellvm.Theory.I2F.Refinement Vellvm.Syntax.DynamicTypes Vellvm.Numeric.Integers
universe u
open Vellvm.Semantics.Interfaces.Sizeof
open Vellvm.Theory.I2F.I2F_exp

#source_check "src/rocq/Theory/I2F/I2F_exp.v|Vellvm.Theory.I2F.I2F_exp|I2F_bitcast_bytes"
  I2F_bitcast_bytes : ∀ {x y} src dst, I2F_dvalue x y → I2F_EOU I2F_dvalue
    (@dvalue_to_memory_bytes PInf src x none >>= fun bs ↦ @memory_bytes_to_dvalue PInf bs dst)
    (@dvalue_to_memory_bytes PFin src y none >>= fun bs ↦ @memory_bytes_to_dvalue PFin bs dst)
