import PortChecks.SourceType
import Vellvm.Semantics.Implementations.Pointer
import Vellvm.Semantics.Implementations.IPtrInfinite

open Vellvm.Utils.StringUtil Vellvm.Semantics.Interfaces.IPtr Vellvm.Semantics.Interfaces.Pointer
open Vellvm.Semantics.Implementations.Provenance Vellvm.Semantics.Implementations.Pointer

#source_check "src/rocq/Semantics/Implementations/Pointer.v|Vellvm.Semantics.Implementations.Pointer|showIptr"
  showIptr : ∀ [IP : IPtr], Show IP.iptr
#source_check "src/rocq/Semantics/Implementations/Pointer.v|Vellvm.Semantics.Implementations.Pointer|PointerV"
  PointerV : ∀ [IP : IPtr], @Pointer ProvenanceV
#source_check "src/rocq/Semantics/Implementations/Pointer.v|Vellvm.Semantics.Implementations.Pointer|PIV"
  PIV : ∀ [IP : IPtr], @PI ProvenanceV (@PointerV IP)
#source_check "src/rocq/Semantics/Implementations/Pointer.v|Vellvm.Semantics.Implementations.Pointer|PITheoryV"
  PITheoryV : ∀ [IP : IPtr] [@IPtrTheory IP], @PITheory ProvenanceV (@PointerV IP) (@PIV IP)

open Vellvm.Semantics.Implementations.IPtrInfinite (IPZ)

#guard (@PointerV IPZ).show_ptr ((0 : Int), some []) == "(0, Some )".toUTF8
#guard (@PointerV IPZ).show_ptr ((7 : Int), some [4]) == "(7, Some 4)".toUTF8
#guard (@PointerV IPZ).show_ptr ((7 : Int), some [4, 12]) == "(7, Some 412)".toUTF8
#guard (@PointerV IPZ).show_ptr ((7 : Int), none) == "(7, None)".toUTF8
