import PortChecks.SourceType
import Vellvm.Semantics.Interfaces.Params

open Vellvm.Semantics.Interfaces.IPtr Vellvm.Semantics.Interfaces.Provenance
open Vellvm.Semantics.Interfaces.Pointer Vellvm.Semantics.Interfaces.Sizeof
open Vellvm.Semantics.Interfaces.Params

#source_check "src/rocq/Semantics/Interfaces/Params.v|Vellvm.Semantics.Interfaces.Params|Params"
  Params : Type 1
#source_check "src/rocq/Semantics/Interfaces/Params.v|Vellvm.Semantics.Interfaces.Params|Build_Params"
  Build_Params : ∀ (I : IPtr) (P : Provenance) (S : Sizeof) (A : @Pointer P) (C : @PI P A),
    @IPtrTheory I → @ProvenanceTheory P → @SizeofTheory S → @PITheory P A C → Params
#source_check "src/rocq/Semantics/Interfaces/Params.v|Vellvm.Semantics.Interfaces.Params|IPTR"
  IPTR : ∀ [Pa : Params], IPtr
#source_check "src/rocq/Semantics/Interfaces/Params.v|Vellvm.Semantics.Interfaces.Params|PROV"
  PROV : ∀ [Pa : Params], Provenance
#source_check "src/rocq/Semantics/Interfaces/Params.v|Vellvm.Semantics.Interfaces.Params|SIZE"
  SIZE : ∀ [Pa : Params], Sizeof
#source_check "src/rocq/Semantics/Interfaces/Params.v|Vellvm.Semantics.Interfaces.Params|PTR"
  PTR : ∀ [Pa : Params], @Pointer Pa.PROV
#source_check "src/rocq/Semantics/Interfaces/Params.v|Vellvm.Semantics.Interfaces.Params|P2I"
  P2I : ∀ [Pa : Params], @PI Pa.PROV Pa.PTR
#source_check "src/rocq/Semantics/Interfaces/Params.v|Vellvm.Semantics.Interfaces.Params|IPTRT"
  IPTRT : ∀ [Pa : Params], @IPtrTheory Pa.IPTR
#source_check "src/rocq/Semantics/Interfaces/Params.v|Vellvm.Semantics.Interfaces.Params|PROVT"
  PROVT : ∀ [Pa : Params], @ProvenanceTheory Pa.PROV
#source_check "src/rocq/Semantics/Interfaces/Params.v|Vellvm.Semantics.Interfaces.Params|SIZET"
  SIZET : ∀ [Pa : Params], @SizeofTheory Pa.SIZE
#source_check "src/rocq/Semantics/Interfaces/Params.v|Vellvm.Semantics.Interfaces.Params|P2IT"
  P2IT : ∀ [Pa : Params], @PITheory Pa.PROV Pa.PTR Pa.P2I
#source_check "src/rocq/Semantics/Interfaces/Params.v|Vellvm.Semantics.Interfaces.Params|pointer_size"
  pointer_size : ∀ [Pa : Params], Nat
