import PortChecks.SourceType
import Vellvm.Semantics.Implementations.Provenance

open Vellvm.Numeric.Rocqlib Vellvm.Semantics.Interfaces.Provenance
open Vellvm.Semantics.Implementations.Provenance
universe u

#source_check "src/rocq/Semantics/Implementations/Provenance.v|Vellvm.Semantics.Implementations.Provenance|eq_dec_option"
  eq_dec_option : ∀ {A : Type u}, EqDecision A → EqDecision (Option A)
#source_check "src/rocq/Semantics/Implementations/Provenance.v|Vellvm.Semantics.Implementations.Provenance|ProvenanceV"
  ProvenanceV : Provenance
#source_check "src/rocq/Semantics/Implementations/Provenance.v|Vellvm.Semantics.Implementations.Provenance|ProvenanceVTheory"
  ProvenanceVTheory : @ProvenanceTheory ProvenanceV
