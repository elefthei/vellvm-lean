module

public import Vellvm.Semantics.Interfaces.Params
public import Vellvm.Semantics.Implementations.Pointer
public import Vellvm.Semantics.Implementations.Sizeof

@[expose] public section
namespace Vellvm.Semantics.Implementations.ParamsV
open Interfaces.IPtr Interfaces.Params Implementations.Provenance
open Implementations.Pointer Implementations.Sizeof

instance ParamsV [IP : IPtr] [T : @IPtrTheory IP] : Params where
  IPTR := IP
  PROV := ProvenanceV
  SIZE := SizeofV
  PTR := @PointerV IP
  P2I := @PIV IP
  IPTRT := T
  PROVT := ProvenanceVTheory
  SIZET := SizeofTheoryV
  P2IT := @PITheoryV IP T

end Vellvm.Semantics.Implementations.ParamsV
