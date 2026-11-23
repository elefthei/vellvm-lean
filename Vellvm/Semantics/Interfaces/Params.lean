module

public import Vellvm.Semantics.Interfaces.IPtr
public import Vellvm.Semantics.Interfaces.Pointer

@[expose] public section
namespace Vellvm.Semantics.Interfaces.Params
open Syntax.DynamicTypes Interfaces.IPtr Interfaces.Provenance Interfaces.Pointer Interfaces.Sizeof

/-- Components shared by the semantics, with laws for these very same components. -/
class Params where
  Build_Params ::
  IPTR : IPtr
  PROV : Provenance
  SIZE : Sizeof
  PTR : @Pointer PROV
  P2I : @PI PROV PTR
  IPTRT : @IPtrTheory IPTR
  PROVT : @ProvenanceTheory PROV
  SIZET : @SizeofTheory SIZE
  P2IT : @PITheory PROV PTR P2I

export Params (Build_Params IPTR PROV SIZE PTR P2I IPTRT PROVT SIZET P2IT)
attribute [instance] Params.IPTR Params.PROV Params.SIZE Params.PTR Params.P2I
  Params.IPTRT Params.PROVT Params.SIZET Params.P2IT

def pointer_size [Pa : Params] : Nat := Pa.SIZE.store_size_dtyp (DTYPE_Base DTYPE_Pointer)

end Vellvm.Semantics.Interfaces.Params
