module

public import Vellvm.Semantics.Implementations.ParamsV
public import Vellvm.Semantics.Implementations.IPtrInfinite
public import Vellvm.Semantics.Implementations.IPtrFinite

@[expose] public section
namespace Vellvm.Theory.I2F.Refinement
open Semantics.Implementations Semantics.Interfaces.Params

abbrev PInf : Params := @ParamsV.ParamsV IPtrInfinite.IPZ IPtrInfinite.IPZTheory
abbrev PFin : Params := @ParamsV.ParamsV IPtrFinite.IP64Bit IPtrFinite.IP64BitTheory

end Vellvm.Theory.I2F.Refinement
