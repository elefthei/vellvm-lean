import Vellvm.Theory.I2F.I2F_toplevel.Allocation
import Vellvm.Theory.I2F.I2F_exp.Operations

namespace Vellvm.Theory.I2F.I2F_toplevel
open Refinement Semantics.TopLevel Syntax.DynamicTypes Syntax.LLVMAst

theorem I2F_initialize_global (g : «global» dtyp) : I2F_refine_MCFG (fun _ _ : Unit ↦ True)
    (@initialize_global PInf g) (@initialize_global PFin g) :=
  initializeGlobalOfExp g fun e ↦ I2F_exp.I2F_denote_exp e (some g.g_typ)

theorem I2F_initialize_globals (gs : List («global» dtyp)) : I2F_refine_MCFG (fun _ _ : Unit ↦ True)
    (@initialize_globals PInf gs) (@initialize_globals PFin gs) :=
  initializeGlobalsOfGlobal I2F_initialize_global gs

theorem I2F_build_global_environment (m : Syntax.CFG.mcfg dtyp) : I2F_refine_MCFG (fun _ _ : Unit ↦ True)
    (@build_global_environment PInf m) (@build_global_environment PFin m) :=
  buildGlobalEnvironmentOfGlobals I2F_initialize_globals m

end Vellvm.Theory.I2F.I2F_toplevel
