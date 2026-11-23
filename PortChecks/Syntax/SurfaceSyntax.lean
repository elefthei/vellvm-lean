import PortChecks.SourceType
import Vellvm.Syntax.SurfaceSyntax

namespace Vellvm.Syntax.SurfaceSyntax

-- The two `Goal P ...; Abort` commands export data to inspect, not proofs of P.
#source_check "src/rocq/Syntax/SurfaceSyntax.v|Vellvm.Syntax.SurfaceSyntax|add_twice"
  add_twice : CFG.mcfg LLVMAst.typ
#source_check "src/rocq/Syntax/SurfaceSyntax.v|Vellvm.Syntax.SurfaceSyntax|test_branch"
  test_branch : CFG.mcfg LLVMAst.typ

open scoped VIR_Notations
open Lean in
run_cmd Elab.Command.liftTermElabM do
  for (n, needles) in [
      (``add_twice, ["#def", "func", "add 5, 9", "15"]),
      (``test_branch, ["modul", "cfg", "alloca i32", "align 4", "store", "load",
        "icmp slt", "br i1", "phi i32", "ret i32"])] do
    let some body := (← getConstInfo n).value? | throwError "missing printing example {n}"
    let doc := (← Meta.ppExpr body).pretty 240
    for needle in needles do
      unless doc.contains needle do
        throwError "printing {n} lost `{needle}`:\n{doc}"

end Vellvm.Syntax.SurfaceSyntax
