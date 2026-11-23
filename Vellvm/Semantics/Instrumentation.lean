module

public import Vellvm.Tree.Runtime
public import Vellvm.Semantics.DynamicValues.Basic
public import Vellvm.Syntax.RawIdMaps

@[expose] public section
namespace Vellvm.Semantics.Instrumentation
open ITree (Effect)
open Tree Interfaces.Params DynamicValues Syntax.LLVMAst Syntax.RawIdMaps

/-- Extraction records locations even when tracing is off. These requests are not LLVM events. -/
inductive TraceRequest [Pa : Params] where
  | setLoc (loc : Option file_info)
  | diagnostic (bytes : IRString)
  | globals (vars : rmap dvalue)
  | locals (vars : rmap dvalue)
  | framePush (vars : rmap dvalue) (exc : Option dvalue)
  | frameSet (vars : rmap dvalue) (exc : Option dvalue)
  | framePop

@[implicit_reducible] def Trace [Params] : Effect := ⟨TraceRequest, fun _ ↦ Unit⟩

class Diagnostics (M : Effect → Effect → Type → Type v) where
  setLoc {E B} : Option file_info → M E B Unit
  diagnostic {E B} : IRString → M E B Unit

class Snapshots (M : Effect → Effect → Type → Type v) [Pa : Params] where
  record {E B} : TraceRequest → M E B Unit

def quietDiagnostics (M) [Runtime M] : Diagnostics M := ⟨fun _ ↦ pure (), fun _ ↦ pure ()⟩
def quietSnapshots (M) [Runtime M] [Params] : Snapshots M := ⟨fun _ ↦ pure ()⟩

instance : Diagnostics CTree.CTree := quietDiagnostics _
instance : Diagnostics Producer := quietDiagnostics _
instance [Params] : Snapshots CTree.CTree := quietSnapshots _
instance [Params] : Snapshots Producer := quietSnapshots _

end Vellvm.Semantics.Instrumentation
