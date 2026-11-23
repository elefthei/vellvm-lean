import Vellvm.Semantics.Denotation.Frames
import Vellvm.Semantics.DynamicValues.Show
import Vellvm.Semantics.Implementations.Memory.Address
import Vellvm.Syntax.AstLib

namespace Vellvm.Semantics.Libraries
open ITree (Effect)
open Vellvm.Tree Interfaces.Params Instrumentation DynamicValues Syntax.LLVMAst Syntax.DynamicTypes
open LLVMEvents (CFGEtop CFGtop)
open VellvmIntegers (int8)

inductive Builtin where
  | puts | putchar
  deriving DecidableEq

private def builtins : List (function_id × Builtin) :=
  [(.Name "puts".toUTF8, .puts), (.Name "putchar".toUTF8, .putchar)]

def selected (decls : List (declaration dtyp)) : List (function_id × Builtin) :=
  builtins.filter fun (name, _) ↦ decls.any fun d ↦ d.dc_name == name

variable [Pa : Params]

namespace Worker
open LLVMEvents.Worker

/-- Use the function ABI with the caller's choice effect in place of `NoChoice`. -/
abbrev FunctionDenotation (M : Effect → Effect → Type → Type v) (B : Effect) :=
  cconv → dtyp → List (dtyp × dvalue) → M CFGEtop B (LLVMEvents.exc ⊕ dvalue)

variable {M : Effect → Effect → Type → Type v} [Runtime M] [Diagnostics M] {B : Effect}

def loadedByte : dvalue → EOU.EOU int8
  | .DVALUE_Base (.DVALUE_I ⟨8, _⟩ b) => .raise_ret b
  | bad => .raise_error ("i8_str_index failed with non-DVALUE_I8 ".toUTF8 ++ show_dvalue bad)

def i8_str_index (strptr : Pa.PTR.ptr) (index : Int) : M CFGEtop B int8 := do
  let iptr ← EOU_to_itree (Pa.IPTR.from_Z index)
  let addr ← EOU_to_itree (Implementations.Memory.ptr_byte_offset strptr iptr)
  let byte ← load (DTYPE_I ⟨8, by decide⟩) (.DVALUE_Base (.DVALUE_Pointer addr))
  EOU_to_itree (loadedByte byte)

def unary (arityError : IRString) (body : dvalue → M CFGEtop B dvalue) :
    FunctionDenotation M B := fun _ _ args ↦
  match args with
  | [(_, v)] => Sum.inr <$> body v
  | _ => «raise» arityError

def putcharBody (v : dvalue) : M CFGEtop B dvalue :=
  match v with
  | .DVALUE_Base (.DVALUE_I sz x) =>
    if sz.val = 32 then do
      let b : int8 := Numeric.Integers.repr (Numeric.Integers.unsigned x)
      io_stdout [b]
      pure (.DVALUE_Base (.DVALUE_I _ b))
    else raiseUB "putc got non-i32 integer argument".toUTF8
  | bad => raiseUB ("putc got non-i32 argument ".toUTF8 ++ show_dvalue bad)

def putchar_denotation : FunctionDenotation M B :=
  unary "putc called with zero or more than one arguments".toUTF8 putcharBody

def putsAt (p : Pa.PTR.ptr) : M CFGEtop B dvalue := do
  let first ← i8_str_index p 0
  let rev ← Runtime.iter (fun (c, bytes, offset) ↦ do
    if c = Numeric.Integers.zero then
      pure (.inr (Numeric.Integers.repr 10 :: bytes))
    else
      let next ← i8_str_index p offset
      pure (.inl (next, c :: bytes, offset + 1))) (first, [], (1 : Int))
  io_stdout rev.reverse
  pure (.DVALUE_Base (.DVALUE_I ⟨8, by decide⟩ Numeric.Integers.zero))

def puts_denotation : FunctionDenotation M B :=
  unary "puts called with zero or more than one arguments".toUTF8 fun v ↦
    match v with
    | .DVALUE_Base (.DVALUE_Pointer p) => putsAt p
    | bad => raiseUB ("puts got non-address argument ".toUTF8 ++ show_dvalue bad)

def denoteBuiltin : Builtin → FunctionDenotation M B
  | .puts => puts_denotation
  | .putchar => putchar_denotation

def instantiate (entries : List (function_id × Builtin)) :
    List (function_id × FunctionDenotation M B) :=
  entries.map fun (name, b) ↦ (name, denoteBuiltin b)

def _LIBRARIES : List (function_id × FunctionDenotation M B) := instantiate builtins

def library_functions (decls : List (declaration dtyp)) : List (function_id × FunctionDenotation M B) :=
  instantiate (selected decls)

variable {N : Effect → Effect → Type → Type w} [Runtime N] [Diagnostics N]
variable [Snapshots M] [Snapshots N] (sim : Simulation M N)

theorem i8_str_index_related (strptr : Pa.PTR.ptr) (index : Int) :
    sim.R (B := B) (i8_str_index strptr index) (i8_str_index strptr index) := by
  unfold i8_str_index
  exact sim.bind (sim.liftEOU _) fun _ ↦ sim.bind (sim.liftEOU _) fun _ ↦
    sim.bind (sim.load _ _) fun byte ↦ sim.liftEOU (loadedByte byte)

private theorem unary_related (msg : IRString)
    {f : dvalue → M CFGEtop B dvalue} {g : dvalue → N CFGEtop B dvalue}
    (h : ∀ v, sim.R (f v) (g v)) (cc : cconv) (rt : dtyp) (args : List (dtyp × dvalue)) :
    sim.R (unary msg f cc rt args) (unary msg g cc rt args) := by
  rcases args with _ | ⟨⟨_, v⟩, _ | ⟨_, _⟩⟩ <;> first | exact sim.«raise» msg | exact sim.map _ (h v)

theorem putchar_denotation_related (cc : cconv) (rt : dtyp) (args : List (dtyp × dvalue)) :
    sim.R (B := B) (putchar_denotation cc rt args) (putchar_denotation cc rt args) := by
  apply unary_related sim
  intro v
  cases v with
  | DVALUE_Base b =>
    cases b <;> first | exact sim.raiseUB _ | skip
    dsimp only [putcharBody]
    split
    · exact sim.bind (sim.io_stdout _) fun _ ↦ sim.pure _
    · exact sim.raiseUB _
  | _ => exact sim.raiseUB _

private theorem putsAt_related (p : Pa.PTR.ptr) : sim.R (B := B) (putsAt p) (putsAt p) := by
  unfold putsAt
  apply sim.bind (i8_str_index_related sim p 0)
  intro first
  apply sim.bind
  · apply sim.iter
    rintro ⟨c, bytes, offset⟩
    dsimp only
    split
    · exact sim.pure _
    · exact sim.bind (i8_str_index_related sim p offset) fun _ ↦ sim.pure _
  · intro rev
    exact sim.bind (sim.io_stdout rev.reverse) fun _ ↦ sim.pure _

theorem puts_denotation_related (cc : cconv) (rt : dtyp) (args : List (dtyp × dvalue)) :
    sim.R (B := B) (puts_denotation cc rt args) (puts_denotation cc rt args) := by
  apply unary_related sim
  intro v
  cases v with
  | DVALUE_Base b => cases b <;> first | exact putsAt_related sim _ | exact sim.raiseUB _
  | _ => exact sim.raiseUB _

theorem denoteBuiltin_related (b : Builtin) (cc : cconv) (rt : dtyp) (args : List (dtyp × dvalue)) :
    sim.R (B := B) (denoteBuiltin b cc rt args) (denoteBuiltin b cc rt args) := by
  cases b with
  | puts => exact puts_denotation_related sim cc rt args
  | putchar => exact putchar_denotation_related sim cc rt args

def EntryRelated (l : function_id × FunctionDenotation M B)
    (r : function_id × FunctionDenotation N B) : Prop :=
  l.1 = r.1 ∧ ∀ cc rt args, sim.R (l.2 cc rt args) (r.2 cc rt args)

private theorem instantiate_related (entries : List (function_id × Builtin)) :
    List.Forall₂ (EntryRelated (B := B) sim) (instantiate entries) (instantiate entries) := by
  induction entries with
  | nil => exact .nil
  | cons e es ih => exact .cons ⟨rfl, denoteBuiltin_related sim e.2⟩ ih

theorem _LIBRARIES_related :
    List.Forall₂ (EntryRelated (B := B) sim) _LIBRARIES _LIBRARIES := instantiate_related sim builtins

theorem library_functions_related (decls : List (declaration dtyp)) :
    List.Forall₂ (EntryRelated (B := B) sim) (library_functions decls) (library_functions decls) :=
  instantiate_related sim (selected decls)

end Worker

def i8_str_index (strptr : Pa.PTR.ptr) (index : Int) : CFGtop int8 := Worker.i8_str_index strptr index

def putchar_denotation : Denotation.function_denotation := Worker.putchar_denotation

def puts_denotation : Denotation.function_denotation := Worker.puts_denotation

def _LIBRARIES : List (function_id × Denotation.function_denotation) := Worker._LIBRARIES

def library_functions (decls : List (declaration dtyp)) :
    List (function_id × Denotation.function_denotation) := Worker.library_functions decls

end Vellvm.Semantics.Libraries
