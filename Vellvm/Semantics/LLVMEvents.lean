module

public import Vellvm.Semantics.Instrumentation

@[expose] public section
namespace Vellvm.Semantics.LLVMEvents
open ITree (Effect Subeffect)
open CTree (CTree)
open Tree Interfaces.Params DynamicValues Syntax.LLVMAst Syntax.DynamicTypes

abbrev exc [Params] := dvalue

inductive GlobalRequest [Pa : Params] where
  | GlobalWrite (id : raw_id) (dv : dvalue)
  | GlobalRead (id : raw_id)
export GlobalRequest (GlobalWrite GlobalRead)

@[implicit_reducible] def GlobalE [Pa : Params] : Effect where
  I := GlobalRequest
  O
    | .GlobalWrite _ _ => Unit
    | .GlobalRead _ => dvalue

inductive LocalRequest [Pa : Params] where
  | LocalWrite (id : raw_id) (dv : dvalue)
  | LocalRead (id : raw_id)
export LocalRequest (LocalWrite LocalRead)

@[implicit_reducible] def LocalE [Pa : Params] : Effect where
  I := LocalRequest
  O
    | .LocalWrite _ _ => Unit
    | .LocalRead _ => dvalue

inductive StackRequest [Pa : Params] where
  | StackPush (args : List (raw_id × dvalue))
  | StackPop
  | StackRaise (x : exc)
  | StackGetExc
export StackRequest (StackPush StackPop StackRaise StackGetExc)

@[implicit_reducible] def StackE [Pa : Params] : Effect where
  I := StackRequest
  O
    | .StackPush _ => Unit
    | .StackPop => Unit
    | .StackRaise _ => Unit
    | .StackGetExc => Option exc

inductive MemoryRequest [Pa : Params] where
  | MemPush
  | MemPop
  | Alloca (t : dtyp) (num_elements : Nat) (align : Option Nat)
  | Load (t : dtyp) (a : dvalue)
  | Store (t : dtyp) (a : dvalue) (v : dvalue)
  | Conv (cv : impure_conversion) (t_from : dtyp) (v : dvalue) (t_to : dtyp)
export MemoryRequest (MemPush MemPop Alloca Load Store Conv)

@[implicit_reducible] def MemoryE [Pa : Params] : Effect where
  I := MemoryRequest
  O
    | .MemPush => Unit
    | .MemPop => Unit
    | .Alloca _ _ _ => dvalue
    | .Load _ _ => dvalue
    | .Store _ _ _ => Unit
    | .Conv _ _ _ _ => dvalue

inductive DrawRequest where
  | Draw (t : dtyp)
export DrawRequest (Draw)

@[implicit_reducible] def DrawE [Pa : Params] : Effect where
  I := DrawRequest
  O
    | .Draw _ => dvalue

inductive CallRequest [Pa : Params] where
  | Call (t : dtyp) (cc : cconv) (f : dvalue) (args : List (dtyp × dvalue))
export CallRequest (Call)

@[implicit_reducible] def CallE [Pa : Params] : Effect where
  I := CallRequest
  O
    | .Call _ _ _ _ => exc ⊕ dvalue

inductive ExternalCallRequest [Pa : Params] where
  | ExternalCall (t : dtyp) (f : dvalue) (args : List (dtyp × dvalue))
  | IO_stdout (bytes : List VellvmIntegers.int8)
  | IO_stderr (bytes : List VellvmIntegers.int8)
export ExternalCallRequest (ExternalCall IO_stdout IO_stderr)

@[implicit_reducible] def ExternalCallE [Pa : Params] : Effect where
  I := ExternalCallRequest
  O
    | .ExternalCall _ _ _ => dvalue
    | .IO_stdout _ => Unit
    | .IO_stderr _ => Unit

inductive IntrinsicRequest [Pa : Params] where
  | Intrinsic (t : dtyp) (f : IRString) (args : List (dtyp × dvalue)) (vararg : Option Pa.PTR.ptr)
export IntrinsicRequest (Intrinsic)

@[implicit_reducible] def IntrinsicE [Pa : Params] : Effect where
  I := IntrinsicRequest
  O
    | .Intrinsic _ _ _ _ => exc ⊕ dvalue

inductive LLVMExcRequest [Pa : Params] where
  | LLVMExc (value : exc)
export LLVMExcRequest (LLVMExc)

@[implicit_reducible] def LLVMExcE [Pa : Params] : Effect where
  I := LLVMExcRequest
  O
    | .LLVMExc _ => Empty

inductive UBERequest where
  | ThrowUB (value : Unit)
export UBERequest (ThrowUB)

@[implicit_reducible] def UBE : Effect where
  I := UBERequest
  O
    | .ThrowUB _ => Empty

inductive FailureRequest where
  | Throw (value : Unit)
export FailureRequest (Throw)

@[implicit_reducible] def FailureE : Effect where
  I := FailureRequest
  O
    | .Throw _ => Empty

inductive OOMRequest where
  | ThrowOOM (value : Unit)
export OOMRequest (ThrowOOM)

@[implicit_reducible] def OOME : Effect where
  I := OOMRequest
  O
    | .ThrowOOM _ => Empty

inductive DebugRequest where
  | Debug (value : Unit)
export DebugRequest (Debug)

@[implicit_reducible] def DebugE : Effect where
  I := DebugRequest
  O
    | .Debug _ => Unit

structure printer where
  mk_printer ::
  printer_set_loc : Option file_info → IRString
  printer_print_msg : IRString → Unit
  printer_get_loc : Unit → IRString
export printer (mk_printer printer_set_loc printer_print_msg printer_get_loc)

def printer_object : printer := ⟨fun _ ↦ .empty, fun _ ↦ (), fun _ ↦ .empty⟩
def set_loc := printer_object.printer_set_loc
def print_msg := printer_object.printer_print_msg
def get_loc := printer_object.printer_get_loc

abbrev MCFGEtop [Params] := ExternalCallE ⊕ₑ IntrinsicE ⊕ₑ GlobalE ⊕ₑ (LocalE ⊕ₑ StackE) ⊕ₑ
  MemoryE ⊕ₑ DrawE ⊕ₑ OOME ⊕ₑ LLVMExcE ⊕ₑ UBE ⊕ₑ DebugE ⊕ₑ FailureE
abbrev CFGEtop [Params] := CallE ⊕ₑ MCFGEtop
abbrev MCFGEbot [Params] := ExternalCallE ⊕ₑ OOME ⊕ₑ LLVMExcE ⊕ₑ UBE ⊕ₑ DebugE ⊕ₑ FailureE
abbrev CFGEbot [Params] := CallE ⊕ₑ MCFGEbot
abbrev CFGtop [Params] := CTree CFGEtop NoChoice
abbrev MCFGtop [Params] := CTree MCFGEtop NoChoice
abbrev CFGbot [Params] := CTree CFGEbot NoChoice
abbrev MCFGbot [Params] := CTree MCFGEbot NoChoice

namespace Worker
variable {M : Effect → Effect → Type → Type v} [Runtime M]

def gwrite [Pa : Params] {E B : Effect} [GlobalE -< E] (id : raw_id) (dv : dvalue) : M E B (Unit) :=
  Runtime.emit (E := GlobalE) (GlobalWrite id dv)

def gread [Pa : Params] {E B : Effect} [GlobalE -< E] (id : raw_id) : M E B (dvalue) :=
  Runtime.emit (E := GlobalE) (GlobalRead id)

def lwrite [Pa : Params] {E B : Effect} [LocalE -< E] (id : raw_id) (dv : dvalue) : M E B (Unit) :=
  Runtime.emit (E := LocalE) (LocalWrite id dv)

def lread [Pa : Params] {E B : Effect} [LocalE -< E] (id : raw_id) : M E B (dvalue) :=
  Runtime.emit (E := LocalE) (LocalRead id)

def stack_push [Pa : Params] {E B : Effect} [StackE -< E] (args : List (raw_id × dvalue)) : M E B (Unit) :=
  Runtime.emit (E := StackE) (StackPush args)

def stack_pop [Pa : Params] {E B : Effect} [StackE -< E] : M E B (Unit) :=
  Runtime.emit (E := StackE) (StackPop)

def stack_raise [Pa : Params] {E B : Effect} [StackE -< E] (x : exc) : M E B (Unit) :=
  Runtime.emit (E := StackE) (StackRaise x)

def stack_get_exc [Pa : Params] {E B : Effect} [StackE -< E] : M E B (Option exc) :=
  Runtime.emit (E := StackE) (StackGetExc)

def mem_push [Pa : Params] {E B : Effect} [MemoryE -< E] : M E B (Unit) :=
  Runtime.emit (E := MemoryE) (MemPush)

def mem_pop [Pa : Params] {E B : Effect} [MemoryE -< E] : M E B (Unit) :=
  Runtime.emit (E := MemoryE) (MemPop)

def alloca [Pa : Params] {E B : Effect} [MemoryE -< E] (t : dtyp) (num_elements : Nat) (align : Option Nat) : M E B (dvalue) :=
  Runtime.emit (E := MemoryE) (Alloca t num_elements align)

def load [Pa : Params] {E B : Effect} [MemoryE -< E] (t : dtyp) (a : dvalue) : M E B (dvalue) :=
  Runtime.emit (E := MemoryE) (Load t a)

def store [Pa : Params] {E B : Effect} [MemoryE -< E] (t : dtyp) (a : dvalue) (v : dvalue) : M E B (Unit) :=
  Runtime.emit (E := MemoryE) (Store t a v)

def conv [Pa : Params] {E B : Effect} [MemoryE -< E] (cv : impure_conversion) (t_from : dtyp) (v : dvalue) (t_to : dtyp) : M E B (dvalue) :=
  Runtime.emit (E := MemoryE) (Conv cv t_from v t_to)

def draw [Pa : Params] {E B : Effect} [DrawE -< E] (t : dtyp) : M E B (dvalue) :=
  Runtime.emit (E := DrawE) (Draw t)

def call [Pa : Params] {E B : Effect} [CallE -< E] (t : dtyp) (cc : cconv) (f : dvalue) (args : List (dtyp × dvalue)) : M E B (exc ⊕ dvalue) :=
  Runtime.emit (E := CallE) (Call t cc f args)

def external_call [Pa : Params] {E B : Effect} [ExternalCallE -< E] (t : dtyp) (f : dvalue) (args : List (dtyp × dvalue)) : M E B (dvalue) :=
  Runtime.emit (E := ExternalCallE) (ExternalCall t f args)

def io_stdout [Pa : Params] {E B : Effect} [ExternalCallE -< E] (bytes : List VellvmIntegers.int8) : M E B (Unit) :=
  Runtime.emit (E := ExternalCallE) (IO_stdout bytes)

def io_stderr [Pa : Params] {E B : Effect} [ExternalCallE -< E] (bytes : List VellvmIntegers.int8) : M E B (Unit) :=
  Runtime.emit (E := ExternalCallE) (IO_stderr bytes)

def intrinsic [Pa : Params] {E B : Effect} [IntrinsicE -< E] (t : dtyp) (f : IRString) (args : List (dtyp × dvalue)) (vararg : Option Pa.PTR.ptr) : M E B (exc ⊕ dvalue) :=
  Runtime.emit (E := IntrinsicE) (Intrinsic t f args vararg)

def withCall [Params] {B X} (t : M MCFGEtop B X) : M CFGEtop B X :=
  Runtime.translate (fun e ↦ ⟨.inr e, id⟩) t

def raiseLLVM [Params] {E B X} [LLVMExcE -< E] (x : exc) : M E B X := do
  nomatch (← Runtime.emit (E := LLVMExcE) (LLVMExc x) : Empty)

variable [Instrumentation.Diagnostics M]

def raiseUB {E B X} [UBE -< E] (msg : IRString) : M E B X := do
  Instrumentation.Diagnostics.diagnostic msg
  nomatch (← Runtime.emit (E := UBE) (ThrowUB ()) : Empty)

def «raise» {E B X} [FailureE -< E] (msg : IRString) : M E B X := do
  Instrumentation.Diagnostics.diagnostic msg
  nomatch (← Runtime.emit (E := FailureE) (Throw ()) : Empty)

def raiseOOM {E B X} [OOME -< E] (msg : IRString) : M E B X := do
  Instrumentation.Diagnostics.diagnostic msg
  nomatch (← Runtime.emit (E := OOME) (ThrowOOM ()) : Empty)

def debug {E B} [DebugE -< E] (msg : IRString) : M E B Unit := do
  Instrumentation.Diagnostics.diagnostic msg
  Runtime.emit (E := DebugE) (Debug ())

def EOU_to_itree {E B X} [FailureE -< E] [OOME -< E] [UBE -< E] : EOU.EOU X → M E B X
  | .raise_error msg => «raise» msg
  | .raise_ub msg => raiseUB msg
  | .raise_oom msg => raiseOOM msg
  | .raise_ret x => pure x

end Worker

def gwrite [Pa : Params] {E B : Effect} [GlobalE -< E] (id : raw_id) (dv : dvalue) : CTree E B (Unit) :=
  Worker.gwrite (M := CTree) id dv

def gread [Pa : Params] {E B : Effect} [GlobalE -< E] (id : raw_id) : CTree E B (dvalue) :=
  Worker.gread (M := CTree) id

def lwrite [Pa : Params] {E B : Effect} [LocalE -< E] (id : raw_id) (dv : dvalue) : CTree E B (Unit) :=
  Worker.lwrite (M := CTree) id dv

def lread [Pa : Params] {E B : Effect} [LocalE -< E] (id : raw_id) : CTree E B (dvalue) :=
  Worker.lread (M := CTree) id

def stack_push [Pa : Params] {E B : Effect} [StackE -< E] (args : List (raw_id × dvalue)) : CTree E B (Unit) :=
  Worker.stack_push (M := CTree) args

def stack_pop [Pa : Params] {E B : Effect} [StackE -< E] : CTree E B (Unit) :=
  Worker.stack_pop (M := CTree)

def stack_raise [Pa : Params] {E B : Effect} [StackE -< E] (x : exc) : CTree E B (Unit) :=
  Worker.stack_raise (M := CTree) x

def stack_get_exc [Pa : Params] {E B : Effect} [StackE -< E] : CTree E B (Option exc) :=
  Worker.stack_get_exc (M := CTree)

def mem_push [Pa : Params] {E B : Effect} [MemoryE -< E] : CTree E B (Unit) :=
  Worker.mem_push (M := CTree)

def mem_pop [Pa : Params] {E B : Effect} [MemoryE -< E] : CTree E B (Unit) :=
  Worker.mem_pop (M := CTree)

def alloca [Pa : Params] {E B : Effect} [MemoryE -< E] (t : dtyp) (num_elements : Nat) (align : Option Nat) : CTree E B (dvalue) :=
  Worker.alloca (M := CTree) t num_elements align

def load [Pa : Params] {E B : Effect} [MemoryE -< E] (t : dtyp) (a : dvalue) : CTree E B (dvalue) :=
  Worker.load (M := CTree) t a

def store [Pa : Params] {E B : Effect} [MemoryE -< E] (t : dtyp) (a : dvalue) (v : dvalue) : CTree E B (Unit) :=
  Worker.store (M := CTree) t a v

def conv [Pa : Params] {E B : Effect} [MemoryE -< E] (cv : impure_conversion) (t_from : dtyp) (v : dvalue) (t_to : dtyp) : CTree E B (dvalue) :=
  Worker.conv (M := CTree) cv t_from v t_to

def draw [Pa : Params] {E B : Effect} [DrawE -< E] (t : dtyp) : CTree E B (dvalue) :=
  Worker.draw (M := CTree) t

def call [Pa : Params] {E B : Effect} [CallE -< E] (t : dtyp) (cc : cconv) (f : dvalue) (args : List (dtyp × dvalue)) : CTree E B (exc ⊕ dvalue) :=
  Worker.call (M := CTree) t cc f args

def external_call [Pa : Params] {E B : Effect} [ExternalCallE -< E] (t : dtyp) (f : dvalue) (args : List (dtyp × dvalue)) : CTree E B (dvalue) :=
  Worker.external_call (M := CTree) t f args

def io_stdout [Pa : Params] {E B : Effect} [ExternalCallE -< E] (bytes : List VellvmIntegers.int8) : CTree E B (Unit) :=
  Worker.io_stdout (M := CTree) bytes

def io_stderr [Pa : Params] {E B : Effect} [ExternalCallE -< E] (bytes : List VellvmIntegers.int8) : CTree E B (Unit) :=
  Worker.io_stderr (M := CTree) bytes

def intrinsic [Pa : Params] {E B : Effect} [IntrinsicE -< E] (t : dtyp) (f : IRString) (args : List (dtyp × dvalue)) (vararg : Option Pa.PTR.ptr) : CTree E B (exc ⊕ dvalue) :=
  Worker.intrinsic (M := CTree) t f args vararg

def withCall [Params] {X} (t : MCFGtop X) : CFGtop X := Worker.withCall (M := CTree) t

def raiseLLVM [Params] {E B X} [LLVMExcE -< E] (x : exc) : CTree E B X := Worker.raiseLLVM x
def raiseUB {E B X} [UBE -< E] (msg : IRString) : CTree E B X := Worker.raiseUB msg
def «raise» {E B X} [FailureE -< E] (msg : IRString) : CTree E B X := Worker.«raise» msg
def raiseOOM {E B X} [OOME -< E] (msg : IRString) : CTree E B X := Worker.raiseOOM msg
def debug {E B} [DebugE -< E] (msg : IRString) : CTree E B Unit := Worker.debug msg

def EOU_to_itree {E B X} [FailureE -< E] [OOME -< E] [UBE -< E] (x : EOU.EOU X) : CTree E B X :=
  Worker.EOU_to_itree x

end Vellvm.Semantics.LLVMEvents
