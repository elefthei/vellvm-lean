import Vellvm.Semantics.Denotation.Basic
import Vellvm.Semantics.Attributes.Values
import Vellvm.Semantics.Operations.Compare
import Vellvm.Semantics.Operations.Conversion
import Vellvm.Semantics.Operations.Freeze
import Vellvm.Semantics.Operations.Gep
import Vellvm.Semantics.Operations.Select
import Vellvm.Semantics.Simulation
import Vellvm.Semantics.VellvmFloats

namespace Vellvm.Semantics.Denotation
open Interfaces.Params DynamicValues Syntax.DynamicTypes Syntax.LLVMAst
open LLVMEvents Vellvm.Tree EOU

variable [Pa : Params]

def denote_float_syntax_as_float (t : dtyp) (f : float_syntax) : EOU dvalue :=
  match t with
  | .DTYPE_Base (.DTYPE_FP .FP_float) =>
    match VellvmFloats.float32_of_float_syntax f with
    | some x => pure (DVALUE_Base (DVALUE_Float x))
    | none => raise_error ("bad float literal: ".toUTF8 ++ Syntax.ShowAST.show_float_syntax f)
  | .DTYPE_Base (.DTYPE_FP .FP_double) =>
    match VellvmFloats.float_of_float_syntax f with
    | some x => pure (DVALUE_Base (DVALUE_Double x))
    | none => raise_error ("bad double literal: ".toUTF8 ++ Syntax.ShowAST.show_float_syntax f)
  | .DTYPE_Base (.DTYPE_FP _) => raise_error "unsupported float type".toUTF8
  | _ => raise_error "bad type for constant float".toUTF8

def denote_int_syntax_as_int (t : dtyp) (x : int_syntax) : EOU dvalue :=
  match t with
  | .DTYPE_Base (.DTYPE_I w) =>
    DVALUE_Base <$> coerce_integer_to_int (some w) (Attributes.denote_int_syntax x)
  | .DTYPE_Base .DTYPE_Iptr =>
    DVALUE_Base <$> coerce_integer_to_int none (Attributes.denote_int_syntax x)
  | .DTYPE_Base (.DTYPE_B w) =>
    pure (DVALUE_Base (DVALUE_B w (BYTE_I (Numeric.Integers.repr (Attributes.denote_int_syntax x)))))
  | _ => raise_error ("bad type for constant int: ".toUTF8 ++ Syntax.ShowAST.show_dtyp t)

def assert_packed_struct_typ : Option dtyp → EOU Unit
  | none => raise_error "denote_exp given untyped EXP_Struct".toUTF8
  | some (.DTYPE_Struct true _) => pure ()
  | some _ => raise_error "bad type for VALUE_Packed_struct".toUTF8

def assert_vector_typ : Option dtyp → EOU (Nat × dtyp)
  | none => raise_error "denote_exp given untyped EXP_Splat".toUTF8
  | some (.DTYPE_Array true sz t) => pure (sz, t)
  | some _ => raise_error "denote_exp given EXP_Splat with non-vector type".toUTF8

def array_typ_of_texps (vector : Bool) (es : List (texp dtyp)) : dtyp :=
  .DTYPE_Array vector es.length (match es with | (t, _) :: _ => t | [] => .DTYPE_Base .DTYPE_Void)

namespace Worker
variable {M : ITree.Effect → ITree.Effect → Type → Type v} [Runtime M]

def lookup_id : «ident» → M MCFGEtop NoChoice dvalue
  | .ID_Global x => LLVMEvents.Worker.gread x
  | .ID_Local x => LLVMEvents.Worker.lread x

variable [Instrumentation.Diagnostics M]

private abbrev liftEOU {X} (x : EOU X) : M MCFGEtop NoChoice X := LLVMEvents.Worker.EOU_to_itree x

mutual
  def denote_exp (top : Option dtyp) : exp dtyp → M MCFGEtop NoChoice dvalue
    | .EXP_Ident i => lookup_id i
    | .EXP_BlockAddress f b => LLVMEvents.Worker.gread (blockaddress_id f b)
    | .EXP_Integer x => match top with
      | none => LLVMEvents.Worker.«raise» "denote_exp given untyped EXP_Integer".toUTF8
      | some t => liftEOU (denote_int_syntax_as_int t x)
    | .EXP_Float x => match top with
      | none => LLVMEvents.Worker.«raise» "denote_exp given untyped EXP_Float".toUTF8
      | some t => liftEOU (denote_float_syntax_as_float t x)
    | .EXP_Bool b =>
      pure (DVALUE_Base (DVALUE_I ⟨1, by decide⟩
        (if b then Numeric.Integers.one else Numeric.Integers.zero)))
    | .EXP_Null | .EXP_Metadata .METADATA_Null => pure (DVALUE_Base (DVALUE_Pointer Pa.PTR.null))
    | .EXP_Zero_initializer => match top with
      | none => LLVMEvents.Worker.«raise» "denote_exp given untyped EXP_Zero_initializer".toUTF8
      | some t => liftEOU (default_dvalue_of_dtyp t)
    | .EXP_Cstring es => do return DVALUE_Array false (← denote_texps es)
    | .EXP_Undef | .EXP_Poison => pure (match top with
      | some t => poison_of_dtyp t
      | none => DVALUE_Base DVALUE_Poison)
    | .EXP_Struct es => do
      let vs ← denote_texps es
      return canonicalize_agg (DTYPE_Struct false (es.map Prod.fst)) vs
    | .EXP_Packed_struct es => do
      liftEOU (assert_packed_struct_typ top)
      let vs ← denote_texps es
      return canonicalize_agg (DTYPE_Struct true (es.map Prod.fst)) vs
    | .EXP_Array es => do return canonicalize_agg (array_typ_of_texps false es) (← denote_texps es)
    | .EXP_Vector es => do return canonicalize_agg (array_typ_of_texps true es) (← denote_texps es)
    | .OP_IBinop op t x y => do
      liftEOU (eval_iop op t (← denote_exp (some t) x) (← denote_exp (some t) y))
    | .OP_ICmp ss op t x y => do
      liftEOU (Operations.Compare.eval_icmp ss op t (← denote_exp (some t) x) (← denote_exp (some t) y))
    | .OP_FBinop op _ t x y => do
      liftEOU (eval_fop op t (← denote_exp (some t) x) (← denote_exp (some t) y))
    | .OP_Fneg _ x => do liftEOU (eval_fneg x.1 (← denote_texp x))
    | .OP_FCmp op _ t x y => do
      liftEOU (eval_fcmp op t (← denote_exp (some t) x) (← denote_exp (some t) y))
    | .OP_Conversion op s x t => do
      Operations.Conversion.Worker.convert op s (← denote_exp (some s) x) t
    | .OP_GetElementPtr flags t p is => do
      liftEOU (Operations.Gep.eval_gep flags t (← denote_texp p) (← denote_texps is))
    | .OP_ExtractElement v i => do liftEOU (extract_element (← denote_texp v) (← denote_texp i))
    | .OP_InsertElement v e i => do
      let vec ← denote_texp v
      let elt ← liftEOU (dvalue_to_dvalue_base (← denote_texp e))
      liftEOU (insert_element v.1 vec (DVALUE_Base elt) (← denote_texp i))
    | .OP_ShuffleVector v w m => do
      liftEOU (shuffle_vector v.1 (← denote_texp v) (← denote_texp w) (← denote_texp m))
    | .OP_ExtractValue v is => do
      liftEOU (extract_value v.1 (← denote_texp v) (is.map Attributes.denote_int_syntax))
    | .OP_InsertValue v e is => do
      liftEOU (insert_value v.1 (← denote_texp v) (← denote_texp e) (is.map Attributes.denote_int_syntax))
    | .OP_Select _ c x y => do
      liftEOU (Operations.Select.eval_select (← denote_texp c) x.1 (← denote_texp x) (← denote_texp y))
    | .EXP_Metadata (.METADATA_Const x) => denote_texp x
    | .EXP_Metadata _ => pure NONE
    | .EXP_Asm _ _ _ _ template _ =>
      LLVMEvents.Worker.«raise» ("denote_exp encountered inlined asm template ".toUTF8 ++ template)
    | .EXP_Splat elt => do
      let (sz, t) ← liftEOU (assert_vector_typ top)
      let v ← denote_texp elt
      return canonicalize_agg (DTYPE_Array true sz t) (List.replicate sz v)
    | .OP_Freeze x => do Operations.Freeze.Worker.freeze x.1 (← denote_texp x)
  termination_by structural e => e

  def denote_texp : texp dtyp → M MCFGEtop NoChoice dvalue
    | (t, e) => denote_exp (some t) e
  termination_by structural x => x

  def denote_texps : List (texp dtyp) → M MCFGEtop NoChoice (List dvalue)
    | [] => pure []
    | x :: xs => do return (← denote_texp x) :: (← denote_texps xs)
  termination_by structural xs => xs
end

theorem denote_texps_eq_map_monad (es : List (texp dtyp)) :
    denote_texps (M := M) es = Utils.ListUtil.map_monad denote_texp es := by
  induction es with
  | nil => rfl
  | cons x xs ih => rw [denote_texps, Utils.ListUtil.map_monad, ih]

def denote_exp' (t : Option dtyp) (e : exp dtyp) : M CFGEtop NoChoice dvalue :=
  LLVMEvents.Worker.withCall (denote_exp t e)

variable {N : ITree.Effect → ITree.Effect → Type → Type w} [Runtime N]
variable [Instrumentation.Diagnostics N] [Instrumentation.Snapshots M] [Instrumentation.Snapshots N]
variable (sim : Simulation M N)

theorem lookup_id_related (i : «ident») : sim.R (lookup_id i) (lookup_id i) := by
  cases i with
  | ID_Global x => exact sim.gread x
  | ID_Local x => exact sim.lread x

mutual
  theorem denote_exp_related (top : Option dtyp) (e : exp dtyp) :
      sim.R (denote_exp top e) (denote_exp top e) := by
    cases e
    case EXP_Ident i => exact lookup_id_related sim i
    case EXP_BlockAddress f b => exact sim.gread (blockaddress_id f b)
    case EXP_Integer => cases top <;> first | exact sim.liftEOU _ | exact sim.«raise» _
    case EXP_Float => cases top <;> first | exact sim.liftEOU _ | exact sim.«raise» _
    case EXP_Zero_initializer => cases top <;> first | exact sim.liftEOU _ | exact sim.«raise» _
    case EXP_Asm => exact sim.«raise» _
    case EXP_Metadata md =>
      cases md <;> first | exact sim.pure _ | exact denote_texp_related _
    case EXP_Splat elt =>
      exact sim.bind (sim.liftEOU _) fun (sz, t) ↦
        sim.bind (denote_texp_related elt) fun _ ↦ sim.pure _
    all_goals simp only [denote_exp]
    all_goals
      repeat' first
        | exact sim.pure _
        | exact sim.liftEOU _
        | exact Operations.Conversion.Worker.convert_congr sim _ _ _ _
        | exact Operations.Freeze.Worker.freeze_congr sim _ _
        | exact denote_exp_related _ _
        | exact denote_texp_related _
        | exact denote_texps_related _
        | apply sim.bind
        | intro
  termination_by structural e

  theorem denote_texp_related (x : texp dtyp) :
      sim.R (denote_texp x) (denote_texp x) := by
    cases x with | mk t e => exact denote_exp_related (some t) e
  termination_by structural x

  theorem denote_texps_related (xs : List (texp dtyp)) :
      sim.R (denote_texps xs) (denote_texps xs) := by
    cases xs with
    | nil => exact sim.pure []
    | cons x xs =>
      exact sim.bind (denote_texp_related x) fun _ ↦
        sim.bind (denote_texps_related xs) fun _ ↦ sim.pure _
  termination_by structural xs
end

theorem denote_exp'_related (t : Option dtyp) (e : exp dtyp) :
    sim.R (denote_exp' t e) (denote_exp' t e) :=
  sim.withCall (denote_exp_related sim t e)

end Worker

def lookup_id (i : «ident») : MCFGtop dvalue := Worker.lookup_id (M := CTree.CTree) i

def denote_exp (top : Option dtyp) (e : exp dtyp) : MCFGtop dvalue :=
  Worker.denote_exp (M := CTree.CTree) top e

def denote_closed_exp (t : dtyp) (e : exp dtyp) : Option dvalue :=
  match (denote_exp (some t) e).unfold with
  | .ret v => some v
  | _ => none

def denote_exp' (t : Option dtyp) (e : exp dtyp) : CFGtop dvalue :=
  Worker.denote_exp' (M := CTree.CTree) t e

end Vellvm.Semantics.Denotation
