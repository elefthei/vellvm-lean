import Vellvm.Numeric.Floats.Basic
import Vellvm.Semantics.LLVMEvents
import Vellvm.Semantics.MemoryBytes
import Vellvm.Semantics.Simulation

namespace Vellvm.Semantics.Operations.Conversion
open Interfaces.Params DynamicValues EOU Syntax.DynamicTypes Syntax.LLVMAst Numeric
open Numeric.Integers Utils.ListUtil

variable [Pa : Params]

def float_to_double : ll_float → ll_double := Floats.Float.of_single
def double_to_float : ll_double → ll_float := Floats.Float.to_single

private def floatToInt {p e} (f : Flocq.binary_float p e) (w : Positive)
    (isSigned : Bool) : EOU dvalue_base :=
  let lo := if isSigned then @min_signed w else 0
  let hi := if isSigned then @max_signed w else @max_unsigned w
  pure <| match IEEE754_extra.ZofB_range p e f lo hi with
    | none => DVALUE_Poison
    | some z => DVALUE_I w (Integers.repr z)

def convert_pure_base (c : pure_conversion) (t : dtyp_base) (x : dvalue_base)
    (u : dtyp_base) : EOU dvalue_base :=
  match c, t, x, u with
  | .Trunc nuw nsw, .DTYPE_I a, .DVALUE_I b i, .DTYPE_I w =>
    if a.val == b.val && w.val < b.val then
      let r := @Integers.repr w (unsigned i)
      if (nuw && unsigned r != unsigned i) || (nsw && signed r != signed i) then pure DVALUE_Poison
      else pure (DVALUE_I w r)
    else raise_error "i-to-i ill-typed Trunc".toUTF8
  | .Zext nneg, .DTYPE_I a, .DVALUE_I b i, .DTYPE_I w =>
    if a.val == b.val && b.val < w.val then
      if nneg && signed i < 0 then pure DVALUE_Poison else pure (DVALUE_I w (Integers.repr (unsigned i)))
    else raise_error "i-to-i ill-typed Zext".toUTF8
  | .Sext, .DTYPE_I a, .DVALUE_I b i, .DTYPE_I w =>
    if a.val == b.val && b.val < w.val then pure (DVALUE_I w (Integers.repr (signed i)))
    else raise_error "i-to-i ill-typed Sext".toUTF8
  | .Uitofp nneg, .DTYPE_I a, .DVALUE_I b i, .DTYPE_FP .FP_float =>
    if a.val != b.val then raise_error "i-to-float ill-typed Uitofp".toUTF8
    else if nneg && signed i < 0 then pure DVALUE_Poison
    else pure (DVALUE_Float (Floats.Float32.of_intu (Integers.repr (unsigned i))))
  | .Uitofp nneg, .DTYPE_I a, .DVALUE_I b i, .DTYPE_FP .FP_double =>
    if a.val != b.val then raise_error "i-to-double ill-typed Uitofp".toUTF8
    else if nneg && signed i < 0 then pure DVALUE_Poison
    else pure (DVALUE_Double (Floats.Float.of_longu (Integers.repr (unsigned i))))
  | .Sitofp, .DTYPE_I a, .DVALUE_I b i, .DTYPE_FP .FP_float =>
    if a.val == b.val then pure (DVALUE_Float (Floats.Float32.of_int (Integers.repr (signed i))))
    else raise_error "i-to-float ill-typed Sitofp".toUTF8
  | .Sitofp, .DTYPE_I a, .DVALUE_I b i, .DTYPE_FP .FP_double =>
    if a.val == b.val then pure (DVALUE_Double (Floats.Float.of_long (Integers.repr (signed i))))
    else raise_error "i-to-double ill-typed Sitofp".toUTF8
  | .Fptoui, .DTYPE_FP .FP_float, .DVALUE_Float f, .DTYPE_I w => floatToInt f w false
  | .Fptoui, .DTYPE_FP .FP_double, .DVALUE_Double f, .DTYPE_I w => floatToInt f w false
  | .Fptosi, .DTYPE_FP .FP_float, .DVALUE_Float f, .DTYPE_I w => floatToInt f w true
  | .Fptosi, .DTYPE_FP .FP_double, .DVALUE_Double f, .DTYPE_I w => floatToInt f w true
  | .Fpext _, .DTYPE_FP .FP_float, .DVALUE_Float f, .DTYPE_FP .FP_double => pure (DVALUE_Double (float_to_double f))
  | .Fptrunc _, .DTYPE_FP .FP_double, .DVALUE_Double f, .DTYPE_FP .FP_float => pure (DVALUE_Float (double_to_float f))
  | .Trunc .., .DTYPE_I _, .DVALUE_Poison, .DTYPE_I _
  | .Zext _, .DTYPE_I _, .DVALUE_Poison, .DTYPE_I _
  | .Sext, .DTYPE_I _, .DVALUE_Poison, .DTYPE_I _
  | .Uitofp _, .DTYPE_I _, .DVALUE_Poison, .DTYPE_FP _
  | .Sitofp, .DTYPE_I _, .DVALUE_Poison, .DTYPE_FP _
  | .Fptoui, .DTYPE_FP _, .DVALUE_Poison, .DTYPE_I _
  | .Fptosi, .DTYPE_FP _, .DVALUE_Poison, .DTYPE_I _
  | .Fpext _, .DTYPE_FP .FP_float, .DVALUE_Poison, .DTYPE_FP .FP_double
  | .Fptrunc _, .DTYPE_FP .FP_double, .DVALUE_Poison, .DTYPE_FP .FP_float => pure DVALUE_Poison
  | c, _, _, _ => raise_error ("ill-typed " ++ (match c with
      | .Trunc .. => "Trunc" | .Zext _ => "Zext" | .Sext => "Sext"
      | .Uitofp _ => "Uitofp" | .Sitofp => "Sitofp" | .Fptoui => "Fptoui"
      | .Fptosi => "Fptosi" | .Fpext _ => "Fpext" | .Fptrunc _ => "Fptrunc")).toUTF8

def get_base_conversion_type : dtyp → dtyp → Option (dtyp_base × dtyp_base)
  | .DTYPE_Base a, .DTYPE_Base b => some (a, b)
  | _, _ => none

def get_vector_conversion_type : dtyp → dtyp → Option (dtyp_base × dtyp_base)
  | .DTYPE_Array true n (.DTYPE_Base a), .DTYPE_Array true m (.DTYPE_Base b) =>
    if n == m then some (a, b) else none
  | _, _ => none

def convert_pure (c : pure_conversion) (t : dtyp) (v : dvalue) (u : dtyp) : EOU dvalue :=
  match t with
  | .DTYPE_Array true n _ =>
    match get_vector_conversion_type t u, vector_elts n v with
    | some (a, b), some lanes => do
      let xs ← map_monad dvalue_to_dvalue_base lanes
      let ys ← map_monad (fun x ↦ convert_pure_base c a x b) xs
      pure (canonicalize_agg u (ys.map DVALUE_Base))
    | none, _ => raise_error "convert_pure: type or vector size mismatch".toUTF8
    | _, none => raise_error "convert_pure: invalid input dvalue".toUTF8
  | _ => match v with
    | .DVALUE_Base x => match get_base_conversion_type t u with
      | some (a, b) => DVALUE_Base <$> convert_pure_base c a x b
      | none => raise_error "convert_pure: type mismatch".toUTF8
    | _ => raise_error "convert_pure: invalid input dvalue".toUTF8

open LLVMEvents MemoryBytes Vellvm.Tree

namespace Worker

def convert {M : ITree.Effect → ITree.Effect → Type → Type v} [Runtime M]
    [Instrumentation.Diagnostics M] {B : ITree.Effect} (c : conversion_type) (t : dtyp)
    (v : dvalue) (u : dtyp) : M MCFGEtop B dvalue :=
  match c with
  | .CONV_Bitcast =>
    if dtyp_eqb t u then pure v
    else if Pa.SIZE.bit_sizeof_dtyp t == Pa.SIZE.bit_sizeof_dtyp u then
      LLVMEvents.Worker.EOU_to_itree (do
        let bytes ← dvalue_to_memory_bytes t v none
        memory_bytes_to_dvalue bytes u)
    else LLVMEvents.Worker.«raise» "unequal bitsize in cast".toUTF8
  | .CONV_Pure c => LLVMEvents.Worker.EOU_to_itree (convert_pure c t v u)
  | .CONV_Impure c => LLVMEvents.Worker.conv c t v u

theorem convert_congr {M : ITree.Effect → ITree.Effect → Type → Type v}
    {N : ITree.Effect → ITree.Effect → Type → Type w} [Runtime M] [Runtime N]
    [Instrumentation.Diagnostics M] [Instrumentation.Diagnostics N]
    [Instrumentation.Snapshots M] [Instrumentation.Snapshots N]
    (s : Simulation M N) {B : ITree.Effect} (c : conversion_type) (t : dtyp)
    (v : dvalue) (u : dtyp) :
    s.R (convert (M := M) (B := B) c t v u) (convert (M := N) c t v u) := by
  cases c with
  | CONV_Bitcast =>
    simp only [convert]
    split
    · exact s.pure v
    · split
      · exact s.liftEOU _
      · exact s.«raise» _
  | CONV_Pure c => exact s.liftEOU _
  | CONV_Impure c => exact s.conv c t v u

end Worker

def convert (c : conversion_type) (t : dtyp) (v : dvalue) (u : dtyp) : MCFGtop dvalue :=
  Worker.convert (M := CTree.CTree) c t v u

end Vellvm.Semantics.Operations.Conversion
