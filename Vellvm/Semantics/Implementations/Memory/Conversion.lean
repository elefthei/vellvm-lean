import Vellvm.Semantics.DynamicValues.Arithmetic
import Vellvm.Semantics.Implementations.Memory.Bytes
import Vellvm.Semantics.LLVMEvents
import Vellvm.Semantics.Operations.Conversion

namespace Vellvm.Semantics.Implementations.Memory
open Interfaces.Params Interfaces.Memory DynamicValues Operations.Conversion
open Syntax.DynamicTypes Syntax.LLVMAst Utils.ListUtil

universe u v w z r
variable [Pa : Params] [MMP : MemoryModelPrimitives.{u,v,w,z,r}]

def assert_inttoptr_types_ok (t_from t_to : dtyp_base) : memM (MMS := MMP.mm_state) Unit :=
  match t_from, t_to with
  | .DTYPE_I _, .DTYPE_Pointer | .DTYPE_Iptr, .DTYPE_Pointer => pure ()
  | _, _ => mub "inttoptr: illegal type cast".toUTF8

def convert_impure_base (conv : impure_conversion) (t_from : dtyp_base) (dv : dvalue_base)
    (t_to : dtyp_base) : memM (MMS := MMP.mm_state) dvalue_base :=
  match conv with
  | .Inttoptr => do
    assert_inttoptr_types_ok t_from t_to
    match dv with
    | .DVALUE_Poison => pure DVALUE_Poison
    | _ => lift (DVALUE_Pointer <$> Pa.P2I.int_to_ptr (dvalue_base_int_unsigned dv)
        Pa.PROV.wildcard_prov)
  | .Ptrtoint | .Ptrtoaddr =>
    match dv, t_to with
    | .DVALUE_Pointer p, .DTYPE_I sz =>
      lift (coerce_integer_to_int (some sz) (Pa.P2I.ptr_to_int p))
    | .DVALUE_Pointer p, .DTYPE_Iptr => lift (coerce_integer_to_int none (Pa.P2I.ptr_to_int p))
    | .DVALUE_Poison, .DTYPE_I _ | .DVALUE_Poison, .DTYPE_Iptr => pure DVALUE_Poison
    | _, _ => mub "Invalid PTOI conversion".toUTF8
  | .Addrspacecast => merr "convert_impure: addrspacecast unimplemented".toUTF8

def convert_impure (conv : impure_conversion) (t_from : dtyp) (dv : dvalue) (t_to : dtyp) :
    memM (MMS := MMP.mm_state) dvalue :=
  match t_from with
  | .DTYPE_Array true sz _ =>
    match get_vector_conversion_type t_from t_to, vector_elts sz dv with
    | some (src, dst), some elts => do
      let bases ← lift (map_monad dvalue_to_dvalue_base elts)
      let lanes ← map_monad (fun v ↦ convert_impure_base conv src v dst) bases
      return canonicalize_agg t_to (lanes.map DVALUE_Base)
    | none, _ => merr "convert_impure: type or vector size mismatch".toUTF8
    | _, none => merr "convert_impure: invalid input dvalue".toUTF8
  | _ =>
    match dv with
    | .DVALUE_Base b =>
      match get_base_conversion_type t_from t_to with
      | some (src, dst) => DVALUE_Base <$> convert_impure_base conv src b dst
      | none => merr "convert_impure: type mismatch".toUTF8
    | _ => merr "convert_impure: invalid input dvalue".toUTF8

def handle_memoryM (e : LLVMEvents.MemoryRequest) :
    memM (MMS := MMP.mm_state) (LLVMEvents.MemoryE.O e) :=
  match e with
  | .MemPush => MMP.mempush
  | .MemPop => MMP.mempop
  | .Alloca t n align => do
    let alignment := match align with
      | none => (Pa.SIZE.dtyp_alignment t).preferred_alignment
      | some a => a
    let p ← allocate_dtyp t n alignment
    return DVALUE_Base (DVALUE_Pointer p)
  | .Load t (.DVALUE_Base (.DVALUE_Pointer p)) => read_dvalue t p
  | .Load _ _ => mub "Loading from something that isn't an address.".toUTF8
  | .Store t (.DVALUE_Base (.DVALUE_Pointer p)) v => write_dvalue p t v
  | .Store _ _ _ => mub "Writing something to somewhere that isn't an address.".toUTF8
  | .Conv conv t_from dv t_to => convert_impure conv t_from dv t_to

end Vellvm.Semantics.Implementations.Memory
