import PortChecks.SourceType
import Vellvm.Theory.I2F.I2F_toplevel.Libraries

open Vellvm.Syntax.LLVMAst Vellvm.Syntax.DynamicTypes
open Vellvm.Semantics.Libraries Vellvm.Utils.RelationsUtil
open Vellvm.Theory.I2F.Refinement Vellvm.Theory.I2F.I2F_denotation
open Vellvm.Theory.I2F.I2F_toplevel

#source_check "src/rocq/Theory/I2F/I2F_toplevel.v|Vellvm.Theory.I2F.I2F_toplevel|I2F_putchar_denotation"
  I2F_putchar_denotation : I2F_function_denotation (@putchar_denotation PInf) (@putchar_denotation PFin)

#source_check "src/rocq/Theory/I2F/I2F_toplevel.v|Vellvm.Theory.I2F.I2F_toplevel|I2F_i8_str_index"
  I2F_i8_str_index : ∀ (p : PInf.PTR.ptr) (q : PFin.PTR.ptr) (i : Int),
    I2F_Addr p q → I2F_refine_CFG Eq (@i8_str_index PInf p i) (@i8_str_index PFin q i)

#source_check "src/rocq/Theory/I2F/I2F_toplevel.v|Vellvm.Theory.I2F.I2F_toplevel|I2F_puts_denotation"
  I2F_puts_denotation : I2F_function_denotation (@puts_denotation PInf) (@puts_denotation PFin)

#source_check "src/rocq/Theory/I2F/I2F_toplevel.v|Vellvm.Theory.I2F.I2F_toplevel|I2F_LIBRARIES"
  I2F_LIBRARIES : List.Forall₂ (prod_rel Eq I2F_function_denotation) (@_LIBRARIES PInf) (@_LIBRARIES PFin)

#source_check "src/rocq/Theory/I2F/I2F_toplevel.v|Vellvm.Theory.I2F.I2F_toplevel|I2F_library_functions"
  I2F_library_functions : ∀ ds : List (declaration dtyp),
    List.Forall₂ (prod_rel Eq I2F_function_denotation) (@library_functions PInf ds) (@library_functions PFin ds)
