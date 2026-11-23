import PortChecks.SourceType
import Vellvm.Theory.I2F.I2F_toplevel.Initialization

namespace PortChecks.I2FToplevelInitialization
open Vellvm Vellvm.Syntax.LLVMAst Vellvm.Syntax.DynamicTypes Vellvm.Semantics.TopLevel
open Vellvm.Theory.I2F.Refinement Vellvm.Theory.I2F.I2F_toplevel

#source_check "src/rocq/Theory/I2F/I2F_toplevel.v|Vellvm.Theory.I2F.I2F_toplevel|I2F_allocate_global"
  I2F_allocate_global : ∀ g : «global» dtyp, I2F_refine_MCFG (fun _ _ : Unit ↦ True)
    (@allocate_global PInf g) (@allocate_global PFin g)

#source_check "src/rocq/Theory/I2F/I2F_toplevel.v|Vellvm.Theory.I2F.I2F_toplevel|I2F_allocate_globals"
  I2F_allocate_globals : ∀ gs : List («global» dtyp), I2F_refine_MCFG (fun _ _ : Unit ↦ True)
    (@allocate_globals PInf gs) (@allocate_globals PFin gs)

#source_check "src/rocq/Theory/I2F/I2F_toplevel.v|Vellvm.Theory.I2F.I2F_toplevel|I2F_allocate_declaration"
  I2F_allocate_declaration : ∀ d : declaration dtyp, I2F_refine_MCFG (fun _ _ : Unit ↦ True)
    (@allocate_declaration PInf d) (@allocate_declaration PFin d)

#source_check "src/rocq/Theory/I2F/I2F_toplevel.v|Vellvm.Theory.I2F.I2F_toplevel|I2F_allocate_declarations"
  I2F_allocate_declarations : ∀ ds : List (declaration dtyp), I2F_refine_MCFG (fun _ _ : Unit ↦ True)
    (@allocate_declarations PInf ds) (@allocate_declarations PFin ds)

#source_check "src/rocq/Theory/I2F/I2F_toplevel.v|Vellvm.Theory.I2F.I2F_toplevel|I2F_allocate_block_address"
  I2F_allocate_block_address : ∀ fb : function_id × block_id, I2F_refine_MCFG (fun _ _ : Unit ↦ True)
    (@allocate_block_address PInf fb) (@allocate_block_address PFin fb)

#source_check "src/rocq/Theory/I2F/I2F_toplevel.v|Vellvm.Theory.I2F.I2F_toplevel|I2F_allocate_block_addresses"
  I2F_allocate_block_addresses : ∀ fbs : List (function_id × block_id), I2F_refine_MCFG (fun _ _ : Unit ↦ True)
    (@allocate_block_addresses PInf fbs) (@allocate_block_addresses PFin fbs)

#source_check "src/rocq/Theory/I2F/I2F_toplevel.v|Vellvm.Theory.I2F.I2F_toplevel|I2F_initialize_global"
  I2F_initialize_global : ∀ g : «global» dtyp, I2F_refine_MCFG (fun _ _ : Unit ↦ True)
    (@initialize_global PInf g) (@initialize_global PFin g)

#source_check "src/rocq/Theory/I2F/I2F_toplevel.v|Vellvm.Theory.I2F.I2F_toplevel|I2F_initialize_globals"
  I2F_initialize_globals : ∀ gs : List («global» dtyp), I2F_refine_MCFG (fun _ _ : Unit ↦ True)
    (@initialize_globals PInf gs) (@initialize_globals PFin gs)

#source_check "src/rocq/Theory/I2F/I2F_toplevel.v|Vellvm.Theory.I2F.I2F_toplevel|I2F_build_global_environment"
  I2F_build_global_environment : ∀ m : Syntax.CFG.mcfg dtyp, I2F_refine_MCFG (fun _ _ : Unit ↦ True)
    (@build_global_environment PInf m) (@build_global_environment PFin m)

#source_check "src/rocq/Theory/I2F/I2F_toplevel.v|Vellvm.Theory.I2F.I2F_toplevel|I2F_i8_array_of_string"
  I2F_i8_array_of_string : ∀ s : IRString, I2F_dvalue (@i8_array_of_string PInf s) (@i8_array_of_string PFin s)

#source_check "src/rocq/Theory/I2F/I2F_toplevel.v|Vellvm.Theory.I2F.I2F_toplevel|I2F_allocate_arg"
  I2F_allocate_arg : ∀ arg : IRString, I2F_refine_MCFG I2F_dvalue (@allocate_arg PInf arg) (@allocate_arg PFin arg)

#source_check "src/rocq/Theory/I2F/I2F_toplevel.v|Vellvm.Theory.I2F.I2F_toplevel|I2F_allocate_args"
  I2F_allocate_args : ∀ args : List IRString, I2F_refine_MCFG I2F_dvalue (@allocate_args PInf args) (@allocate_args PFin args)

#source_check "src/rocq/Theory/I2F/I2F_toplevel.v|Vellvm.Theory.I2F.I2F_toplevel|I2F_build_main_args"
  I2F_build_main_args : ∀ args : List IRString, I2F_refine_MCFG I2F_targs (@build_main_args PInf args) (@build_main_args PFin args)

end PortChecks.I2FToplevelInitialization
