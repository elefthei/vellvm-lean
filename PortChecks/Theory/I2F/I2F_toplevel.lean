import PortChecks.SourceType
import PortChecks.Theory.I2F.I2F_toplevel.Initialization
import PortChecks.Theory.I2F.I2F_toplevel.Libraries
import Vellvm.Theory.I2F.I2F_toplevel

open Vellvm Vellvm.Semantics Vellvm.Syntax Vellvm.Theory.I2F
open LLVMAst DynamicTypes DynamicValues Denotation LLVMEvents TopLevel
open Refinement I2F_denotation I2F_interp I2F_toplevel
open Utils.IntMaps Utils.RelationsUtil

#source_check "src/rocq/Theory/I2F/I2F_toplevel.v|Vellvm.Theory.I2F.I2F_toplevel|I2F_initial_FusedS"
  I2F_initial_FusedS : I2F_FusedS
    ((@Implementations.Memory.MemoryModelStateV PInf).initial_state,
      (@Handlers.Stack.Build_stack_frame PInf (RawIdMaps.RM.empty _) none none, []), RawIdMaps.RM.empty (@dvalue PInf))
    ((@Implementations.Memory.MemoryModelStateV PFin).initial_state,
      (@Handlers.Stack.Build_stack_frame PFin (RawIdMaps.RM.empty _) none none, []), RawIdMaps.RM.empty (@dvalue PFin))

#source_check "src/rocq/Theory/I2F/I2F_toplevel.v|Vellvm.Theory.I2F.I2F_toplevel|I2F_address_one_function"
  I2F_address_one_function : ∀ (df : definition dtyp (CFG.cfg dtyp)),
    I2F_refine_MCFG (prod_rel Eq I2F_function_denotation)
      (@address_one_function PInf df) (@address_one_function PFin df)

#source_check "src/rocq/Theory/I2F/I2F_toplevel.v|Vellvm.Theory.I2F.I2F_toplevel|I2F_address_one_library_function"
  I2F_address_one_library_function : ∀ (fid : function_id) {d₁ : @function_denotation PInf}
    {d₂ : @function_denotation PFin}, I2F_function_denotation d₁ d₂ →
    I2F_refine_MCFG (prod_rel Eq I2F_function_denotation)
      (@address_one_library_function PInf (fid, d₁)) (@address_one_library_function PFin (fid, d₂))

#source_check "src/rocq/Theory/I2F/I2F_toplevel.v|Vellvm.Theory.I2F.I2F_toplevel|I2F_ctx_of_list"
  I2F_ctx_of_list : ∀ {l₁ : List (Int × @function_denotation PInf)}
    {l₂ : List (Int × @function_denotation PFin)},
    List.Forall₂ (prod_rel Eq I2F_function_denotation) l₁ l₂ →
    I2F_ctx (IP.of_list l₁) (IP.of_list l₂)

#source_check "src/rocq/Theory/I2F/I2F_toplevel.v|Vellvm.Theory.I2F.I2F_toplevel|I2F_denote_vellvm"
  I2F_denote_vellvm : ∀ (ret_typ : dtyp) (entry : function_id)
    {args₁ : List (dtyp × @dvalue PInf)} {args₂ : List (dtyp × @dvalue PFin)}
    (mcfg : CFG.mcfg dtyp), I2F_targs args₁ args₂ → I2F_refine_MCFG I2F_dvalue
      (@denote_vellvm PInf ret_typ entry args₁ mcfg) (@denote_vellvm PFin ret_typ entry args₂ mcfg)

#source_check "src/rocq/Theory/I2F/I2F_toplevel.v|Vellvm.Theory.I2F.I2F_toplevel|I2F_interpreter_gen"
  I2F_interpreter_gen : ∀ (ret_typ : dtyp) (entry : function_id)
    {arg_gen₁ : @MCFGtop PInf (List (dtyp × @dvalue PInf))}
    {arg_gen₂ : @MCFGtop PFin (List (dtyp × @dvalue PFin))} (prog : ll_toplevel_entities),
    I2F_refine_MCFG I2F_targs arg_gen₁ arg_gen₂ →
    I2F_refine_MCFGbot (prod_rel I2F_dvalue I2F_FusedS)
      (@interpreter_gen PInf ret_typ entry arg_gen₁ prog) (@interpreter_gen PFin ret_typ entry arg_gen₂ prog)

#source_check "src/rocq/Theory/I2F/I2F_toplevel.v|Vellvm.Theory.I2F.I2F_toplevel|I2F_interpreter_param"
  I2F_interpreter_param : ∀ (argv : List IRString) (prog : ll_toplevel_entities),
    I2F_refine_MCFGbot (prod_rel I2F_dvalue I2F_FusedS)
      (@interpreter_param PInf argv prog) (@interpreter_param PFin argv prog)
