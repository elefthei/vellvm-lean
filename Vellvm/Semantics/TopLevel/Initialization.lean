import Vellvm.Semantics.Denotation.Expressions
import Vellvm.Semantics.IntrinsicsDefinitions.Families

namespace Vellvm.Semantics.TopLevel
open Interfaces.Params DynamicValues Syntax.DynamicTypes Syntax.LLVMAst
open LLVMEvents (MCFGEtop MCFGtop)
open Vellvm.Tree Utils.ListUtil

variable [Pa : Params]

def i8 : dtyp := .DTYPE_Base (.DTYPE_I ⟨8, by decide⟩)

def i8_array_of_string (s : IRString) : dvalue :=
  let byte (n : Nat) := DVALUE_Base (DVALUE_I ⟨8, by decide⟩ (Numeric.Integers.repr n))
  DVALUE_Array false (s.size.foldRev (fun i hi xs ↦ byte s[i].toNat :: xs) [byte 0])

def block_address_eq_dec (x y : function_id × block_id) : Decidable (x = y) := inferInstance

namespace Worker
open LLVMEvents.Worker (alloca store gwrite gread raiseUB)
variable {M : ITree.Effect → ITree.Effect → Type → Type v} [Runtime M] {B : ITree.Effect}

def allocate_global (g : «global» dtyp) : M MCFGEtop B Unit := do
  if g.g_alias then return ()
  gwrite g.g_ident (← alloca g.g_typ 1 none)

def allocate_globals (gs : List («global» dtyp)) : M MCFGEtop B Unit :=
  loop_monad allocate_global gs

def allocate_arg (arg : IRString) : M MCFGEtop B dvalue := do
  let len := arg.size + 1
  let v ← alloca i8 len none
  store (.DTYPE_Array false len i8) v (i8_array_of_string arg)
  return v

private def allocateArgv (args : List IRString) (len : Nat) : M MCFGEtop B dvalue := do
  let ptr : dtyp := .DTYPE_Base .DTYPE_Pointer
  let v ← alloca ptr len none
  let addrs ← map_monad allocate_arg args
  store (.DTYPE_Array false len ptr) v (DVALUE_Array false addrs)
  return v

def allocate_args (args : List IRString) : M MCFGEtop B dvalue :=
  allocateArgv args args.length

def build_main_args (args : List IRString) : M MCFGEtop B (List (dtyp × dvalue)) := do
  let argc := args.length
  let v ← allocateArgv args argc
  let w : Positive := ⟨32, by decide⟩
  return [(.DTYPE_Base (.DTYPE_I w), DVALUE_Base (DVALUE_I w (Numeric.Integers.repr argc))),
          (.DTYPE_Base .DTYPE_Pointer, v)]

def allocate_declaration (d : declaration dtyp) : M MCFGEtop B Unit := do
  if IntrinsicsDefinitions.is_intrinsic d.dc_name then return ()
  gwrite d.dc_name (← alloca (.DTYPE_Base .DTYPE_Pointer) 1 none)

def allocate_declarations (ds : List (declaration dtyp)) : M MCFGEtop B Unit :=
  loop_monad allocate_declaration ds

def allocate_block_address (fb : function_id × block_id) : M MCFGEtop B Unit := do
  gwrite (Denotation.blockaddress_id fb.1 fb.2) (← alloca i8 1 none)

def allocate_block_addresses (fbs : List (function_id × block_id)) : M MCFGEtop B Unit :=
  loop_monad allocate_block_address fbs

variable [Instrumentation.Diagnostics M]

def initialize_global (g : «global» dtyp) : M MCFGEtop NoChoice Unit := do
  if g.g_alias then
    match g.g_exp with
    | some (.EXP_Ident (.ID_Global src)) => gwrite g.g_ident (← gread src)
    | some _ => raiseUB ("alias ".toUTF8 ++ Syntax.ShowAST.show_raw_id g.g_ident ++
        " has bad initializer expression".toUTF8)
    | none => raiseUB ("alias ".toUTF8 ++ Syntax.ShowAST.show_raw_id g.g_ident ++
        " not initialized".toUTF8)
  else
    let a ← gread g.g_ident
    let v ← match g.g_exp with
      | none => pure (poison_of_dtyp g.g_typ)
      | some e => Denotation.Worker.denote_exp (some g.g_typ) e
    store g.g_typ a v

def initialize_globals (gs : List («global» dtyp)) : M MCFGEtop NoChoice Unit :=
  loop_monad initialize_global gs

def build_global_environment (m : Syntax.CFG.mcfg dtyp) : M MCFGEtop NoChoice Unit := do
  allocate_declarations (m.m_declarations ++ m.m_definitions.map (·.df_prototype))
  -- Rocq's nodup retains the last occurrence, which determines allocation order.
  allocate_block_addresses (@List.dedup _ block_address_eq_dec (Syntax.CFG.mcfg_block_addresses m))
  allocate_globals m.m_globals
  initialize_globals m.m_globals

variable {N : ITree.Effect → ITree.Effect → Type → Type w} [Runtime N] [Instrumentation.Diagnostics N]
variable [Instrumentation.Snapshots M] [Instrumentation.Snapshots N] (sim : Simulation M N)

theorem allocate_global_related (g : «global» dtyp) :
    sim.R (B := B) (allocate_global g) (allocate_global g) := by
  unfold allocate_global
  split
  · exact sim.pure ()
  · exact sim.bind (sim.alloca _ _ _) (fun v ↦ sim.gwrite _ v)

theorem allocate_globals_related (gs : List («global» dtyp)) :
    sim.R (B := B) (allocate_globals gs) (allocate_globals gs) :=
  sim.loop_monad (allocate_global_related sim) gs

theorem allocate_arg_related (arg : IRString) :
    sim.R (B := B) (allocate_arg arg) (allocate_arg arg) :=
  sim.bind (sim.alloca _ _ _) fun v ↦ sim.bind (sim.store _ v _) fun _ ↦ sim.pure v

theorem allocate_args_related (args : List IRString) :
    sim.R (B := B) (allocate_args args) (allocate_args args) :=
  sim.bind (sim.alloca _ _ _) fun v ↦ sim.bind (sim.map_monad (allocate_arg_related sim) args)
    fun _ ↦ sim.bind (sim.store _ v _) fun _ ↦ sim.pure v

theorem build_main_args_related (args : List IRString) :
    sim.R (B := B) (build_main_args args) (build_main_args args) :=
  sim.bind (allocate_args_related sim args) (fun _ ↦ sim.pure _)

theorem allocate_declaration_related (d : declaration dtyp) :
    sim.R (B := B) (allocate_declaration d) (allocate_declaration d) := by
  unfold allocate_declaration
  split
  · exact sim.pure ()
  · exact sim.bind (sim.alloca _ _ _) (fun v ↦ sim.gwrite _ v)

theorem allocate_declarations_related (ds : List (declaration dtyp)) :
    sim.R (B := B) (allocate_declarations ds) (allocate_declarations ds) :=
  sim.loop_monad (allocate_declaration_related sim) ds

theorem allocate_block_address_related (fb : function_id × block_id) :
    sim.R (B := B) (allocate_block_address fb) (allocate_block_address fb) :=
  sim.bind (sim.alloca _ _ _) (fun v ↦ sim.gwrite _ v)

theorem allocate_block_addresses_related (fbs : List (function_id × block_id)) :
    sim.R (B := B) (allocate_block_addresses fbs) (allocate_block_addresses fbs) :=
  sim.loop_monad (allocate_block_address_related sim) fbs

theorem initialize_global_related (g : «global» dtyp) :
    sim.R (initialize_global g) (initialize_global g) := by
  unfold initialize_global
  split
  · split
    · exact sim.bind (sim.gread _) (fun v ↦ sim.gwrite _ v)
    · exact sim.raiseUB _
    · exact sim.raiseUB _
  · apply sim.bind (sim.gread _)
    intro a
    cases g.g_exp with
    | none => exact sim.bind (sim.pure _) (sim.store g.g_typ a)
    | some e => exact sim.bind (Denotation.Worker.denote_exp_related sim _ e) (sim.store g.g_typ a)

theorem initialize_globals_related (gs : List («global» dtyp)) :
    sim.R (initialize_globals gs) (initialize_globals gs) :=
  sim.loop_monad (initialize_global_related sim) gs

theorem build_global_environment_related (m : Syntax.CFG.mcfg dtyp) :
    sim.R (build_global_environment m) (build_global_environment m) :=
  sim.bind (allocate_declarations_related sim _) fun _ ↦
    sim.bind (allocate_block_addresses_related sim _) fun _ ↦
      sim.bind (allocate_globals_related sim _) fun _ ↦ initialize_globals_related sim _

end Worker

def allocate_global (g : «global» dtyp) : MCFGtop Unit := Worker.allocate_global g

def allocate_globals (gs : List («global» dtyp)) : MCFGtop Unit := Worker.allocate_globals gs

def allocate_arg (arg : IRString) : MCFGtop dvalue := Worker.allocate_arg arg

def allocate_args (args : List IRString) : MCFGtop dvalue := Worker.allocate_args args

def build_main_args (args : List IRString) : MCFGtop (List (dtyp × dvalue)) :=
  Worker.build_main_args args

def allocate_declaration (d : declaration dtyp) : MCFGtop Unit := Worker.allocate_declaration d

def allocate_declarations (ds : List (declaration dtyp)) : MCFGtop Unit := Worker.allocate_declarations ds

def initialize_global (g : «global» dtyp) : MCFGtop Unit := Worker.initialize_global g

def initialize_globals (gs : List («global» dtyp)) : MCFGtop Unit := Worker.initialize_globals gs

def allocate_block_address (fb : function_id × block_id) : MCFGtop Unit :=
  Worker.allocate_block_address fb

def allocate_block_addresses (fbs : List (function_id × block_id)) : MCFGtop Unit :=
  Worker.allocate_block_addresses fbs

def build_global_environment (m : Syntax.CFG.mcfg dtyp) : MCFGtop Unit :=
  Worker.build_global_environment m

end Vellvm.Semantics.TopLevel
