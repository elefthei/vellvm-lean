import Vellvm.Semantics.TopLevel.Addressing
import Vellvm.Semantics.TopLevel.Initialization
import Vellvm.Semantics.TopLevel.Linking
import Vellvm.Semantics.Libraries
import Vellvm.Syntax.TypToDtyp

namespace Vellvm.Semantics.TopLevel
open ITree (Effect)
open Tree Interfaces.Params Instrumentation DynamicValues Syntax.LLVMAst Syntax.CFG Syntax.DynamicTypes
open LLVMEvents (MCFGEtop MCFGtop)
open Utils.ListUtil (map_monad)
open Utils.IntMaps

variable [Pa : Params]

namespace Worker
variable {M : Effect → Effect → Type → Type v} [Runtime M] [Diagnostics M] [Catch M]

def denote_vellvm (ret_typ : dtyp) (entry : function_id) (args : List (dtyp × dvalue))
    (m : mcfg dtyp) : M MCFGEtop NoChoice dvalue := do
  build_global_environment m
  let defs := m.m_definitions
  let ds ← map_monad functionAddress defs
  let libs := Libraries.selected m.m_declarations
  let ls ← map_monad (fun p ↦ libraryAddress p.1) libs
  let addr ← LLVMEvents.Worker.gread entry
  let table := IP.of_list (addressTable (Denotation.Worker.denote_function (M := M)) defs ds ++
    addressTable (fun p ↦ Libraries.Worker.denoteBuiltin (M := M) (B := NoChoice) p.2) libs ls)
  match ← Denotation.Worker.denote_mcfg table ret_typ addr args with
  | .inl exc => LLVMEvents.Worker.raiseLLVM exc
  | .inr v => pure v

/-- The argument generator is part of the open tree, before the module's initialization. -/
def open_program (ret_typ : dtyp) (entry : function_id)
    (arg_gen : M MCFGEtop NoChoice (List (dtyp × dvalue))) (prog : ll_toplevel_entities) :
    M MCFGEtop NoChoice dvalue := do
  let args ← arg_gen
  denote_vellvm ret_typ entry args (Syntax.TypToDtyp.convert_types (mcfg_of_tle (link PREDEFINED_FUNCTIONS prog)))

def open_main (argv : List IRString) (prog : ll_toplevel_entities) : M MCFGEtop NoChoice dvalue :=
  open_program (DTYPE_Base (DTYPE_I ⟨32, by decide⟩)) (.Name "main".toUTF8) (build_main_args argv) prog

variable {N : Effect → Effect → Type → Type w} [Runtime N] [Diagnostics N] [Catch N]
variable [Snapshots M] [Snapshots N] (sim : Simulation M N) (hc : Denotation.CatchCompatible sim)
include hc

theorem denote_vellvm_related (ret_typ : dtyp) (entry : function_id) (args : List (dtyp × dvalue))
    (m : mcfg dtyp) : sim.R (denote_vellvm ret_typ entry args m) (denote_vellvm ret_typ entry args m) := by
  unfold denote_vellvm
  apply sim.bind (build_global_environment_related sim m)
  intro _
  apply sim.bind
  · apply sim.map_monad
    intro df
    exact address_related sim _ _
  intro ds
  apply sim.bind
  · apply sim.map_monad
    intro p
    exact address_related sim _ _
  intro ls
  apply sim.bind (sim.gread entry)
  intro addr
  apply sim.bind
  · apply Denotation.Worker.denote_mcfg_related
    apply Utils.IntMaps.IM_Refine_of_list_app
    · exact addressTable_related _ _ (Denotation.Worker.denote_function_related sim hc) _ ds
    · exact addressTable_related _ _ (fun p ↦ Libraries.Worker.denoteBuiltin_related sim p.2) _ ls
  · rintro (exc | rv)
    · exact sim.raiseLLVM exc
    · exact sim.pure rv

theorem open_program_related (ret_typ : dtyp) (entry : function_id)
    {l : M MCFGEtop NoChoice (List (dtyp × dvalue))} {r : N MCFGEtop NoChoice (List (dtyp × dvalue))}
    (h : sim.R l r) (prog : ll_toplevel_entities) :
    sim.R (open_program ret_typ entry l prog) (open_program ret_typ entry r prog) :=
  sim.bind h (fun args ↦ denote_vellvm_related sim hc ret_typ entry args _)

end Worker

def denote_vellvm (ret_typ : dtyp) (entry : function_id) (args : List (dtyp × dvalue)) (m : mcfg dtyp) :
    MCFGtop dvalue := Worker.denote_vellvm ret_typ entry args m

private theorem map_input {A B X : Type} (f : A → B) (g : B → MCFGtop X) (xs : List A) :
    map_monad g (xs.map f) = map_monad (fun x ↦ g (f x)) xs := by
  induction xs with
  | nil => rfl
  | cons _ _ ih => simp only [List.map_cons, map_monad, ih]

theorem address_functions_bind {X : Type} (ds : List (definition dtyp (cfg dtyp)))
    (k : List (Int × Denotation.function_denotation) → MCFGtop X) :
    (map_monad address_one_function ds >>= k) = (map_monad Worker.functionAddress ds >>= fun zs ↦
      k (Worker.addressTable Denotation.denote_function ds zs)) :=
  addressTable_bind _ _ _ _

theorem address_libraries_bind {X : Type} (ds : List (declaration dtyp))
    (k : List (Int × Denotation.function_denotation) → MCFGtop X) :
    (map_monad address_one_library_function (Libraries.library_functions ds) >>= k) =
      (map_monad (fun p ↦ Worker.libraryAddress p.1) (Libraries.selected ds) >>= fun zs ↦
        k (Worker.addressTable (fun p ↦ Libraries.Worker.denoteBuiltin p.2) (Libraries.selected ds) zs)) := by
  change (map_monad address_one_library_function ((Libraries.selected ds).map _) >>= k) = _
  rw [map_input]
  exact addressTable_bind _ _ _ _

/-- The higher-order address traversal in the source and the first-order runtime traversal agree
as trees (not merely on terminating executions). -/
theorem denote_vellvm_source (ret_typ : dtyp) (entry : function_id) (args : List (dtyp × dvalue))
    (m : mcfg dtyp) : denote_vellvm ret_typ entry args m = (do
      build_global_environment m
      let ds ← map_monad address_one_function m.m_definitions
      let ls ← map_monad address_one_library_function (Libraries.library_functions m.m_declarations)
      let addr ← LLVMEvents.gread entry
      match ← Denotation.denote_mcfg (IP.of_list (ds ++ ls)) ret_typ addr args with
      | .inl exc => LLVMEvents.raiseLLVM exc
      | .inr v => pure v) := by
  simp only [address_functions_bind, address_libraries_bind]
  rfl

end Vellvm.Semantics.TopLevel
