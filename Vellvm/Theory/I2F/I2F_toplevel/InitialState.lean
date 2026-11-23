import Vellvm.Theory.I2F.I2F_interp.State

namespace Vellvm.Theory.I2F.I2F_toplevel
open Refinement I2F_interp I2F_memory Semantics.DynamicValues Semantics.Implementations.Memory
open Semantics.Handlers.Stack Syntax.RawIdMaps Utils.IntMaps

theorem I2F_initial_FusedS : I2F_FusedS
    ((@MemoryModelStateV PInf).initial_state, (@Build_stack_frame PInf (RM.empty _) none none, []),
      RM.empty (@dvalue PInf))
    ((@MemoryModelStateV PFin).initial_state, (@Build_stack_frame PFin (RM.empty _) none none, []),
      RM.empty (@dvalue PFin)) :=
  ⟨⟨⟨IM_Refine_empty _, .I2F_FS_Singleton .nil, IM_Refine_empty _⟩, rfl⟩,
    ⟨RM_Refine_empty _, .none, rfl⟩, .nil, RM_Refine_empty _⟩

end Vellvm.Theory.I2F.I2F_toplevel
