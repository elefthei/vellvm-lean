module

@[expose] public section
namespace Vellvm.Theory.I2F.Refinement

/-- The Equations graph-correctness principle registered for a function. -/
class FunctionalInduction {α : Type u} (f : α) where
  fun_ind_prf_ty : Type v
  fun_ind_prf : fun_ind_prf_ty

/-- The Equations eliminator and its number of motive and method binders. -/
class FunctionalElimination {α : Type u} (f : α) (fun_elim_ty : Type v) (n : Nat) where
  fun_elim : fun_elim_ty

end Vellvm.Theory.I2F.Refinement
