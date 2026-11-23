import Vellvm.Semantics.Denotation

namespace Vellvm.Semantics.TopLevel
open ITree (Effect)
open Tree Interfaces.Params Instrumentation DynamicValues Syntax.LLVMAst Syntax.CFG Syntax.DynamicTypes
open LLVMEvents (MCFGEtop MCFGtop)
open Utils.ListUtil (map_monad)

variable [Pa : Params]

namespace Worker
variable {M : Effect → Effect → Type → Type v} [Runtime M] [Diagnostics M]

/-- Only the integer address crosses a runtime bind; a producer's function closures live one
universe above the LLVM answer types. -/
def address (name : function_id) (message : IRString) : M MCFGEtop NoChoice Int := do
  match dvalue_ptr_address (← LLVMEvents.Worker.gread name) with
  | some z => pure z
  | none => LLVMEvents.Worker.«raise» message

def functionAddress (df : definition dtyp (cfg dtyp)) : M MCFGEtop NoChoice Int :=
  address df.df_prototype.dc_name "address_one_function: invalid address, should not happen.".toUTF8

def libraryAddress (fid : function_id) : M MCFGEtop NoChoice Int :=
  address fid "address_one_library_function: invalid address, should not happen.".toUTF8

def addressTable {A : Type u} {F : Type w} (den : A → F) (xs : List A) (keys : List Int) :
    List (Int × F) := keys.zipWith (fun k x ↦ (k, den x)) xs

variable {N : Effect → Effect → Type → Type w} [Runtime N] [Diagnostics N]
variable [Snapshots M] [Snapshots N] (sim : Simulation M N)

theorem address_related (name : function_id) (message : IRString) :
    sim.R (address name message) (address name message) := by
  unfold address
  apply sim.bind (sim.gread _)
  intro fv
  cases dvalue_ptr_address fv with
  | some z => exact sim.pure z
  | none => exact sim.«raise» _

theorem addressTable_related {A : Type u} {F : Type w} {G : Type z} {R : F → G → Prop}
    (l : A → F) (r : A → G) (h : ∀ a, R (l a) (r a)) (xs : List A) (keys : List Int) :
    List.Forall₂ (Utils.RelationsUtil.prod_rel Eq R) (addressTable l xs keys) (addressTable r xs keys) := by
  induction keys generalizing xs with
  | nil => exact .nil
  | cons k ks ih =>
    cases xs with
    | nil => exact .nil
    | cons x xs => exact .cons ⟨rfl, h x⟩ (ih xs)

end Worker

def address_one_function (df : definition dtyp (cfg dtyp)) :
    MCFGtop (Int × Denotation.function_denotation) := do
  return (← Worker.functionAddress df, Denotation.denote_function df)

def address_one_library_function (libfun : function_id × Denotation.function_denotation) :
    MCFGtop (Int × Denotation.function_denotation) := do
  return (← Worker.libraryAddress libfun.1, libfun.2)

/-- Pairing the closures after address lookup computes precisely the source's list of addressed
functions, in order, even when a lookup diverges or aborts. -/
theorem addressTable_bind {A F X : Type} (key : A → MCFGtop Int) (den : A → F) (xs : List A)
    (k : List (Int × F) → MCFGtop X) :
    (map_monad (fun x ↦ key x >>= fun z ↦ pure (z, den x)) xs >>= k) =
      (map_monad key xs >>= fun zs ↦ k (Worker.addressTable den xs zs)) := by
  induction xs generalizing k with
  | nil => simp [map_monad, Worker.addressTable]
  | cons x xs ih =>
    simp only [map_monad, bind_assoc, pure_bind]
    apply congrArg (fun h ↦ key x >>= h)
    funext z
    exact ih (fun ys ↦ k ((z, den x) :: ys))

end Vellvm.Semantics.TopLevel
