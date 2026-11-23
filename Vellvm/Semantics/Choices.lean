module

public import Vellvm.Semantics.AllocationChoice
public import Vellvm.Semantics.DynamicValues.Pointers
public import Vellvm.Semantics.Implementations.Memory.Basic
public import Vellvm.Semantics.Implementations.ParamsV
public import Vellvm.Semantics.LLVMEvents

@[expose] public section
namespace Vellvm.Semantics
open ITree (Effect)
open CTree (CTree)
open Tree Interfaces.Params DynamicValues Syntax.DynamicTypes EOU
open Implementations.Memory Handlers.Memory

inductive ChoiceRequest (P : Params) where
  | draw (dt : dtyp) (initial : @dvalue P) (success : default_dvalue_of_dtyp dt = raise_ret initial)
  | nextKey (bytes : memory (Pa := P)) (size align : Nat)
  | fresh (high : P.PROV.provenance)
  | exposed

namespace ChoiceRequest
variable {P : Params}

def Answer : ChoiceRequest P → Type
  | .draw .. => @dvalue P
  | .nextKey .. => Int
  | .fresh _ => P.PROV.provenance
  | .exposed => Option P.PROV.provenance

def Legal : (c : ChoiceRequest P) → c.Answer → Prop
  | .draw dt _ _, x => @dvalue_is_canonical P dt x = true ∧ @dvalue_well_defined P x = true ∧
      @allPointers P (fun p ↦ P.PTR.ptr_provenance p = P.PROV.nil_prov) x
  | .nextKey bytes size align, k => AllocationLegal bytes size align k
  | .fresh high, p => P.PROV.provenance_lt high p
  | .exposed, p => p = none

def reference : (c : ChoiceRequest P) → c.Answer
  | .draw _ x _ => x
  | .nextKey bytes _ align => next_key_with_alignment bytes align
  | .fresh high => P.PROV.next_provenance high
  | .exposed => none

theorem reference_legal (hn : P.PTR.ptr_provenance P.PTR.null = P.PROV.nil_prov)
    (c : ChoiceRequest P) : c.Legal c.reference := by
  letI : Params := P
  cases c with
  | draw dt x eq =>
    obtain ⟨hc, hd⟩ := default_success_canonical_defined dt x eq
    exact ⟨hc, hd, default_valid_pointers _ hn dt x eq⟩
  | nextKey bytes size align => exact next_key_with_alignment_legal bytes size align
  | fresh high => exact P.PROVT.provenance_lt_next_provenance high
  | exposed => rfl

end ChoiceRequest

@[implicit_reducible] def Choice (P : Params) : Effect :=
  ⟨ChoiceRequest P, fun c ↦ {x : c.Answer // c.Legal x}⟩

/-- Selection sites receive only the raw answer; downstream checks (including pointer OOM) still run. -/
abbrev Chooser (P : Params) (M : Effect → Effect → Type → Type v) (E B : Effect) :=
  (c : ChoiceRequest P) → M E B c.Answer

def referenceChooser {P : Params} {M : Effect → Effect → Type → Type v} [Runtime M] {E B : Effect} :
    Chooser P M E B := fun c ↦ pure c.reference

def branchingChooser {P : Params} {M : Effect → Effect → Type → Type v} [Runtime M] {E : Effect} :
    Chooser P M E (Choice P) := fun c ↦ do
  let x ← Runtime.branch (M := M) (B := Choice P) c
  pure x.val

/-- Both IPZ and IP64Bit instantiate this scheduler. No hypothesis is added to the generic interpreter. -/
def canonical [IP : Interfaces.IPtr.IPtr] [T : Interfaces.IPtr.IPtrTheory] :
    (c : (Choice (@Implementations.ParamsV.ParamsV IP T)).I) →
      CTree LLVMEvents.MCFGEbot NoChoice ((Choice (@Implementations.ParamsV.ParamsV IP T)).O c) :=
  fun c ↦ pure ⟨c.reference, c.reference_legal rfl⟩

end Vellvm.Semantics
