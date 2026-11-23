module

public import Vellvm.Semantics.Interfaces.IPtr
public import Vellvm.Semantics.Interfaces.Pointer
public import Vellvm.Semantics.Implementations.Provenance

@[expose] public section
namespace Vellvm.Semantics.Implementations.Pointer
open Numeric.Rocqlib Utils.StringUtil Semantics.EOU Interfaces.IPtr Interfaces.Pointer
open Implementations.Provenance

variable [IP : IPtr]

instance showIptr : Show IP.iptr := ⟨IP.show_iptr⟩

instance PointerV : @Pointer ProvenanceV where
  ptr := IP.iptr × ProvenanceV.prov
  null := (IP.zero_iptr, ProvenanceV.nil_prov)
  eq_dec_ptr :=
    letI : DecidableEq IP.iptr := eqDecidable IP.eq_dec_iptr
    fun (a b : IP.iptr × Option (List Nat)) ↦ decideSum (a = b)
  ptr_provenance := Prod.snd
  show_ptr := (@showPair IP.iptr ProvenanceV.prov (@showIptr IP) ⟨ProvenanceV.show_prov⟩).«show»

instance PIV : @PI ProvenanceV (@PointerV IP) where
  ptr_to_int a := IP.to_Z a.1
  int_to_ptr i p := EOU.bind (IP.from_Z i) fun a ↦ raise_ret (a, p)

instance PITheoryV [T : @IPtrTheory IP] : @PITheory ProvenanceV (@PointerV IP) (@PIV IP) where
  int_to_ptr_provenance := by
    intro x p a h
    obtain ⟨i, _, hi⟩ := EOU_bind_ret_inv (IP.from_Z x) (fun j ↦ raise_ret (j, p)) a h
    cases hi
    rfl
  int_to_ptr_ptr_to_int := by
    rintro ⟨i, p⟩ _ rfl
    change EOU.bind (IP.from_Z (IP.to_Z i)) (fun j ↦ raise_ret (j, p)) = raise_ret (i, p)
    simp only [T.to_Z_from_Z, EOU.bind]
  int_to_ptr_ptr_to_int_exists := by
    rintro ⟨i, _⟩ p
    refine ⟨(i, p), ?_, rfl, rfl⟩
    change EOU.bind (IP.from_Z (IP.to_Z i)) _ = _
    simp only [T.to_Z_from_Z, EOU.bind]
  ptr_to_int_int_to_ptr := by
    intro x p a h
    obtain ⟨i, hi, h⟩ := EOU_bind_ret_inv (IP.from_Z x) (fun j ↦ raise_ret (j, p)) a h
    cases h
    exact T.from_Z_to_Z x hi

end Vellvm.Semantics.Implementations.Pointer
