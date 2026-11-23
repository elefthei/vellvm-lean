import Vellvm.Semantics.AllocationChoice

namespace Examples.Allocation
open Vellvm.Semantics Vellvm.Semantics.Handlers.Memory Vellvm.Utils.IntMaps

def atKey (n : Int) : IntMap Unit :=
  ⟨.Node .Leaf n () .Leaf 1, .BSNode .BSLeaf .BSLeaf (fun _ h ↦ nomatch h) (fun _ h ↦ nomatch h)⟩

example : next_key_with_alignment (atKey 5) 4 = 8 := by decide
example : next_key_with_alignment (atKey (-5)) 0 = 1 := by decide

example : ¬ AllocationLegal (atKey 5) 2 4 4 := by
  rintro ⟨_, _, free⟩
  exact free 1 (by decide) (by decide) ⟨(), .MapsRoot rfl⟩

example : AllocationLegal (atKey 5) 2 4 8 := next_key_with_alignment_legal (atKey 5) 2 4

example : AllocationLegal (atKey 5) 2 4 12 := by
  refine ⟨by decide, .inr (by decide), ?_⟩
  rintro i hi _ ⟨v, hv⟩
  change Vellvm.OrderedAVL.Raw.MapsTo (12 + i) v (.Node .Leaf 5 () .Leaf 1) at hv
  cases hv with
  | MapsRoot he => omega
  | MapsLeft h | MapsRight h => cases h

example : AllocationLegal (atKey 5) 0 0 5 :=
  ⟨by decide, .inl rfl, fun _ hi hlt ↦ by omega⟩

end Examples.Allocation
