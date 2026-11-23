import PortChecks.SourceType
import Vellvm.Semantics.Implementations.Sizeof

open Vellvm.Syntax.DynamicTypes Vellvm.Semantics.Interfaces.Sizeof
open Vellvm.Semantics.Implementations.Sizeof

#source_check "src/rocq/Semantics/Implementations/Sizeof.v|Vellvm.Semantics.Implementations.Sizeof|SizeofV"
  SizeofV : Sizeof
#source_check "src/rocq/Semantics/Implementations/Sizeof.v|Vellvm.Semantics.Implementations.Sizeof|Store_size_alloc_size"
  Store_size_alloc_size : ∀ t, @alloc_size_dtyp SizeofV t =
    pad_to_align (Dtyp_alignment t) (Store_size_dtyp t)
#source_check "src/rocq/Semantics/Implementations/Sizeof.v|Vellvm.Semantics.Implementations.Sizeof|struct_fields_extent_V"
  struct_fields_extent_V : ∀ p l, @struct_fields_extent SizeofV p l =
    l.foldl (fun acc x ↦ (if p then acc else pad_to_align (Dtyp_alignment x) acc) +
      pad_to_align (Dtyp_alignment x) (Store_size_dtyp x)) 0
#source_check "src/rocq/Semantics/Implementations/Sizeof.v|Vellvm.Semantics.Implementations.Sizeof|preferred_Dtyp_alignment_Struct"
  preferred_Dtyp_alignment_Struct : ∀ dts, preferred_alignment (Dtyp_alignment (DTYPE_Struct false dts)) =
    Vellvm.Semantics.Implementations.Sizeof.max_preferred_dtyp_alignment dts
#source_check "src/rocq/Semantics/Implementations/Sizeof.v|Vellvm.Semantics.Implementations.Sizeof|round_up_to_eight_div"
  round_up_to_eight_div : ∀ {n}, 0 < n → round_up_to_eight n / 8 = (n + 7) / 8
#source_check "src/rocq/Semantics/Implementations/Sizeof.v|Vellvm.Semantics.Implementations.Sizeof|SizeofTheoryV"
  SizeofTheoryV : @SizeofTheory SizeofV

-- i65 has ABI alignment four but preferred alignment eight: nine bytes stride by sixteen.
example : alloc_size_dtyp (DTYPE_I ⟨65, by decide⟩) = 16 := by
  rw [Store_size_alloc_size]
  simp only [Dtyp_alignment, Store_size_dtyp]
  decide

example : store_size_dtyp (DTYPE_Array true 8 (DTYPE_I ⟨1, by decide⟩)) = 1 := by
  rw [store_size_dtyp_vector_int]; decide

-- Packing removes each field's offset alignment, not its allocation padding.
example : store_size_dtyp (DTYPE_Struct true [DTYPE_I ⟨24, by decide⟩, DTYPE_I ⟨8, by decide⟩]) = 5 := by
  change Store_size_dtyp (DTYPE_Struct true _) = 5
  simp only [Store_size_dtyp, List.foldl_cons, List.foldl_nil, Dtyp_alignment]
  decide
