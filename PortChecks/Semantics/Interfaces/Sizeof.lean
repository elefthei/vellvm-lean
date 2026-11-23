import PortChecks.SourceType
import Vellvm.Semantics.Interfaces.Sizeof

open Vellvm Vellvm.Syntax.DynamicTypes Vellvm.Semantics.Interfaces.Sizeof

#source_check "src/rocq/Semantics/Interfaces/Sizeof.v|Vellvm.Semantics.Interfaces.Sizeof|pad_to_0"
  pad_to_0 : ∀ x, pad_to 0 x = x
#source_check "src/rocq/Semantics/Interfaces/Sizeof.v|Vellvm.Semantics.Interfaces.Sizeof|pad_to_mod"
  pad_to_mod : ∀ {a} x, a ≠ 0 → pad_to a x % a = 0
#source_check "src/rocq/Semantics/Interfaces/Sizeof.v|Vellvm.Semantics.Interfaces.Sizeof|pad_amount_aligned"
  pad_amount_aligned : ∀ a y, y % a = 0 → pad_amount a y = 0
#source_check "src/rocq/Semantics/Interfaces/Sizeof.v|Vellvm.Semantics.Interfaces.Sizeof|pad_to_idem"
  pad_to_idem : ∀ a x, pad_to a (pad_to a x) = pad_to a x
#source_check "src/rocq/Semantics/Interfaces/Sizeof.v|Vellvm.Semantics.Interfaces.Sizeof|store_le_alloc"
  store_le_alloc : ∀ [Sizeof] t, store_size_dtyp t ≤ alloc_size_dtyp t
#source_check "src/rocq/Semantics/Interfaces/Sizeof.v|Vellvm.Semantics.Interfaces.Sizeof|store_size_B_I"
  store_size_B_I : ∀ [S : Sizeof] [@SizeofTheory S] (sz : Positive),
    store_size_dtyp (DTYPE_B sz) = store_size_dtyp (DTYPE_I sz)
#source_check "src/rocq/Semantics/Interfaces/Sizeof.v|Vellvm.Semantics.Interfaces.Sizeof|store_size_int_mult8"
  store_size_int_mult8 : ∀ [S : Sizeof] [@SizeofTheory S] (sz : Positive),
    sz.val % 8 = 0 → 8 * store_size_dtyp (DTYPE_I sz) = sz.val
#source_check "src/rocq/Semantics/Interfaces/Sizeof.v|Vellvm.Semantics.Interfaces.Sizeof|store_size_int_mixed"
  store_size_int_mixed : ∀ [S : Sizeof] [@SizeofTheory S] (sz : Positive),
    sz.val % 8 ≠ 0 → 1 ≤ store_size_dtyp (DTYPE_I sz) ∧
      8 * (store_size_dtyp (DTYPE_I sz) - 1) + sz.val % 8 = sz.val
#source_check "src/rocq/Semantics/Interfaces/Sizeof.v|Vellvm.Semantics.Interfaces.Sizeof|store_size_int_bits"
  store_size_int_bits : ∀ [S : Sizeof] [@SizeofTheory S] (sz : Positive),
    sz.val ≤ 8 * store_size_dtyp (DTYPE_I sz)
#source_check "src/rocq/Semantics/Interfaces/Sizeof.v|Vellvm.Semantics.Interfaces.Sizeof|store_size_B_bytes"
  store_size_B_bytes : ∀ [S : Sizeof] [@SizeofTheory S] (sz : Positive),
    sz.val % 8 = 0 → 8 * store_size_dtyp (DTYPE_B sz) = sz.val
