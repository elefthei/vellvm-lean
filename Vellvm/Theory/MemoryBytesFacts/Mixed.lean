import Vellvm.Theory.MemoryBytesFacts.Base

namespace Vellvm.Theory.MemoryBytesFacts
open Semantics Semantics.Interfaces.Params Semantics.Interfaces.Sizeof Semantics.DynamicValues
open Semantics.MemoryBytes Semantics.EOU Syntax.DynamicTypes Utils.ListUtil

variable [Pa : Params]

private abbrev padded (bits : List memory_bit) :=
  bits ++ (if !(bits.length == 8) then List.replicate (8 - bits.length) Bit_psn else [])

def mixed_byte (bits : List memory_bit) (idx : Nat) : memory_byte :=
  BYTE_Mixed (padded ((bits.drop (8 * idx)).take 8))

theorem writer_mixed_byte (sz : Positive) (bits : List memory_bit) (idx : Nat) :
    memory_byte_of_dvalue_bv (BYTE_Mixed (bit_sz := sz) bits) idx = mixed_byte bits idx := rfl

theorem mixed_byte_shift (bits : List memory_bit) (j : Nat) :
    mixed_byte bits (1 + j) = mixed_byte (bits.drop 8) j := by
  simp only [mixed_byte, List.drop_drop, Nat.mul_add, Nat.mul_one]

theorem memory_byte_to_memory_bits_mixed (bits : List memory_bit) (idx : Nat) :
    memory_byte_to_memory_bits (mixed_byte bits idx) = padded ((bits.drop (8 * idx)).take 8) := rfl

private abbrev block (bits : List memory_bit) (n : Nat) := (Nseq 0 n).map (mixed_byte bits)

theorem mixed_block_head (bits : List memory_bit) (n : Nat) :
    block bits (n + 1) = mixed_byte bits 0 :: (Nseq 1 n).map (mixed_byte bits) := rfl

theorem mixed_byte_0 (bits : List memory_bit) :
    mixed_byte bits 0 = BYTE_Mixed (padded (bits.take 8)) := rfl

private theorem block_step (bits : List memory_bit) (n : Nat) :
    block bits (n + 1) = mixed_byte bits 0 :: block (bits.drop 8) n := by
  rw [mixed_block_head]
  change _ :: (Nseq (1 + 0) n).map _ = _
  rw [← map_Nseq_shift (mixed_byte bits) n 0 1]
  simp only [mixed_byte_shift, block]

private theorem drop_bound (n : Nat) (bits : List memory_bit) (h : bits.length ≤ 8 * (n+1)) :
    (bits.drop 8).length ≤ 8 * n := by simp only [List.length_drop]; omega

theorem get_bits_writer (n : Nat) (bits acc : List memory_bit) (hlen : bits.length ≤ 8 * n) :
    get_bits_of_memory_byte_list bits.length (block bits n) acc = bits.reverseAux acc := by
  induction n generalizing bits acc with
  | zero =>
    have h : bits.length = 0 := by omega
    rw [List.length_eq_zero_iff.mp h]
    rfl
  | succ n ih =>
    rw [block_step, get_bits_of_memory_byte_list, memory_byte_to_memory_bits_mixed]
    simp only [Nat.mul_zero, List.drop_zero]
    by_cases h : bits.length < 8
    · simp only [if_pos h, List.take_of_length_le (Nat.le_of_lt h), padded]
      rw [List.take_append_of_le_length (Nat.le_refl _), List.take_length]
    · have h₈ := take_length_exact bits 8 (by omega)
      change (bits.take 8).length = 8 at h₈
      simp only [if_neg h, padded, h₈, beq_self_eq_true, Bool.not_true, Bool.false_eq_true,
        if_false, List.append_nil]
      rw [← List.length_drop (i := 8) (l := bits), ih _ _ (drop_bound n bits hlen)]
      have hr := congrArg List.reverse (List.take_append_drop 8 bits)
      simpa only [List.reverseAux_eq, List.reverse_append, List.append_assoc] using
        congrArg (· ++ acc) hr

theorem all_poison_bytes_forallb (l : List memory_byte) :
    all_poison_bytes l = l.all is_all_poison_byte := by
  induction l with
  | nil => rfl
  | cons b l ih =>
    cases h : is_all_poison_byte b <;> simp [all_poison_bytes, poison_split, h, all_poison_bytes] at ih ⊢
    exact ih

theorem mixed_all_poison (n : Nat) (bits : List memory_bit) (hlen : bits.length ≤ 8 * n)
    (h : (block bits n).all is_all_poison_byte = true) : bits.all is_poison_bit = true := by
  induction n generalizing bits with
  | zero =>
    have e := List.length_eq_zero_iff.mp (show bits.length = 0 by omega)
    simp [e]
  | succ n ih =>
    rw [block_step, List.all_cons, Bool.and_eq_true] at h
    obtain ⟨hh, ht⟩ := h
    change (padded (bits.take 8)).all is_poison_bit = true at hh
    rw [padded, List.all_append, Bool.and_eq_true] at hh
    have ht' := ih (bits.drop 8) (drop_bound n bits hlen) ht
    calc
      bits.all is_poison_bit = ((bits.take 8) ++ bits.drop 8).all is_poison_bit := by rw [List.take_append_drop]
      _ = true := by rw [List.all_append, hh.1, ht']; rfl

theorem map_monad_bit_pois (l : List memory_bit) (h : l.any is_poison_bit = true) :
    map_monad (m := EOUP) memory_bit_to_bit l = raise_ret none := by
  induction l with
  | nil => contradiction
  | cons b l ih =>
    rw [map_monad_cons_EOUP]
    cases b <;> simp only [List.any_cons, is_poison_bit, Bool.false_or, Bool.true_or] at h
    all_goals first | rfl | rw [ih h]; rfl

theorem memory_bits_to_Z_pois (l : List memory_bit) (h : l.any is_poison_bit = true) :
    memory_bits_to_Z l = raise_ret none := by
  rw [memory_bits_to_Z, map_monad_bit_pois l h]; rfl

theorem memory_byte_to_Z_mixed_pois (bits : List memory_bit) (idx : Nat)
    (h : ((bits.drop (8 * idx)).take 8).any is_poison_bit = true) :
    memory_byte_to_Z (mixed_byte bits idx) = raise_ret none := by
  apply memory_bits_to_Z_pois
  simp [padded, List.any_append, h]

theorem map_monad_bit_ret (l : List memory_bit) :
    ∃ r, map_monad (m := EOUP) memory_bit_to_bit l = raise_ret r := by
  induction l with
  | nil => exact ⟨some [], rfl⟩
  | cons b l ih =>
    obtain ⟨r, hr⟩ := ih
    rw [map_monad_cons_EOUP, hr]
    cases b <;> cases r <;> exact ⟨_, rfl⟩

theorem memory_bits_to_Z_total (bits : List memory_bit) :
    memory_bits_to_Z bits = raise_ret none ∨ ∃ z, memory_bits_to_Z bits = raise_ret (some z) := by
  obtain ⟨r, e⟩ := map_monad_bit_ret bits
  rw [memory_bits_to_Z, e]
  cases r with
  | none => exact Or.inl rfl
  | some xs => exact Or.inr ⟨_, rfl⟩

theorem memory_byte_to_Z_mixed_ret (bits : List memory_bit) (idx : Nat) :
    ∃ r, memory_byte_to_Z (mixed_byte bits idx) = raise_ret r := by
  rcases memory_bits_to_Z_total (padded ((bits.drop (8 * idx)).take 8)) with h | ⟨z, h⟩
  · exact ⟨_, h⟩
  · exact ⟨_, h⟩

private theorem any_split (bits : List memory_bit) (h : bits.any is_poison_bit = true) :
    (bits.take 8).any is_poison_bit = true ∨ (bits.drop 8).any is_poison_bit = true := by
  rw [← Bool.or_eq_true, ← List.any_append, List.take_append_drop]; exact h

theorem map_monad_byte_mixed_pois (n : Nat) (bits : List memory_bit) (hlen : bits.length ≤ 8 * n)
    (hp : bits.any is_poison_bit = true) :
    map_monad (m := EOUP) memory_byte_to_Z (block bits n) = raise_ret none := by
  induction n generalizing bits with
  | zero =>
    have e := List.length_eq_zero_iff.mp (show bits.length = 0 by omega)
    simp [e] at hp
  | succ n ih =>
    rw [block_step, map_monad_cons_EOUP]
    rcases any_split bits hp with hh | ht
    · rw [memory_byte_to_Z_mixed_pois bits 0 hh]; rfl
    · rw [ih _ (drop_bound n bits hlen) ht]
      obtain ⟨r, e⟩ := memory_byte_to_Z_mixed_ret bits 0
      rw [e]; cases r <;> rfl

theorem cbmix_cons (extra : Nat) (b : memory_byte) (f : Nat → memory_byte) (a n : Nat) :
    concat_bytes_Z_mixed extra (b :: (Nseq a (n + 1)).map f) =
      (do let z ← memory_byte_to_Z b
          let r ← concat_bytes_Z_mixed extra ((Nseq a (n+1)).map f)
          pure (z + (r <<< 8)) : EOUP Int) := by
  have shift (r : Int) : r <<< 8 = 256 * r :=
    (Int.shiftLeft_eq_mul_pow r 8).trans (Int.mul_comm _ _)
  simp only [shift]
  change concat_bytes_Z_mixed extra (b :: f a :: _) = _
  cases b <;> rfl

theorem concat_bytes_Z_mixed_mixed_pois (n : Nat) {extra : Nat} (bits : List memory_bit)
    (hx : 0 < extra ∧ extra ≤ 8) (hlen : bits.length = 8 * n + extra)
    (hp : bits.any is_poison_bit = true) :
    concat_bytes_Z_mixed extra (block bits (n + 1)) = raise_ret none := by
  induction n generalizing bits with
  | zero =>
    change memory_bits_to_Z ((padded (bits.take 8)).take extra) = _
    rw [List.take_of_length_le (show bits.length ≤ 8 by omega), padded,
      show extra = bits.length by omega, List.take_append_of_le_length (Nat.le_refl _),
      List.take_length]
    exact memory_bits_to_Z_pois bits hp
  | succ n ih =>
    rw [block_step, cbmix_cons]
    rcases any_split bits hp with hh | ht
    · rw [memory_byte_to_Z_mixed_pois bits 0 hh]; rfl
    · have e : (bits.drop 8).length = 8 * n + extra := by simp only [List.length_drop]; omega
      rw [ih _ e ht]
      obtain ⟨r, hr⟩ := memory_byte_to_Z_mixed_ret bits 0
      rw [hr]; cases r <;> rfl

theorem all_pointer_bits_from_app (l₁ : List memory_bit) (p : Pa.PTR.ptr) (j : Nat)
    (l₂ : List memory_bit) : all_pointer_bits_from p j (l₁ ++ l₂) =
      (all_pointer_bits_from p j l₁ && all_pointer_bits_from p (j + l₁.length) l₂) := by
  induction l₁ generalizing j with
  | nil => simp [all_pointer_bits_from]
  | cons b l ih =>
    cases b with
    | Bit_ptr q i =>
      simp only [List.cons_append, all_pointer_bits_from, ih, List.length_cons, Bool.and_assoc]
      rw [show 1 + j + l.length = j + (l.length + 1) by omega]
    | Bit_bit x => rfl
    | Bit_psn => rfl

theorem all_pointer_bits_from_repeat_psn (m : Nat) (p : Pa.PTR.ptr) (j : Nat) :
    all_pointer_bits_from p j (List.replicate m Bit_psn) = true → m = 0 := by
  cases m <;> simp [List.replicate_succ, all_pointer_bits_from]

theorem valid_pointer_bits_implies (l : List memory_bit) (p : Pa.PTR.ptr) (base offset : Nat)
    (h : valid_pointer_bits p base offset l = raise_ret (some true)) :
    all_pointer_bits_from p (base + offset) l = true := by
  induction l generalizing offset with
  | nil => rfl
  | cons b l ih =>
    cases b with
    | Bit_ptr q i =>
      cases e : Pa.PTR.eq_dec_ptr p q with
      | inr ne => simp only [valid_pointer_bits, e] at h; cases h
      | inl eq =>
        by_cases ej : i = base + offset
        · simp only [valid_pointer_bits, e, ej, beq_self_eq_true, if_true] at h
          simpa [all_pointer_bits_from, e, Numeric.Rocqlib.chooseSide, ej,
            show 1 + (base + offset) = base + (1 + offset) by omega] using ih (1 + offset) h
        · simp [valid_pointer_bits, e, ej, pure, EOUP_Monad] at h; cases h
    | Bit_bit x => cases h
    | Bit_psn => cases h

private theorem valid_of_pointer_byte_at (p : Pa.PTR.ptr) (k : Nat) (b : memory_byte)
    (h : pointer_byte_at p k b = true) : valid_pointer_byte p k b = raise_ret (some true) := by
  unfold pointer_byte_at at h
  generalize valid_pointer_byte p k b = v at h ⊢
  cases v with
  | raise_ret o => cases o with
    | none => contradiction
    | some b => cases b <;> first | rfl | contradiction
  | _ => contradiction

theorem pointer_slice_implies_bits (n : Nat) (bits : List memory_bit) (p : Pa.PTR.ptr) (k : Nat)
    (hlen : bits.length ≤ 8*n) (hs : pointer_slice_from p k (block bits n) = true) :
    all_pointer_bits_from p (8*k) bits = true := by
  induction n generalizing bits k with
  | zero =>
    rw [List.length_eq_zero_iff.mp (show bits.length = 0 by omega)]; rfl
  | succ n ih =>
    rw [block_step, pointer_slice_from, Bool.and_eq_true] at hs
    have ev := valid_of_pointer_byte_at p k _ hs.1
    change valid_pointer_bits p (k*8) 0 (padded (bits.take 8)) = _ at ev
    have eh := valid_pointer_bits_implies _ _ _ _ ev
    simp only [Nat.add_zero, padded, all_pointer_bits_from_app, Bool.and_eq_true] at eh
    have hfull : (bits.take 8).length = 8 := by
      by_contra ne
      have hpad := eh.2
      simp only [beq_eq_false_iff_ne.mpr ne, Bool.not_false, if_true] at hpad
      have := all_pointer_bits_from_repeat_psn _ _ _ hpad
      simp only [List.length_take] at *; omega
    have et := ih (bits.drop 8) (1+k) (drop_bound n bits hlen) hs.2
    calc
      all_pointer_bits_from p (8*k) bits =
          all_pointer_bits_from p (k*8) (bits.take 8 ++ bits.drop 8) := by
        rw [List.take_append_drop, Nat.mul_comm]
      _ = true := by
        rw [all_pointer_bits_from_app, eh.1, hfull, show k*8 + 8 = 8*(1+k) by omega, et]
        rfl

theorem pointer_slice_head (bits : List memory_bit) (n : Nat) :
    match bits with
    | .Bit_ptr q j :: _ => memory_bytes_to_pointer_slice (block bits (n+1)) =
        (if pointer_slice_from q (j/8) (block bits (n+1)) then some (q,j/8) else none)
    | _ => memory_bytes_to_pointer_slice (block bits (n+1)) = none := by
  cases bits with
  | nil => rfl
  | cons b l => cases b <;> rfl

theorem pointer_slice_mixed_unaligned (sz : Positive) {n : Nat} (bits : List memory_bit)
    {p : Pa.PTR.ptr} {k : Nat} (hlen : bits.length ≤ 8*(n+1)) (hn : (!is_pointer_chunk sz bits) = true)
    (hs : memory_bytes_to_pointer_slice (block bits (n+1)) = some (p,k)) :
    pointer_chunk_aligned sz k = false := by
  have hh := pointer_slice_head bits n
  cases bits with
  | nil => rw [hh] at hs; contradiction
  | cons b l =>
    cases b with
    | Bit_psn => rw [hh] at hs; contradiction
    | Bit_bit x => rw [hh] at hs; contradiction
    | Bit_ptr q j =>
      rw [hh] at hs
      split at hs
      · rename_i e
        cases hs
        have hall := pointer_slice_implies_bits _ _ _ _ hlen e
        have hj := hall
        simp only [all_pointer_bits_from, Bool.and_eq_true, beq_iff_eq] at hj
        have hj' : j = 8 * (j/8) := hj.1.2
        have run : all_pointer_bits_from p j (Bit_ptr p j :: l) = true := by
          conv_lhs => arg 2; rw [hj']
          exact hall
        apply Bool.eq_false_of_not_eq_true
        intro ha
        simp only [pointer_chunk_aligned, Bool.and_eq_true, beq_iff_eq] at ha
        have hjmod : j % sz.val = 0 := by
          have e' : j = j/8*8 := by omega
          rw [e']; exact ha.2
        simp [is_pointer_chunk, ha.1, hjmod, run] at hn
      · contradiction

theorem read_base_block_BYTE_Mixed {sz : Positive} (bits : List memory_bit)
    (hlen : bits.length = sz.val) (hp : (!is_pointer_chunk sz bits) = true)
    (hi : (!(bits.all is_int_bit)) = true) (hn : (!(bits.all is_poison_bit)) = true) :
    memory_bytes_to_dvalue_base
      ((Nseq 0 (store_size_dtyp (DTYPE_Base (DTYPE_B sz)))).map
        (memory_byte_of_dvalue_bv (BYTE_Mixed (bit_sz := sz) bits))) (DTYPE_B sz) =
      raise_ret (DVALUE_B sz (BYTE_Mixed bits)) := by
  change memory_bytes_to_dvalue_base (block bits (store_size_dtyp (DTYPE_Base (DTYPE_B sz)))) _ = _
  generalize hk : store_size_dtyp (DTYPE_Base (DTYPE_B sz)) = K
  rw [store_size_dtyp_bytes] at hk
  have hb : bits.length ≤ 8*K := by omega
  cases K with
  | zero => have := sz.property; omega
  | succ n =>
    have nap : all_poison_bytes (block bits (n+1)) = false := by
      apply Bool.eq_false_of_not_eq_true
      rw [all_poison_bytes_forallb]
      intro e
      rw [mixed_all_poison _ _ hb e] at hn
      contradiction
    have fb : memory_bytes_to_byte_value sz (block bits (n+1)) =
        raise_ret (memory_bytes_to_bits_value sz (block bits (n+1))) := by
      unfold memory_bytes_to_byte_value
      cases e : memory_bytes_to_pointer_slice (block bits (n+1)) with
      | none => rfl
      | some pair =>
        obtain ⟨p,k⟩ := pair
        simp [pointer_slice_mixed_unaligned sz bits hb hp e, pure, EOU_monad]
    have hbits : (get_bits_of_memory_byte_list sz.val (block bits (n+1)) []).reverse = bits := by
      rw [← hlen, get_bits_writer _ _ _ hb]; simp [List.reverseAux_eq]
    have hmix : (bits.any is_ptr_bit || bits.any is_poison_bit) = true := by
      cases h : bits.any is_ptr_bit with
      | true => rfl
      | false => exact not_all_int_no_ptr_pois bits hi h
    rw [memory_bytes_to_dvalue_base, if_neg (by simp [nap]), fb]
    change (if dvalue_bv_all_poison (memory_bytes_to_bits_value sz _) then _ else _) = _
    simp only [memory_bytes_to_bits_value, hbits, hmix, if_true, dvalue_bv_all_poison]
    have hnp : bits.all is_poison_bit = false := by simpa using hn
    simp [hnp, pure, EOU_monad]

theorem read_base_block (dtb : dtyp_base) (dv : dvalue_base) (hs : serializable_base dtb)
    (ht : dvalue_base_has_dtyp_base dv dtb = true) (hc : dvalue_base_canonical dv = true) :
    memory_bytes_to_dvalue_base ((Nseq 0 (store_size_dtyp (DTYPE_Base dtb))).map (base_byte_gen dv))
      dtb = raise_ret dv := by
  cases dv with
  | DVALUE_Pointer p =>
    cases dtb <;> simp [dvalue_base_has_dtyp_base] at ht
    exact read_base_block_pointer p
  | DVALUE_I sz x =>
    cases dtb <;> simp [dvalue_base_has_dtyp_base] at ht
    rename_i w
    have ew : sz = w := Subtype.ext ht
    subst w
    by_cases e : sz.val % 8 = 0
    · exact read_int_block_mult8 x e
    · exact read_int_block_mixed x e
  | DVALUE_Iptr x =>
    cases dtb <;> simp [dvalue_base_has_dtyp_base, serializable_base] at ht hs
  | DVALUE_Double d =>
    cases dtb <;> try contradiction
    rename_i fp
    cases fp <;> first | contradiction | exact read_base_block_double d
  | DVALUE_Float f =>
    cases dtb <;> try contradiction
    rename_i fp
    cases fp <;> first | contradiction | exact read_base_block_float f
  | DVALUE_Poison =>
    change memory_bytes_to_dvalue_base ((Nseq 0 _).map (fun _ ↦ poison_memory_byte)) dtb = _
    rw [map_const_Nseq]
    exact read_base_block_poison dtb hs
  | DVALUE_None =>
    cases dtb <;> simp [dvalue_base_has_dtyp_base, serializable_base] at ht hs
  | DVALUE_B sz bv =>
    cases dtb <;> simp [dvalue_base_has_dtyp_base] at ht
    rename_i w
    have ew : sz = w := Subtype.ext ht
    subst w
    cases bv with
    | BYTE_Pointer p k =>
      apply read_base_block_BYTE_Pointer
      simpa [dvalue_base_canonical, dvalue_bv_canonical] using hc
    | BYTE_I x => exact read_base_block_BYTE_I x
    | BYTE_Mixed bits =>
      simp only [dvalue_base_canonical, dvalue_bv_canonical, Bool.and_eq_true, beq_iff_eq] at hc
      exact read_base_block_BYTE_Mixed bits hc.1.1.1 hc.1.1.2 hc.1.2 hc.2

end Vellvm.Theory.MemoryBytesFacts
