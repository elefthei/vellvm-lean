import Vellvm.Semantics.MemoryBytes

namespace Vellvm.Theory.MemoryBytesFacts
open Semantics Semantics.EOU Semantics.MemoryBytes Semantics.DynamicValues
open Semantics.Interfaces.Params Semantics.Interfaces.Sizeof Syntax.DynamicTypes Utils.ListUtil

def tapad (ta : Option Nat) (x : Nat) : Nat :=
  match ta with
  | none => x
  | some a => pad_to a x

theorem tapad_ge (ta : Option Nat) (x : Nat) : x ≤ tapad ta x := by
  cases ta <;> simp [tapad, pad_to]

variable [Pa : Params]

theorem accumulate_poison_bytes_length (n : Nat) (acc : List memory_byte) :
    (accumulate_poison_bytes n acc).length = n + acc.length := rev_loop_acc_length _ _ _ _

theorem accumulate_padding_spec (offset : Nat) (ta : Option Nat) (acc : List memory_byte) :
    (accumulate_padding offset ta acc).1 = tapad ta offset ∧
    (accumulate_padding offset ta acc).2.length = acc.length + (tapad ta offset - offset) := by
  cases ta <;> simp [tapad, pad_to, accumulate_padding, accumulate_padding_bytes,
    accumulate_poison_bytes_length, Nat.add_comm]

theorem accumulate_padding_bytes_spec (offset n : Nat) (acc : List memory_byte) :
    (accumulate_padding_bytes offset n acc).1 = offset + n ∧
    (accumulate_padding_bytes offset n acc).2.length = acc.length + n := by
  simp [accumulate_padding_bytes, accumulate_poison_bytes_length, Nat.add_comm]

theorem acc_memory_bytes_of_dvalue_base_spec (dtb : dtyp_base) (dv : dvalue_base) (offset : Nat)
    (acc : List memory_byte) :
    (acc_memory_bytes_of_dvalue_base dtb dv offset acc).1 = store_size_dtyp (DTYPE_Base dtb) + offset ∧
    (acc_memory_bytes_of_dvalue_base dtb dv offset acc).2.length = acc.length + store_size_dtyp (DTYPE_Base dtb) := by
  simp [acc_memory_bytes_of_dvalue_base, rev_loop_acc_length, Nat.add_comm]

def struct_bytes_loop := @writeStruct Pa

def array_bytes_loop := @writeArray Pa

theorem ser_struct_unfold (packed : Bool) (dts : List dtyp) (p : Bool) (fields : List dvalue)
    (offset : Nat) (ta : Option Nat) (acc : List memory_byte) :
    acc_dvalue_to_memory_bytes_h (DTYPE_Struct packed dts) (DVALUE_Struct p fields) offset ta acc =
    struct_bytes_loop acc_dvalue_to_memory_bytes_h ta
      (if packed then none else some (max_preferred_dtyp_alignment dts)) fields dts offset acc := by
  rw [acc_dvalue_to_memory_bytes_h]
  rfl

def packed_vector_bytes := @writePacked Pa

theorem ser_array_unfold (vec : Bool) (sz : Nat) (t : dtyp) (p : Bool) (elts : List dvalue)
    (offset : Nat) (ta : Option Nat) (acc : List memory_byte) :
    acc_dvalue_to_memory_bytes_h (DTYPE_Array vec sz t) (DVALUE_Array p elts) offset ta acc =
    match packed_vector_type (DTYPE_Array vec sz t) with
    | some (_, m) => packed_vector_bytes m (DTYPE_Array vec sz t) elts offset ta acc
    | none => array_bytes_loop acc_dvalue_to_memory_bytes_h ta t
        (if vec then 0 else alloc_size_dtyp t - store_size_dtyp t) elts offset acc := by
  rw [acc_dvalue_to_memory_bytes_h]
  rfl

omit Pa in
theorem packed_vector_type_Some (dt : dtyp) {tb : dtyp_base} {m : Positive}
    (h : packed_vector_type dt = some (tb, m)) :
    ∃ sz, dt = DTYPE_Array true sz (DTYPE_Base tb) ∧ (tb = DTYPE_I m ∨ tb = DTYPE_B m) ∧ m.val % 8 ≠ 0 := by
  cases dt with
  | DTYPE_Array v sz t =>
    cases v <;> try contradiction
    cases t with
    | DTYPE_Base b =>
      cases b <;> simp only [packed_vector_type] at h <;> try contradiction
      all_goals split at h <;> cases h <;> exact ⟨sz, rfl, by simp, by assumption⟩
    | _ => contradiction
  | _ => contradiction

theorem store_size_packed_vector (dt : dtyp) {tb : dtyp_base} {m : Positive}
    (h : packed_vector_type dt = some (tb, m)) :
    ∃ sz, dt = DTYPE_Array true sz (DTYPE_Base tb) ∧ store_size_dtyp dt = (sz * m.val + 7) / 8 := by
  obtain ⟨sz, rfl, rfl | rfl, _⟩ := packed_vector_type_Some dt h
  · exact ⟨sz, rfl, store_size_dtyp_vector_int sz m⟩
  · exact ⟨sz, rfl, store_size_dtyp_vector_bytes sz m⟩

theorem store_size_unpacked_vector (sz : Nat) (t : dtyp)
    (h : packed_vector_type (DTYPE_Array true sz t) = none) :
    store_size_dtyp (DTYPE_Array true sz t) = sz * store_size_dtyp t := by
  have byteSized (m : Nat) (hm : m % 8 = 0) : (sz * m + 7) / 8 = sz * ((m + 7) / 8) := by
    obtain ⟨k, rfl⟩ := Nat.dvd_of_mod_eq_zero hm
    rw [show sz * (8 * k) + 7 = 7 + sz * k * 8 by ac_rfl, show 8 * k + 7 = 7 + k * 8 by ac_rfl]
    simp [Nat.add_mul_div_right]
  cases t with
  | DTYPE_Base b =>
    cases b <;> try solve | apply store_size_dtyp_vector <;> simp
    · rw [store_size_dtyp_vector_int, store_size_dtyp_int]
      apply byteSized; simpa [packed_vector_type] using h
    · rw [store_size_dtyp_vector_bytes, store_size_dtyp_bytes]
      apply byteSized; simpa [packed_vector_type] using h
  | _ => apply store_size_dtyp_vector <;> simp

theorem acc_bits_to_memory_bytes_length (n : Nat) (bits : List memory_bit) (acc : List memory_byte) :
    (acc_bits_to_memory_bytes n bits acc).length = n + acc.length := by
  induction n generalizing bits acc with
  | zero => simp [acc_bits_to_memory_bytes]
  | succ n ih => simp only [acc_bits_to_memory_bytes, ih, List.length_cons]; omega

theorem acc_packed_bits_to_memory_bytes_length (nbytes : Nat) (bits : List memory_bit) (acc : List memory_byte) :
    (acc_packed_bits_to_memory_bytes nbytes bits acc).length = acc.length + nbytes := by
  simp [acc_packed_bits_to_memory_bytes, acc_bits_to_memory_bytes_length, Nat.add_comm]

theorem packed_vector_bytes_spec (m : Positive) (dt : dtyp) (elts : List dvalue) (offset : Nat)
    (ta : Option Nat) (acc : List memory_byte) {offset' bs}
    (h : packed_vector_bytes m dt elts offset ta acc = raise_ret (offset', bs)) :
    offset' = tapad ta (offset + store_size_dtyp dt) ∧ bs.length = acc.length + (offset' - offset) := by
  obtain ⟨bits, _, hr⟩ := EOU_bind_ret_inv (map_monad (packed_elt_bits m) elts) _ _ h
  let bytes := acc_packed_bits_to_memory_bytes (store_size_dtyp dt) bits.flatten acc
  have hp : accumulate_padding (offset + store_size_dtyp dt) ta bytes = (offset', bs) :=
    Semantics.EOU.EOU.raise_ret.inj hr
  obtain ⟨ho, hl⟩ := accumulate_padding_spec (offset + store_size_dtyp dt) ta bytes
  rw [hp] at ho hl
  have hb := acc_packed_bits_to_memory_bytes_length (store_size_dtyp dt) bits.flatten acc
  have hg := tapad_ge ta (offset + store_size_dtyp dt)
  exact ⟨ho, by dsimp only [Prod.snd] at hl; change bytes.length = _ at hb; omega⟩

theorem ser_base_unfold (dtb : dtyp_base) (dv : dvalue_base) (offset : Nat) (ta : Option Nat)
    (acc : List memory_byte) :
    acc_dvalue_to_memory_bytes_h (DTYPE_Base dtb) (DVALUE_Base dv) offset ta acc =
    let (o, bs) := acc_memory_bytes_of_dvalue_base dtb dv offset acc
    raise_ret (accumulate_padding o ta bs) := by
  rw [acc_dvalue_to_memory_bytes_h]
  rfl

theorem ser_struct_poison_unfold (packed : Bool) (dts : List dtyp) (offset : Nat) (ta : Option Nat)
    (acc : List memory_byte) :
    acc_dvalue_to_memory_bytes_h (DTYPE_Struct packed dts) (DVALUE_Base DVALUE_Poison) offset ta acc =
    let (o, bs) := accumulate_padding_bytes offset (store_size_dtyp (DTYPE_Struct packed dts)) acc
    raise_ret (accumulate_padding o ta bs) := by
  rw [acc_dvalue_to_memory_bytes_h]
  rfl

theorem ser_array_poison_unfold (vec : Bool) (sz : Nat) (t : dtyp) (offset : Nat) (ta : Option Nat)
    (acc : List memory_byte) :
    acc_dvalue_to_memory_bytes_h (DTYPE_Array vec sz t) (DVALUE_Base DVALUE_Poison) offset ta acc =
    let (o, bs) := accumulate_padding_bytes offset (store_size_dtyp (DTYPE_Array vec sz t)) acc
    raise_ret (accumulate_padding o ta bs) := by
  rw [acc_dvalue_to_memory_bytes_h]
  rfl

def sfe_step (pad : Option Nat) (offset : Nat) (t : dtyp) : Nat :=
  tapad (pad.map fun _ ↦ (dtyp_alignment t).preferred_alignment) offset + alloc_size_dtyp t

private abbrev Serializer := dtyp → dvalue → Nat → Option Nat → List memory_byte → EOU (Nat × List memory_byte)

theorem struct_bytes_loop_nil (ser : Serializer) (ta pad : Option Nat) (offset : Nat) (acc : List memory_byte) :
    struct_bytes_loop ser ta pad [] [] offset acc =
    let (o, bs) := accumulate_padding offset pad acc
    raise_ret (accumulate_padding o ta bs) := rfl

theorem struct_bytes_loop_cons (ser : Serializer) (ta pad : Option Nat) (f : dvalue) (fs : List dvalue)
    (dt : dtyp) (dts : List dtyp) (offset : Nat) (acc : List memory_byte) :
    struct_bytes_loop ser ta pad (f :: fs) (dt :: dts) offset acc = (do
      let (o, a) := accumulate_padding offset (pad.map fun _ ↦ (dtyp_alignment dt).preferred_alignment) acc
      let (coff, bs) ← ser dt f 0 none a
      let (o', bs') := accumulate_padding_bytes (o + coff) (alloc_size_dtyp dt - store_size_dtyp dt) bs
      struct_bytes_loop ser ta pad fs dts o' bs') := rfl

theorem array_bytes_loop_nil (ser : Serializer) (ta : Option Nat) (dt : dtyp) (ep offset : Nat)
    (acc : List memory_byte) :
    array_bytes_loop ser ta dt ep [] offset acc = raise_ret (accumulate_padding offset ta acc) := rfl

theorem array_bytes_loop_cons (ser : Serializer) (ta : Option Nat) (dt : dtyp) (ep : Nat) (e : dvalue)
    (es : List dvalue) (offset : Nat) (acc : List memory_byte) :
    array_bytes_loop ser ta dt ep (e :: es) offset acc = (do
      let (coff, bs) ← ser dt e 0 none acc
      let (o, bs') := accumulate_padding_bytes (offset + coff) ep bs
      array_bytes_loop ser ta dt ep es o bs') := rfl

def ser_spec (dv : dvalue) : Prop := ∀ dt, dvalue_has_dtyp dv dt → ∀ ta acc offset' bs,
  acc_dvalue_to_memory_bytes_h dt dv 0 ta acc = raise_ret (offset', bs) →
  offset' = tapad ta (store_size_dtyp dt) ∧ bs.length = acc.length + offset'

theorem struct_bytes_loop_spec {fs ts} (ht : List.Forall₂ dvalue_has_dtyp fs ts) :
    List.Forall ser_spec fs → ∀ pad ta offset acc {offset' bs},
    struct_bytes_loop acc_dvalue_to_memory_bytes_h ta pad fs ts offset acc = raise_ret (offset', bs) →
    offset' = tapad ta (tapad pad (ts.foldl (sfe_step pad) offset)) ∧
    bs.length = acc.length + (offset' - offset) ∧ offset ≤ offset' := by
  induction ht with
  | nil =>
    intro _ pad ta offset acc offset' bs h
    let p := accumulate_padding offset pad acc
    have he : accumulate_padding p.1 ta p.2 = (offset', bs) := Semantics.EOU.EOU.raise_ret.inj h
    obtain ⟨p₁, p₂⟩ := accumulate_padding_spec offset pad acc
    change p.1 = _ at p₁
    change p.2.length = _ at p₂
    obtain ⟨q₁, q₂⟩ := accumulate_padding_spec p.1 ta p.2
    rw [he] at q₁ q₂
    have g₁ := tapad_ge pad offset
    have g₂ := tapad_ge ta p.1
    simp only [Prod.fst, Prod.snd] at q₁ q₂
    exact ⟨q₁.trans (congrArg (tapad ta) p₁), by omega, by omega⟩
  | @cons f t fs ts hft _ ih =>
    intro hs pad ta offset acc offset' bs h
    obtain ⟨hf, hfs⟩ := (List.forall_cons _ _ _).mp hs
    let q := pad.map fun _ ↦ (dtyp_alignment t).preferred_alignment
    let p := accumulate_padding offset q acc
    obtain ⟨⟨coff, cs⟩, hc, hr⟩ := EOU_bind_ret_inv
      (acc_dvalue_to_memory_bytes_h t f 0 none p.2) _ _ h
    obtain ⟨ec, lc⟩ := hf t hft none p.2 coff cs hc
    change coff = store_size_dtyp t at ec
    let gap := alloc_size_dtyp t - store_size_dtyp t
    let r := accumulate_padding_bytes (p.1 + coff) gap cs
    change struct_bytes_loop acc_dvalue_to_memory_bytes_h ta pad fs ts r.1 r.2 = _ at hr
    obtain ⟨eo, el, eg⟩ := ih hfs pad ta r.1 r.2 hr
    obtain ⟨p₁, p₂⟩ := accumulate_padding_spec offset q acc
    change p.1 = _ at p₁
    change p.2.length = _ at p₂
    obtain ⟨r₁, r₂⟩ := accumulate_padding_bytes_spec (p.1 + coff) gap cs
    change r.1 = _ at r₁
    change r.2.length = _ at r₂
    have gp := tapad_ge q offset
    have gs := store_le_alloc t
    have step : r.1 = sfe_step pad offset t := by
      change r.1 = tapad q offset + alloc_size_dtyp t
      dsimp only [gap] at r₁
      omega
    exact ⟨by simpa only [List.foldl_cons, ← step] using eo, by omega, by omega⟩

theorem array_bytes_loop_spec {elts t} :
    List.Forall (fun e ↦ dvalue_has_dtyp e t) elts → List.Forall ser_spec elts →
    ∀ ta ep offset acc {offset' bs},
    array_bytes_loop acc_dvalue_to_memory_bytes_h ta t ep elts offset acc = raise_ret (offset', bs) →
    offset' = tapad ta (offset + elts.length * (store_size_dtyp t + ep)) ∧
    bs.length = acc.length + (offset' - offset) ∧ offset ≤ offset' := by
  induction elts with
  | nil =>
    intro _ _ ta ep offset acc offset' bs h
    have he : accumulate_padding offset ta acc = (offset', bs) := Semantics.EOU.EOU.raise_ret.inj h
    obtain ⟨ho, hl⟩ := accumulate_padding_spec offset ta acc
    rw [he] at ho hl
    change offset' = tapad ta offset at ho
    change bs.length = acc.length + (tapad ta offset - offset) at hl
    have hg := tapad_ge ta offset
    exact ⟨by simpa using ho, by omega, by omega⟩
  | cons e es ih =>
    intro ht hs ta ep offset acc offset' bs h
    obtain ⟨ht, hts⟩ := (List.forall_cons _ _ _).mp ht
    obtain ⟨hs, hss⟩ := (List.forall_cons _ _ _).mp hs
    obtain ⟨⟨coff, cs⟩, hc, hr⟩ := EOU_bind_ret_inv
      (acc_dvalue_to_memory_bytes_h t e 0 none acc) _ _ h
    obtain ⟨ec, lc⟩ := hs t ht none acc coff cs hc
    change coff = store_size_dtyp t at ec
    let p := accumulate_padding_bytes (offset + coff) ep cs
    change array_bytes_loop acc_dvalue_to_memory_bytes_h ta t ep es p.1 p.2 = _ at hr
    obtain ⟨eo, el, eg⟩ := ih hts hss ta ep p.1 p.2 hr
    obtain ⟨p₁, p₂⟩ := accumulate_padding_bytes_spec (offset + coff) ep cs
    change p.1 = _ at p₁
    change p.2.length = _ at p₂
    refine ⟨eo.trans (congrArg (tapad ta) ?_), by omega, by omega⟩
    rw [List.length_cons, Nat.succ_mul]; omega

private theorem pad_from_zero {n offset' : Nat} {ta : Option Nat} {acc bs : List memory_byte}
    (p : Nat × List memory_byte) (h₁ : p.1 = n) (h₂ : p.2.length = acc.length + n)
    (h : accumulate_padding p.1 ta p.2 = (offset', bs)) :
    offset' = tapad ta n ∧ bs.length = acc.length + offset' := by
  obtain ⟨ho, hl⟩ := accumulate_padding_spec p.1 ta p.2
  rw [h, h₁] at ho hl
  simp only [Prod.fst, Prod.snd] at ho hl
  have hg := tapad_ge ta n
  exact ⟨ho, by omega⟩

theorem acc_dvalue_to_memory_bytes_h_spec {dv dt} (ht : dvalue_has_dtyp dv dt) (ta : Option Nat)
    (acc : List memory_byte) {offset' bs}
    (h : acc_dvalue_to_memory_bytes_h dt dv 0 ta acc = raise_ret (offset', bs)) :
    offset' = tapad ta (store_size_dtyp dt) ∧ bs.length = acc.length + offset' := by
  suffices s : ser_spec dv from s dt ht ta acc offset' bs h
  clear ht h
  apply dvalue_ind ser_spec _ _ _ dv
  · intro db t ht ta acc o bs h
    have poison_case (n : Nat) :
        raise_ret (accumulate_padding (accumulate_padding_bytes 0 n acc).1 ta
          (accumulate_padding_bytes 0 n acc).2) = raise_ret (o, bs) →
        o = tapad ta n ∧ bs.length = acc.length + o := by
      obtain ⟨h₁, h₂⟩ := accumulate_padding_bytes_spec 0 n acc
      exact fun he ↦ pad_from_zero _ (by simpa using h₁) h₂ (Semantics.EOU.EOU.raise_ret.inj he)
    cases t with
    | DTYPE_Base b =>
      rw [ser_base_unfold] at h
      obtain ⟨h₁, h₂⟩ := acc_memory_bytes_of_dvalue_base_spec b db 0 acc
      exact pad_from_zero _ (by simpa using h₁) h₂ (Semantics.EOU.EOU.raise_ret.inj h)
    | DTYPE_Struct p ts =>
      cases ht
      rw [ser_struct_poison_unfold] at h
      exact poison_case _ h
    | DTYPE_Array v n t =>
      cases ht
      rw [ser_array_poison_unfold] at h
      exact poison_case _ h
  · intro p fs ih dt ht ta acc o bs h
    cases ht with
    | DVALUE_Struct_typ =>
      rw [ser_struct_unfold] at h
      obtain ⟨eo, el, _⟩ := struct_bytes_loop_spec (by assumption)
        (List.forall_iff_forall_mem.mpr ih) _ _ _ _ h
      refine ⟨eo.trans (congrArg (tapad ta) ?_), by simpa using el⟩
      cases p
      · rw [store_size_dtyp_Struct]; rfl
      · rw [store_size_dtyp_Packed_struct]; rfl
  · intro v es ih dt ht ta acc o bs h
    cases ht with
    | DVALUE_Array_typ =>
      rename_i n t _ hs hn _
      rw [ser_array_unfold] at h
      cases hp : packed_vector_type (DTYPE_Array v n t) with
      | some tm =>
        obtain ⟨tb, m⟩ := tm
        rw [hp] at h
        simpa using packed_vector_bytes_spec _ _ _ _ _ _ h
      | none =>
        rw [hp] at h
        obtain ⟨eo, el, _⟩ := array_bytes_loop_spec
          (List.forall_iff_forall_mem.mpr hs) (List.forall_iff_forall_mem.mpr ih)
          _ _ _ _ h
        refine ⟨eo.trans (congrArg (tapad ta) ?_), by simpa using el⟩
        rw [hn, Nat.zero_add]
        cases v with
        | false =>
          rw [store_size_dtyp_array]
          congr 1
          have := store_le_alloc t
          change store_size_dtyp t + (alloc_size_dtyp t - store_size_dtyp t) = alloc_size_dtyp t
          omega
        | true => simp [store_size_unpacked_vector n t hp]

theorem dvalue_to_memory_bytes_sizeof {dt dv} (ta : Option Nat) {bytes : List memory_byte}
    (ht : dvalue_has_dtyp dv dt) : dvalue_to_memory_bytes dt dv ta = raise_ret bytes →
    bytes.length = match ta with
      | none => store_size_dtyp dt
      | some a => pad_to a (store_size_dtyp dt) := by
  intro h
  obtain ⟨⟨o, bs⟩, hw, hr⟩ := EOU_bind_ret_inv (acc_dvalue_to_memory_bytes_h dt dv 0 ta []) _ _ h
  have hb : bs.reverse = bytes := Semantics.EOU.EOU.raise_ret.inj hr
  obtain ⟨eo, el⟩ := acc_dvalue_to_memory_bytes_h_spec ht ta [] hw
  change bytes.length = tapad ta (store_size_dtyp dt)
  rw [← hb, List.length_reverse, el, List.length_nil, Nat.zero_add, eo]

theorem concat_bytes_Z_mixed_cons2 (extra : Nat) (b d : memory_byte) (rest : List memory_byte) :
    concat_bytes_Z_mixed extra (b :: d :: rest) = (do
      let z ← memory_byte_to_Z b
      let r ← concat_bytes_Z_mixed extra (d :: rest)
      pure (z + 256 * r) : EOUP Int) := by
  cases b <;> rw [concat_bytes_Z_mixed]

end Vellvm.Theory.MemoryBytesFacts
