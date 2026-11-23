import Vellvm.Theory.MemoryBytesFacts.Mixed

namespace Vellvm.Theory.MemoryBytesFacts
open Semantics Semantics.Interfaces.Params Semantics.Interfaces.Sizeof Semantics.DynamicValues
open Semantics.EOU Semantics.MemoryBytes Syntax.DynamicTypes Utils.ListUtil

variable [Pa : Params]

theorem accumulate_padding_bytes_shape (offset n : Nat) (acc : List memory_byte) :
    accumulate_padding_bytes offset n acc = (offset + n, List.replicate n poison_memory_byte ++ acc) := by
  simp [accumulate_padding_bytes, accumulate_poison_bytes_app]

theorem accumulate_padding_shape (offset : Nat) (q : Option Nat) (acc : List memory_byte) :
    accumulate_padding offset q acc =
      (tapad q offset, List.replicate (tapad q offset - offset) poison_memory_byte ++ acc) := by
  cases q <;> simp [accumulate_padding, accumulate_padding_bytes_shape, tapad, pad_to]

theorem poison_block_shape (n : Nat) (ta : Option Nat) (acc : List memory_byte) :
    (let (o, bs) := accumulate_padding_bytes 0 n acc
     pure (accumulate_padding o ta bs) : EOU (Nat × List memory_byte)) =
    raise_ret (tapad ta n, List.replicate (tapad ta n) poison_memory_byte ++ acc) := by
  have h := tapad_ge ta n
  simp only [accumulate_padding_bytes_shape, Nat.zero_add, accumulate_padding_shape,
    ← List.append_assoc, List.replicate_append_replicate, Nat.sub_add_cancel h] <;> rfl

theorem ser_poison_agg (dt : dtyp) (ta : Option Nat) (acc : List memory_byte)
    (h : match dt with | .DTYPE_Base _ => False | _ => True) :
    acc_dvalue_to_memory_bytes_h dt (DVALUE_Base DVALUE_Poison) 0 ta acc =
      raise_ret (tapad ta (store_size_dtyp dt),
        List.replicate (tapad ta (store_size_dtyp dt)) poison_memory_byte ++ acc) := by
  cases dt with
  | DTYPE_Base _ => exact False.elim h
  | DTYPE_Struct _ _ => rw [ser_struct_poison_unfold]; apply poison_block_shape
  | DTYPE_Array _ _ _ => rw [ser_array_poison_unfold]; apply poison_block_shape

theorem poison_split_app_live (w extra : List memory_byte) (h : (poison_split w).2 ≠ []) :
    poison_split (w ++ extra) = ((poison_split w).1, (poison_split w).2 ++ extra) := by
  induction w with
  | nil => exact (h rfl).elim
  | cons b w ih =>
    cases hb : is_all_poison_byte b with
    | false => simp [poison_split, hb]
    | true =>
      cases hs : poison_split w with
      | mk k tail =>
        simp [poison_split, hb, hs] at h ⊢
        simp [ih (by simpa [hs] using h), hs]

theorem poison_split_app_poison (w extra : List memory_byte) (h : (poison_split w).2 = []) :
    poison_split (w ++ extra) = ((poison_split w).1 + (poison_split extra).1, (poison_split extra).2) := by
  induction w with
  | nil => simp [poison_split]
  | cons b w ih =>
    cases hb : is_all_poison_byte b with
    | false => simp [poison_split, hb] at h
    | true =>
      cases hs : poison_split w with
      | mk k tail =>
        simp [poison_split, hb, hs] at h ⊢
        simp [ih (by simpa [hs] using h), hs, Nat.add_assoc]

theorem read_base_trailing (dtb : dtyp_base) (w extra : List memory_byte)
    (h : store_size_dtyp (DTYPE_Base dtb) ≤ w.length) :
    memory_bytes_to_dvalue (w ++ extra) (DTYPE_Base dtb) = memory_bytes_to_dvalue w (DTYPE_Base dtb) := by
  simp only [memory_bytes_to_dvalue, List.take_append_of_le_length h]

abbrev read_struct_loop (rd : List memory_byte → dtyp → EOU dvalue) := readStruct rd

theorem read_struct_unfold (packed : Bool) (dts : List dtyp) (dbs : List memory_byte) :
    memory_bytes_to_dvalue dbs (DTYPE_Struct packed dts) =
      (let (np, rest) := poison_split dbs
       match rest with
       | [] => pure (poison_of_dtyp (DTYPE_Struct packed dts))
       | _ :: _ => canonicalize_agg (DTYPE_Struct packed dts) <$>
           read_struct_loop memory_bytes_to_dvalue np
             (if packed then none else some (max_preferred_dtyp_alignment dts)) 0 dts dbs) := by
  rw [memory_bytes_to_dvalue]
  cases poison_split dbs with
  | mk np rest => cases rest <;> rfl

theorem poison_split_prefix (l : List memory_byte) :
    (take (poison_split l).1 l).all is_all_poison_byte = true := by
  induction l with
  | nil => rfl
  | cons b l ih =>
    cases hb : is_all_poison_byte b with
    | false => simp [poison_split, hb, take]
    | true =>
      cases hs : poison_split l with
      | mk k tail =>
        simpa [poison_split, hb, hs, Nat.one_add, take] using (show
          (take k l).all is_all_poison_byte = true by simpa [hs] using ih)

theorem forallb_head_false (b : memory_byte) (l : List memory_byte)
    (h : is_all_poison_byte b = false) : (b :: l).all is_all_poison_byte = false := by
  simp [h]

theorem base_block_not_all_poison (dtb : dtyp_base) {dv : dvalue_base}
    (hs : serializable_base dtb) (ht : dvalue_base_has_dtyp_base dv dtb = true)
    (hc : dvalue_base_canonical dv = true) (hn : dv ≠ DVALUE_Poison) :
    ((Nseq 0 (store_size_dtyp (DTYPE_Base dtb))).map (base_byte_gen dv)).all is_all_poison_byte = false := by
  have hpos := serializable_base_pos dtb hs
  cases dv with
  | DVALUE_Poison => exact (hn rfl).elim
  | DVALUE_None => cases dtb <;> first | contradiction | cases ht | exact False.elim hs
  | DVALUE_B sz bv =>
    cases dtb <;> try (solve | cases ht)
    rename_i width
    apply Bool.eq_false_iff.mpr
    intro hall
    have hr := read_base_block (DTYPE_B width) (DVALUE_B sz bv) hs ht hc
    simp only [memory_bytes_to_dvalue_base, all_poison_bytes_forallb, hall, if_true] at hr
    cases hr
  | _ => cases he : store_size_dtyp (DTYPE_Base dtb) <;> first | omega | rfl

def rt_spec (dv : dvalue) : Prop :=
  ∀ dt, dvalue_has_dtyp dv dt → serializable dt → ∀ ta acc offset' bs,
    acc_dvalue_to_memory_bytes_h dt dv 0 ta acc = raise_ret (offset', bs) →
      ∃ w, bs = w ++ acc ∧ w.length = tapad ta (store_size_dtyp dt) ∧
        memory_bytes_to_dvalue w.reverse dt = pure dv ∧
        (dv ≠ poison_of_dtyp dt → w.reverse.all is_all_poison_byte = false)

abbrev read_array_loop (rd : List memory_byte → dtyp → EOU dvalue) := readArray rd

def packed_vector_elts (tb : dtyp_base) (m : Positive) (sz : Nat) (dbs : List memory_byte) :
    List dvalue :=
  packed_bits_to_elts tb m sz (get_bits_of_memory_byte_list (sz * m.val) dbs []).reverse

theorem read_array_unfold (vec : Bool) (sz : Nat) (t : dtyp) (dbs : List memory_byte) :
    memory_bytes_to_dvalue dbs (DTYPE_Array vec sz t) =
      (let (np, rest) := poison_split dbs
       match rest with
       | [] => pure (poison_of_dtyp (DTYPE_Array vec sz t))
       | _ :: _ => match packed_vector_type (DTYPE_Array vec sz t) with
         | some (tb, m) => pure (canonicalize_agg (DTYPE_Array vec sz t) (packed_vector_elts tb m sz dbs))
         | none => do
           let es ← read_array_loop memory_bytes_to_dvalue np
             (if vec then store_size_dtyp t else alloc_size_dtyp t) t sz 0 dbs
           pure (canonicalize_agg (DTYPE_Array vec sz t) es)) := by
  rw [memory_bytes_to_dvalue]
  cases poison_split dbs with
  | mk np rest =>
    cases rest with
    | nil => rfl
    | cons _ _ => cases packed_vector_type (DTYPE_Array vec sz t) <;> rfl

theorem read_array_loop_cons (rd : List memory_byte → dtyp → EOU dvalue) (np stride : Nat)
    (t : dtyp) (n offset : Nat) (dbs : List memory_byte) :
    read_array_loop rd np stride t (n+1) offset dbs =
      ((if offset + store_size_dtyp t ≤ np then pure (poison_of_dtyp t)
        else rd (take (store_size_dtyp t) dbs) t) >>= fun e ↦
       read_array_loop rd np stride t n (offset + stride) (drop stride dbs) >>= fun es ↦
       pure (e :: es)) := by
  by_cases h : offset + store_size_dtyp t ≤ np <;> simp [read_array_loop, readArray, readArrayOn, h]

theorem forallb_poison_repeat (k : Nat) : (List.replicate k poison_memory_byte).all is_all_poison_byte = true := by
  simp [List.all_replicate, is_all_poison_memory_byte]

theorem forallb_sub (l : List memory_byte) {n : Nat} (i m : Nat) (hle : i + m ≤ n)
    (h : (take n l).all is_all_poison_byte = true) :
    (take m (drop i l)).all is_all_poison_byte = true := by
  have h' := forallb_take_pres _ _ m (forallb_drop_pres _ _ i h)
  rwa [drop_take, take_take_le _ _ _ (by omega)] at h'

theorem read_struct_loop_cons (rd : List memory_byte → dtyp → EOU dvalue) (np : Nat)
    (pad : Option Nat) (offset : Nat) (dt : dtyp) (dts : List dtyp) (dbs : List memory_byte) :
    read_struct_loop rd np pad offset (dt :: dts) dbs =
      (let n := if pad.isSome then pad_amount (dtyp_alignment dt).preferred_alignment offset else 0
       let dbs' := drop n dbs
       let start := offset + n
       (if start + store_size_dtyp dt ≤ np then pure (poison_of_dtyp dt)
        else rd (take (store_size_dtyp dt) dbs') dt) >>= fun f ↦
       read_struct_loop rd np pad (start + alloc_size_dtyp dt) dts (drop (alloc_size_dtyp dt) dbs') >>=
         fun fs ↦ pure (f :: fs)) := by
  let n := if pad.isSome then pad_amount (dtyp_alignment dt).preferred_alignment offset else 0
  by_cases h : offset + n + store_size_dtyp dt ≤ np <;>
    dsimp only [n] at h <;> simp only [read_struct_loop, readStruct, readStructOn, h, if_true, if_false]

private theorem after_prefix (pre rest : List memory_byte) (offset np : Nat)
    (h : (take (np - offset) (pre ++ rest)).all is_all_poison_byte = true) :
    (take (np - (offset + pre.length)) rest).all is_all_poison_byte = true := by
  have hh := forallb_drop_pres _ _ pre.length h
  rwa [drop_take, drop_app_exact pre rest _ rfl, Nat.sub_sub] at hh

/-- A skipped slot is entirely inside the poison prefix, so its liveness clause identifies its value. -/
private theorem read_slot (dt : dtyp) (v : dvalue) (w extra : List memory_byte) (start np : Nat)
    (hlen : w.length = store_size_dtyp dt) (hr : memory_bytes_to_dvalue w dt = pure v)
    (hl : v ≠ poison_of_dtyp dt → w.all is_all_poison_byte = false)
    (hp : (take (np - start) (w ++ extra)).all is_all_poison_byte = true) :
    (if start + store_size_dtyp dt ≤ np then pure (poison_of_dtyp dt)
     else memory_bytes_to_dvalue (take (store_size_dtyp dt) (w ++ extra)) dt) = pure v := by
  rw [take_app_exact w extra _ hlen]
  split
  · rename_i hskip
    have hall := forallb_sub (w ++ extra) 0 (store_size_dtyp dt) (n := np - start) (by omega) hp
    rw [drop_nil, take_app_exact w extra _ hlen] at hall
    by_cases h : v = poison_of_dtyp dt
    · rw [h]
    · rw [hl h] at hall; contradiction
  · exact hr

theorem struct_loop_read {fields : List dvalue} {dts : List dtyp}
    (ht : List.Forall₂ dvalue_has_dtyp fields dts) :
    List.Forall rt_spec fields → FORALL serializable dts →
    ∀ (ta pad : Option Nat) (offset : Nat) (acc : List memory_byte) {offset' : Nat} {bs : List memory_byte},
      struct_bytes_loop acc_dvalue_to_memory_bytes_h ta pad fields dts offset acc = raise_ret (offset', bs) →
      ∃ w, bs = w ++ acc ∧ w.length = offset' - offset ∧ offset ≤ offset' ∧
        (fields_all_poison dts fields = false → w.reverse.all is_all_poison_byte = false) ∧
        (∀ np extra, (take (np - offset) (w.reverse ++ extra)).all is_all_poison_byte = true →
          read_struct_loop memory_bytes_to_dvalue np pad offset dts (w.reverse ++ extra) = pure fields) := by
  induction ht with
  | nil =>
    intro _ _ ta pad offset acc offset' bs h
    simp only [struct_bytes_loop_nil, accumulate_padding_shape] at h
    rcases Prod.mk.inj (EOU.raise_ret.inj h) with ⟨rfl, rfl⟩
    have h₁ := tapad_ge pad offset
    have h₂ := tapad_ge ta (tapad pad offset)
    refine ⟨List.replicate _ poison_memory_byte ++ List.replicate _ poison_memory_byte,
      (List.append_assoc _ _ _).symm, ?_, by omega, ?_, ?_⟩
    · simp only [List.length_append, List.length_replicate]; omega
    · intro hp; cases hp
    · intros; rfl
  | @cons f dt fs dts hf _ ih =>
    intro hrs hs ta pad offset acc offset' bs h
    rw [List.forall_cons] at hrs
    let q := pad.map (fun _ ↦ (dtyp_alignment dt).preferred_alignment)
    let start := tapad q offset
    let lead := List.replicate (start - offset) poison_memory_byte
    let gap := List.replicate (alloc_size_dtyp dt - store_size_dtyp dt) poison_memory_byte
    rw [struct_bytes_loop_cons, accumulate_padding_shape] at h
    change EOU.bind (acc_dvalue_to_memory_bytes_h dt f 0 none (lead ++ acc)) _ = _ at h
    obtain ⟨⟨coff, cbs⟩, hc, htail⟩ := EOU_bind_ret_inv _ _ _ h
    have hrt : rt_spec f := hrs.1
    obtain ⟨wf, hw, hlen, hread, hlive⟩ := hrt dt hf hs.1 none _ _ _ hc
    have hcoff : coff = store_size_dtyp dt :=
      (acc_dvalue_to_memory_bytes_h_spec hf none _ hc).1
    change wf.length = store_size_dtyp dt at hlen
    subst coff
    change (let (o, b) := accumulate_padding_bytes (start + store_size_dtyp dt)
              (alloc_size_dtyp dt - store_size_dtyp dt) cbs
            struct_bytes_loop acc_dvalue_to_memory_bytes_h ta pad fs dts o b) = _ at htail
    rw [accumulate_padding_bytes_shape] at htail
    have hsa := store_le_alloc dt
    have ho : start + store_size_dtyp dt + (alloc_size_dtyp dt - store_size_dtyp dt) =
        start + alloc_size_dtyp dt := by omega
    change struct_bytes_loop _ ta pad fs dts _ (gap ++ cbs) = _ at htail
    rw [ho] at htail
    obtain ⟨wr, hbs, hrlen, hle, hrlive, hrread⟩ := ih hrs.2 hs.2 ta pad _ _ htail
    have h₀ : offset ≤ start := tapad_ge q offset
    have hlead : lead.length = start - offset := List.length_replicate
    have hgap : gap.length = alloc_size_dtyp dt - store_size_dtyp dt := List.length_replicate
    have hstart : offset + lead.length = start := by omega
    have hrlead : lead.reverse = lead := List.reverse_replicate
    have hrgap : gap.reverse = gap := List.reverse_replicate
    have hrev : (wr ++ gap ++ wf ++ lead).reverse = lead ++ wf.reverse ++ gap ++ wr.reverse := by
      simp only [List.reverse_append, hrlead, hrgap, List.append_assoc]
    refine ⟨wr ++ gap ++ wf ++ lead, ?_, ?_, by omega, ?_, ?_⟩
    · simp only [hbs, hw, List.append_assoc]
    · simp only [List.length_append]; omega
    · intro hn
      change ((dtyp_is_empty dt || dvalue_is_poison f) && fields_all_poison dts fs) = false at hn
      rcases Bool.and_eq_false_iff.mp hn with h | h
      · obtain ⟨hempty, hf'⟩ := Bool.or_eq_false_iff.mp h
        have hne : f ≠ poison_of_dtyp dt := by
          rw [poison_of_dtyp_nonempty dt hempty]
          exact dvalue_is_poison_false _ hf'
        simp [hrev, List.all_append, hlive hne]
      · simp [hrev, List.all_append, hrlive h]
    · intro np extra hp
      rw [hrev] at hp ⊢
      simp only [List.append_assoc] at hp ⊢
      have hp' := after_prefix lead _ offset np hp
      rw [hstart] at hp'
      have hwlen : wf.reverse.length = store_size_dtyp dt := by simpa using hlen
      have hslotlen : (wf.reverse ++ gap).length = alloc_size_dtyp dt := by
        simp only [List.length_append, hwlen]; omega
      have hchild := read_slot dt f wf.reverse (gap ++ (wr.reverse ++ extra)) start np
        hwlen hread hlive hp'
      have htpre := after_prefix (wf.reverse ++ gap) (wr.reverse ++ extra) start np
        (by simpa only [List.append_assoc] using hp')
      rw [hslotlen] at htpre
      have hpad : (if pad.isSome then pad_amount (dtyp_alignment dt).preferred_alignment offset
                   else 0) = lead.length := by
        cases pad <;> simp [lead, start, q, tapad, pad_to]
      have hd : drop (alloc_size_dtyp dt) (wf.reverse ++ (gap ++ (wr.reverse ++ extra))) =
          wr.reverse ++ extra := by
        rw [← List.append_assoc wf.reverse gap, drop_app_exact _ _ _ hslotlen]
      rw [read_struct_loop_cons]
      dsimp only
      rw [hpad, drop_app_exact lead _ _ rfl, hstart, hchild, hd, hrread np extra htpre]
      <;> rfl

theorem array_loop_read {elts : List dvalue} {t : dtyp} (ht : List.Forall (fun e ↦ dvalue_has_dtyp e t) elts) :
    List.Forall rt_spec elts → serializable t →
    ∀ (ta : Option Nat) (ep offset : Nat) (acc : List memory_byte) {offset' : Nat} {bs : List memory_byte},
      array_bytes_loop acc_dvalue_to_memory_bytes_h ta t ep elts offset acc = raise_ret (offset', bs) →
      ∃ w, bs = w ++ acc ∧ w.length = offset' - offset ∧ offset ≤ offset' ∧
        (dtyp_is_empty t = false → elts.all dvalue_is_poison = false → w.reverse.all is_all_poison_byte = false) ∧
        (∀ np extra, (take (np - offset) (w.reverse ++ extra)).all is_all_poison_byte = true →
          read_array_loop memory_bytes_to_dvalue np (store_size_dtyp t + ep) t elts.length offset
            (w.reverse ++ extra) = pure elts) := by
  induction elts with
  | nil =>
    intro _ _ ta ep offset acc offset' bs h
    rw [array_bytes_loop_nil, accumulate_padding_shape] at h
    rcases Prod.mk.inj (EOU.raise_ret.inj h) with ⟨rfl, rfl⟩
    refine ⟨_, rfl, List.length_replicate, tapad_ge ta offset, ?_, ?_⟩
    · intro _ hp; cases hp
    · intros; rfl
  | cons e es ih =>
    intro hrs hs ta ep offset acc offset' bs h
    rw [List.forall_cons] at ht hrs
    rw [array_bytes_loop_cons] at h
    obtain ⟨⟨coff, cbs⟩, hc, htail⟩ := EOU_bind_ret_inv _ _ _ h
    have hrt : rt_spec e := hrs.1
    obtain ⟨we, hw, hlen, hread, hlive⟩ := hrt t ht.1 hs none acc _ _ hc
    have hcoff : coff = store_size_dtyp t :=
      (acc_dvalue_to_memory_bytes_h_spec ht.1 none acc hc).1
    change we.length = store_size_dtyp t at hlen
    subst coff
    change (let (o, b) := accumulate_padding_bytes (offset + store_size_dtyp t) ep cbs
            array_bytes_loop acc_dvalue_to_memory_bytes_h ta t ep es o b) = _ at htail
    rw [accumulate_padding_bytes_shape] at htail
    let gap := List.replicate ep poison_memory_byte
    change array_bytes_loop _ ta t ep es (offset + store_size_dtyp t + ep) (gap ++ cbs) = _ at htail
    obtain ⟨wr, hbs, hrlen, hle, hrlive, hrread⟩ := ih ht.2 hrs.2 hs ta ep _ _ htail
    have hgap : gap.length = ep := List.length_replicate
    have hrgap : gap.reverse = gap := List.reverse_replicate
    have hrev : (wr ++ gap ++ we).reverse = we.reverse ++ gap ++ wr.reverse := by
      simp only [List.reverse_append, hrgap, List.append_assoc]
    refine ⟨wr ++ gap ++ we, ?_, ?_, by omega, ?_, ?_⟩
    · simp only [hbs, hw, List.append_assoc]
    · simp only [List.length_append]; omega
    · intro hne hn
      rcases Bool.and_eq_false_iff.mp hn with h | h
      · have he : e ≠ poison_of_dtyp t := by
          rw [poison_of_dtyp_nonempty t hne]
          exact dvalue_is_poison_false _ h
        simp [hrev, List.all_append, hlive he]
      · simp [hrev, List.all_append, hrlive hne h]
    · intro np extra hp
      rw [hrev] at hp ⊢
      simp only [List.append_assoc] at hp ⊢
      have hwlen : we.reverse.length = store_size_dtyp t := by simpa using hlen
      have hslotlen : (we.reverse ++ gap).length = store_size_dtyp t + ep := by
        simp only [List.length_append, hwlen, hgap]
      have hchild := read_slot t e we.reverse (gap ++ (wr.reverse ++ extra)) offset np
        hwlen hread hlive hp
      have htpre := after_prefix (we.reverse ++ gap) (wr.reverse ++ extra) offset np
        (by simpa only [List.append_assoc] using hp)
      rw [hslotlen, ← Nat.add_assoc] at htpre
      have hd : drop (store_size_dtyp t + ep) (we.reverse ++ (gap ++ (wr.reverse ++ extra))) =
          wr.reverse ++ extra := by
        rw [← List.append_assoc we.reverse gap, drop_app_exact _ _ _ hslotlen]
      rw [List.length_cons, read_array_loop_cons, hchild, hd, ← Nat.add_assoc, hrread np extra htpre]
      <;> rfl

end Vellvm.Theory.MemoryBytesFacts
