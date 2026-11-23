import Vellvm.Theory.MemoryBytesFacts.Aggregate
import Vellvm.Theory.MemoryBytesFacts.Packed

namespace Vellvm.Theory.MemoryBytesFacts
open Semantics.DynamicValues Semantics.EOU Semantics.MemoryBytes Semantics.Interfaces.Params
open Semantics.Interfaces.Sizeof Syntax.DynamicTypes Utils.ListUtil

variable [Pa : Params]

private abbrev Witness (dv : dvalue) (dt : dtyp) (ta : Option Nat) (acc bs : List memory_byte) :=
  ∃ w, bs = w ++ acc ∧ w.length = tapad ta (store_size_dtyp dt) ∧
    memory_bytes_to_dvalue w.reverse dt = raise_ret dv ∧
    (dv ≠ poison_of_dtyp dt → w.reverse.all is_all_poison_byte = false)

private theorem finishBlock {dv dt ta acc off bs} (typed : dvalue_has_dtyp dv dt)
    (hw : acc_dvalue_to_memory_bytes_h dt dv 0 ta acc = raise_ret (off, bs)) (w : List memory_byte)
    (written : bs = w ++ acc) (readback : memory_bytes_to_dvalue w.reverse dt = raise_ret dv)
    (live : dv ≠ poison_of_dtyp dt → w.reverse.all is_all_poison_byte = false) :
    Witness dv dt ta acc bs := by
  have ⟨hoff, hbytes⟩ := acc_dvalue_to_memory_bytes_h_spec typed ta acc hw
  rw [written, List.length_append] at hbytes
  exact ⟨w, written, by omega, readback, live⟩

/-- On the all-poison path, a live value would have contributed at least one live byte. -/
private theorem splitReads (l : List memory_byte) (dt : dtyp) (dv : dvalue) (rd : Nat → EOU dvalue)
    (live : dv ≠ poison_of_dtyp dt → l.all is_all_poison_byte = false)
    (readback : ∀ np, (take np l).all is_all_poison_byte = true → rd np = raise_ret dv) :
    (let (np, rest) := poison_split l
     match rest with
     | [] => raise_ret (poison_of_dtyp dt)
     | _ :: _ => rd np) = raise_ret dv := by
  rcases hp : poison_split l with ⟨np, rest⟩
  have hpre := poison_split_prefix l
  rw [hp] at hpre
  cases rest with
  | nil =>
    have hall : l.all is_all_poison_byte = true := by
      rw [← all_poison_bytes_forallb, all_poison_bytes, hp]; rfl
    by_cases h : dv = poison_of_dtyp dt
    · exact congrArg raise_ret h.symm
    · rw [live h] at hall; contradiction
  | cons _ _ => exact readback np hpre

private theorem scalarBlock (b : dvalue_base) (t : dtyp_base) {ta acc off bs}
    (typed : dvalue_has_dtyp (DVALUE_Base b) (DTYPE_Base t))
    (hs : serializable_base t)
    (hw : acc_dvalue_to_memory_bytes_h (DTYPE_Base t) (DVALUE_Base b) 0 ta acc = raise_ret (off, bs)) :
    Witness (DVALUE_Base b) (DTYPE_Base t) ta acc bs := by
  have hc : dvalue_base_has_dtyp_base b t = true ∧ dvalue_base_canonical b = true := by
    cases typed with
    | DVALUE_Base_typ _ _ h c => exact ⟨h,c⟩
    | DVALUE_Poison_typ_agg _ _ => cases t <;> exact ⟨rfl,rfl⟩
  let n := store_size_dtyp (DTYPE_Base t)
  let fwd := (Nseq 0 n).map (base_byte_gen b)
  let pad := List.replicate (tapad ta n - n) poison_memory_byte
  have hlen : fwd.length = n := base_block_length t b
  have hread : memory_bytes_to_dvalue_base fwd t = raise_ret b := read_base_block t b hs hc.1 hc.2
  have h := hw
  rw [ser_base_unfold, acc_base_unfold, rev_loop_acc_app] at h
  simp only [Nat.add_zero, accumulate_padding_shape] at h
  refine finishBlock typed hw (pad ++ fwd.reverse) ?_ ?_ ?_
  · have he := congrArg Prod.snd (Semantics.EOU.EOU.raise_ret.inj h)
    simpa only [pad, fwd, n, List.append_assoc] using he.symm
  · have htake := take_app_exact fwd pad n hlen
    simp only [List.reverse_append, List.reverse_reverse, pad, List.reverse_replicate]
    rw [memory_bytes_to_dvalue]
    change DVALUE_Base <$> memory_bytes_to_dvalue_base (take n (fwd ++ pad)) t = _
    rw [htake, hread]; rfl
  · intro ne
    have hb : b ≠ DVALUE_Poison := fun eq ↦ ne (by rw [eq, poison_of_dtyp_base])
    have live : fwd.all is_all_poison_byte = false := base_block_not_all_poison t hs hc.1 hc.2 hb
    simp only [List.reverse_append, List.reverse_reverse, List.all_append, live, Bool.false_and]

private theorem poisonBlock (dt : dtyp) {ta acc off bs} (notBase : match dt with | .DTYPE_Base _ => False | _ => True)
    (nonempty : dtyp_is_empty dt = false)
    (hw : acc_dvalue_to_memory_bytes_h dt (DVALUE_Base DVALUE_Poison) 0 ta acc = raise_ret (off, bs)) :
    Witness (DVALUE_Base DVALUE_Poison) dt ta acc bs := by
  have h := hw
  rw [ser_poison_agg dt ta acc notBase] at h
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Semantics.EOU.EOU.raise_ret.inj h)
  refine ⟨_, rfl, List.length_replicate, ?_, ?_⟩
  · rw [List.reverse_replicate, read_repeat_poison_agg _ _ notBase, poison_of_dtyp_nonempty _ nonempty]
  · simp [poison_of_dtyp_nonempty _ nonempty]

private theorem structBlock (p : Bool) (ts : List dtyp) (fs : List dvalue) {ta acc off bs}
    (hnp : agg_is_poison (DTYPE_Struct p ts) fs = false) (ht : List.Forall₂ dvalue_has_dtyp fs ts)
    (ih : List.Forall rt_spec fs) (hs : FORALL serializable ts)
    (hw : acc_dvalue_to_memory_bytes_h (DTYPE_Struct p ts) (DVALUE_Struct p fs) 0 ta acc = raise_ret (off,bs)) :
    Witness (DVALUE_Struct p fs) (DTYPE_Struct p ts) ta acc bs := by
  have typed := DVALUE_Struct_typ p hnp ht
  have h := hw
  rw [ser_struct_unfold] at h
  obtain ⟨w, hbytes, _, _, live, rd⟩ := struct_loop_read ht ih hs ta _ 0 acc h
  have hl : DVALUE_Struct p fs ≠ poison_of_dtyp (DTYPE_Struct p ts) → w.reverse.all is_all_poison_byte = false := by
    intro ne; exact live ((struct_canonical_cases typed).resolve_left ne)
  refine finishBlock typed hw w hbytes ?_ hl
  rw [read_struct_unfold]
  apply splitReads _ _ _ (fun np ↦ canonicalize_agg (DTYPE_Struct p ts) <$>
    read_struct_loop memory_bytes_to_dvalue np
      (if p then none else some (max_preferred_dtyp_alignment ts)) 0 ts w.reverse) hl
  intro np hp
  have hh := rd np [] (by simpa using hp)
  simp only [List.append_nil] at hh
  rw [hh]
  change raise_ret (canonicalize_agg _ fs) = _
  simp [canonicalize_agg, hnp]

private theorem arrayBlock (v : Bool) (n : Nat) (t : dtyp) (xs : List dvalue) {ta acc off bs}
    (nv : NO_VOID t) (hnp : agg_is_poison (DTYPE_Array v n t) xs = false)
    (ht : List.Forall (fun x ↦ dvalue_has_dtyp x t) xs) (hlen : xs.length = n)
    (ih : List.Forall rt_spec xs) (hs : serializable t)
    (hw : acc_dvalue_to_memory_bytes_h (DTYPE_Array v n t) (DVALUE_Array v xs) 0 ta acc = raise_ret (off,bs)) :
    Witness (DVALUE_Array v xs) (DTYPE_Array v n t) ta acc bs := by
  have typed := DVALUE_Array_typ v n nv hnp (List.forall_iff_forall_mem.mp ht) hlen
  have canon := array_canonical_cases typed
  have h := hw
  rw [ser_array_unfold] at h
  cases ep : packed_vector_type (DTYPE_Array v n t) with
  | none =>
    rw [ep] at h
    obtain ⟨w, hbytes, _, _, live, rd⟩ := array_loop_read ht ih hs ta _ 0 acc h
    have hl : DVALUE_Array v xs ≠ poison_of_dtyp (DTYPE_Array v n t) → w.reverse.all is_all_poison_byte = false := by
      intro ne; obtain ⟨empty, live'⟩ := canon.resolve_left ne; exact live empty live'
    refine finishBlock typed hw w hbytes ?_ hl
    rw [read_array_unfold]
    simp only [ep]
    apply splitReads _ _ _ (fun np ↦ do
      let es ← read_array_loop memory_bytes_to_dvalue np
        (if v then store_size_dtyp t else alloc_size_dtyp t) t n 0 w.reverse
      pure (canonicalize_agg (DTYPE_Array v n t) es)) hl
    intro np hp
    have hh := rd np [] (by simpa using hp)
    have stride : (if v then store_size_dtyp t else alloc_size_dtyp t) =
        store_size_dtyp t + (if v then 0 else alloc_size_dtyp t - store_size_dtyp t) := by
      cases v <;> simp [Nat.add_sub_of_le (store_le_alloc t)]
    simp only [List.append_nil, hlen, ← stride] at hh
    rw [hh]
    change raise_ret (canonicalize_agg _ xs) = _
    simp [canonicalize_agg, hnp]
  | some tm =>
    rcases tm with ⟨tb,m⟩
    obtain ⟨n', ht', hm, hm8⟩ := packed_vector_type_Some _ ep
    obtain ⟨hv, hlen', ht'⟩ := dtyp.DTYPE_Array.inj ht'
    subst v n' t
    obtain ⟨n', ht', hsize⟩ := store_size_packed_vector _ ep
    have hlen' := (dtyp.DTYPE_Array.inj ht').2.1
    subst n'
    rw [ep] at h
    obtain ⟨bitss, hbits, res⟩ := EOU_bind_ret_inv (map_monad (packed_elt_bits m) xs) _ _ h
    let nb := (n*m.val + 7)/8
    let fwd := packed_fwd nb bitss.flatten
    let pad := List.replicate (tapad ta nb - nb) poison_memory_byte
    obtain ⟨_, _, rd, live⟩ := packed_round_trip n hm hm8 ht hlen hbits
    have hwit := congrArg Prod.snd (Semantics.EOU.EOU.raise_ret.inj res)
    simp only [Nat.zero_add, hsize, acc_packed_bits_fwd, accumulate_padding_shape] at hwit
    have hbytes : bs = (pad ++ fwd.reverse) ++ acc := by
      simpa only [pad, fwd, nb, List.append_assoc] using hwit.symm
    have hrev : (pad ++ fwd.reverse).reverse = fwd ++ pad := by simp [pad]
    have hl : DVALUE_Array true xs ≠ poison_of_dtyp (DTYPE_Array true n (DTYPE_Base tb)) →
        (fwd ++ pad).all is_all_poison_byte = false := by
      intro ne
      have hlive : fwd.all is_all_poison_byte = false := live (canon.resolve_left ne).2
      simp [hlive]
    refine finishBlock typed hw _ hbytes ?_ (by simpa only [hrev] using hl)
    rw [hrev, read_array_unfold]
    simp only [ep]
    apply splitReads _ _ _ (fun _ ↦ pure (canonicalize_agg (DTYPE_Array true n (DTYPE_Base tb))
      (packed_vector_elts tb m n (fwd ++ pad)))) hl
    intro _ _
    change raise_ret (canonicalize_agg _ (packed_vector_elts tb m n (fwd ++ pad))) = _
    rw [rd pad]; simp [canonicalize_agg, hnp]

private theorem roundTripSpec (dv : dvalue) : rt_spec dv := by
  apply dvalue_ind rt_spec ?_ ?_ ?_ dv
  · intro b dt typed hs ta acc off bs hw
    cases dt with
    | DTYPE_Base t => exact scalarBlock b t typed (by simpa only [serializable] using hs) hw
    | DTYPE_Struct _ _ =>
      cases typed with
      | DVALUE_Poison_typ_agg _ ne => exact poisonBlock _ trivial ne hw
    | DTYPE_Array _ _ _ =>
      cases typed with
      | DVALUE_Poison_typ_agg _ ne => exact poisonBlock _ trivial ne hw
  · intro p fs ih dt typed hs ta acc off bs hw
    cases typed with
    | DVALUE_Struct_typ _ hnp ht =>
      exact structBlock _ _ _ hnp ht (List.forall_iff_forall_mem.mpr ih)
        (by simpa only [serializable, FORALL] using hs) hw
  · intro v xs ih dt typed hs ta acc off bs hw
    cases typed with
    | DVALUE_Array_typ _ _ nv hnp ht hlen =>
      exact arrayBlock _ _ _ _ nv hnp (List.forall_iff_forall_mem.mpr ht) hlen
        (List.forall_iff_forall_mem.mpr ih) (by simpa only [serializable] using hs) hw

theorem round_trip_h {dv : dvalue} {dt : dtyp} (typed : dvalue_has_dtyp dv dt)
    (hs : serializable dt) (ta : Option Nat) (acc : List memory_byte) {offset' : Nat} {bs : List memory_byte}
    (written : acc_dvalue_to_memory_bytes_h dt dv 0 ta acc = raise_ret (offset', bs)) :
    ∃ w, bs = w ++ acc ∧ w.length = tapad ta (store_size_dtyp dt) ∧
      memory_bytes_to_dvalue w.reverse dt = raise_ret dv ∧
      (dv ≠ poison_of_dtyp dt → w.reverse.all is_all_poison_byte = false) :=
  roundTripSpec dv dt typed hs ta acc offset' bs written

theorem memory_bytes_round_trip1 {dt : dtyp} {dv : dvalue} (ta : Option Nat) {mb : List memory_byte}
    (hs : serializable dt) (typed : dvalue_has_dtyp dv dt)
    (written : dvalue_to_memory_bytes dt dv ta = raise_ret mb) :
    memory_bytes_to_dvalue mb dt = raise_ret dv := by
  obtain ⟨⟨off, bs⟩, hw, hmb⟩ := EOU_bind_ret_inv (acc_dvalue_to_memory_bytes_h dt dv 0 ta []) _ _ written
  obtain ⟨w, hbs, _, hr, _⟩ := round_trip_h typed hs ta [] hw
  change raise_ret bs.reverse = raise_ret mb at hmb
  rw [← Semantics.EOU.EOU.raise_ret.inj hmb, hbs, List.append_nil]
  exact hr

end Vellvm.Theory.MemoryBytesFacts
