import Vellvm.Theory.MemoryBytesFacts.RoundTrip
import Vellvm.Theory.MemoryBytesFacts.Packed

namespace Vellvm.Theory.MemoryBytesFacts
open Syntax.DynamicTypes Semantics Semantics.DynamicValues Semantics.MemoryBytes Semantics.EOU
open Semantics.Interfaces.Params Semantics.Interfaces.Sizeof Utils.ListUtil

variable [Pa : Params]

theorem valid_pointer_bits_of_run (bits : List memory_bit) (p : Pa.PTR.ptr) (base off : Nat)
    (hr : all_pointer_bits_from p (base + off) bits = true) (hl : bits.length + off = 8) :
    valid_pointer_bits p base off bits = raise_ret (some true) := by
  induction bits generalizing off with
  | nil => simp at hl; subst off; rfl
  | cons b bs ih =>
    cases b with
    | Bit_ptr q j =>
      cases he : Pa.PTR.eq_dec_ptr p q <;>
        simp [all_pointer_bits_from, he, Numeric.Rocqlib.chooseSide] at hr
      rw [valid_pointer_bits, he, if_pos (beq_iff_eq.mpr hr.1)]
      apply ih
      · rw [show base + (1 + off) = 1 + (base + off) by omega]; exact hr.2
      · simp only [List.length_cons] at hl; omega
    | Bit_psn | Bit_bit _ => contradiction

theorem BYTE_Pointer_bits (p : Pa.PTR.ptr) (k : Nat) :
    memory_byte_to_memory_bits (BYTE_Pointer p k) = (Nseq (8 * k) 8).map (Bit_ptr p) := by
  simp [memory_byte_to_memory_bits, dvalue_bv_to_memory_bits, memory_bits_from, rev_loop_acc_app]

theorem pointer_byte_at_run (b : memory_byte) (p : Pa.PTR.ptr) (i : Nat) (hw : memory_byte_wf b)
    (hr : all_pointer_bits_from p (8 * i) (memory_byte_to_memory_bits b) = true) :
    pointer_byte_at p i b = true := by
  cases b with
  | BYTE_Pointer q k =>
    rw [BYTE_Pointer_bits] at hr
    change all_pointer_bits_from p (8 * i) (Bit_ptr q (8 * k) :: _) = true at hr
    rw [all_pointer_bits_from] at hr
    cases he : Pa.PTR.eq_dec_ptr p q <;> simp [he, Numeric.Rocqlib.chooseSide] at hr
    have : k = i := by omega
    subst k
    simp [pointer_byte_at, valid_pointer_byte, he, pure, EOUP_Monad]
  | BYTE_I x => rw [BYTE_I_bits] at hr; contradiction
  | BYTE_Mixed bits =>
    unfold pointer_byte_at
    rw [valid_pointer_byte, valid_pointer_bits_of_run]
    · simpa [Nat.mul_comm, memory_byte_to_memory_bits, dvalue_bv_to_memory_bits] using hr
    · simpa only [Nat.add_zero, memory_byte_wf] using hw

theorem pointer_slice_from_chunk {dbs : List memory_byte} (p : Pa.PTR.ptr) (i : Nat) {n : Nat}
    (hw : List.Forall memory_byte_wf dbs) (hn : 8 * dbs.length ≤ n)
    (hr : all_pointer_bits_from p (8 * i) (get_bits_fwd n dbs) = true) :
    pointer_slice_from p i dbs = true := by
  induction dbs generalizing n i with
  | nil => rfl
  | cons b bs ih =>
    obtain ⟨hb, hbs⟩ := (List.forall_cons _ _ _).mp hw
    simp only [List.length_cons, Nat.mul_succ] at hn
    have h8 : ¬n < 8 := by omega
    rw [get_bits_fwd, if_neg h8, all_pointer_bits_from_app, Bool.and_eq_true] at hr
    rw [pointer_slice_from, pointer_byte_at_run _ _ _ hb hr.1, Bool.true_and]
    apply ih (n := n - 8) (hw := hbs) (hn := by omega)
    have ht := hr.2
    rw [memory_byte_bits_length b hb] at ht
    simpa [Nat.mul_add, Nat.add_comm] using ht

private theorem chunk_run {sz : Positive} {bits : List memory_bit} (hc : is_pointer_chunk sz bits = true) :
    ∃ p j tl, bits = Bit_ptr p j :: tl ∧ sz.val % 8 = 0 ∧ j % sz.val = 0 ∧
      all_pointer_bits_from p j bits = true := by
  cases bits with
  | nil => contradiction
  | cons b tl =>
    cases b with
    | Bit_ptr p j =>
      simp only [is_pointer_chunk, Bool.and_eq_true, beq_iff_eq] at hc
      exact ⟨p, j, tl, rfl, hc.1.1, hc.1.2, hc.2⟩
    | Bit_psn | Bit_bit _ => contradiction

theorem pointer_slice_of_chunk {sz : Positive} {dbs : List memory_byte}
    (hw : List.Forall memory_byte_wf dbs) (hn : 8 * dbs.length ≤ sz.val)
    (hc : is_pointer_chunk sz (get_bits_fwd sz.val dbs) = true) :
    ∃ p k, memory_bytes_to_pointer_slice dbs = some (p, k) ∧ pointer_chunk_aligned sz k = true := by
  obtain ⟨p, j, tl, he, h8, hj, run⟩ := chunk_run hc
  have hj8 := Nat.mod_eq_zero_of_dvd ((Nat.dvd_of_mod_eq_zero h8).trans (Nat.dvd_of_mod_eq_zero hj))
  have hj' : 8 * (j / 8) = j := by omega
  have hsl := pointer_slice_from_chunk p (j / 8) hw hn (by simpa only [hj'] using run)
  have hal : pointer_chunk_aligned sz (j / 8) = true := by
    simp [pointer_chunk_aligned, Nat.mul_comm (j / 8) 8, hj', h8, hj]
  refine ⟨p, j / 8, ?_, hal⟩
  cases dbs with
  | nil =>
    have hz := all_pointer_bits_from_repeat_psn sz.val p j run
    exact False.elim (Nat.ne_of_gt sz.property hz)
  | cons b bs =>
    have hge : ¬sz.val < 8 := by have := sz.property; omega
    rw [get_bits_fwd, if_neg hge] at he
    cases b with
    | BYTE_Pointer q k =>
      rw [BYTE_Pointer_bits] at he
      change Bit_ptr q (8 * k) :: _ = Bit_ptr p j :: tl at he
      injection he with hh ht
      injection hh with hq hk
      subst p; subst j
      have hk : 8 * k / 8 = k := by omega
      rw [hk] at hsl ⊢
      simp [memory_bytes_to_pointer_slice, hsl]
    | BYTE_I x => rw [BYTE_I_bits] at he; contradiction
    | BYTE_Mixed bits =>
      have hb := ((List.forall_cons _ _ _).mp hw).1
      change bits.length = 8 at hb
      cases bits with
      | nil => contradiction
      | cons hd rest =>
        change hd :: _ = Bit_ptr p j :: tl at he
        injection he with hh ht
        subst hd
        simp [memory_bytes_to_pointer_slice, hsl]

theorem mix_not_all_int (l : List memory_bit) (h : (l.any is_ptr_bit || l.any is_poison_bit) = true) :
    l.all is_int_bit = false := by
  induction l with
  | nil => contradiction
  | cons b bs ih => cases b <;> simp_all [is_ptr_bit, is_poison_bit, is_int_bit]

theorem memory_bytes_to_bits_value_canonical (sz : Positive) {dbs : List memory_byte}
    (hw : List.Forall memory_byte_wf dbs) (hl : dbs.length ≤ store_size_dtyp (DTYPE_Base (DTYPE_B sz)))
    (na : ∀ p k, memory_bytes_to_pointer_slice dbs = some (p,k) → pointer_chunk_aligned sz k = false)
    (hnp : dvalue_bv_all_poison (memory_bytes_to_bits_value sz dbs) = false) :
    dvalue_bv_canonical (memory_bytes_to_bits_value sz dbs) = true := by
  have he : (get_bits_of_memory_byte_list sz.val dbs []).reverse = get_bits_fwd sz.val dbs :=
    reader_bits_fwd _ _
  simp only [memory_bytes_to_bits_value, he] at hnp ⊢
  split <;> rename_i hm
  · rw [if_pos hm] at hnp
    have hc : is_pointer_chunk sz (get_bits_fwd sz.val dbs) = false := by
      cases hc : is_pointer_chunk sz (get_bits_fwd sz.val dbs) with
      | false => rfl
      | true =>
        obtain ⟨_, _, _, _, h8, _, _⟩ := chunk_run hc
        have hs := store_size_B_bytes (S := Pa.SIZE) sz h8
        obtain ⟨p, k, hpk, hal⟩ := pointer_slice_of_chunk hw (by omega) hc
        rw [na p k hpk] at hal
        contradiction
    simp [dvalue_bv_canonical, get_bits_fwd_length _ hw, hc, mix_not_all_int _ hm,
      show (get_bits_fwd sz.val dbs).all is_poison_bit = false from hnp]
  · cases memory_bytes_to_int sz dbs <;> try rfl
    rename_i oa; cases oa <;> rfl

theorem memory_bytes_to_byte_value_canonical {sz : Positive} {dbs : List memory_byte} {bv : dvalue_bv sz}
    (hw : List.Forall memory_byte_wf dbs) (hl : dbs.length ≤ store_size_dtyp (DTYPE_Base (DTYPE_B sz)))
    (hr : memory_bytes_to_byte_value sz dbs = raise_ret bv) (hnp : dvalue_bv_all_poison bv = false) :
    dvalue_bv_canonical bv = true := by
  unfold memory_bytes_to_byte_value at hr
  cases hs : memory_bytes_to_pointer_slice dbs with
  | none =>
    rw [hs] at hr; cases hr
    exact memory_bytes_to_bits_value_canonical _ hw hl (by simp [hs]) hnp
  | some pk =>
    rcases pk with ⟨p,k⟩
    rw [hs] at hr
    cases ha : pointer_chunk_aligned sz k <;> simp only [ha, Bool.false_eq_true, if_false, if_true] at hr
    · cases hr
      exact memory_bytes_to_bits_value_canonical _ hw hl (by
        intro q j h; rw [hs] at h; cases h; exact ha) hnp
    · cases hr
      exact (Bool.and_eq_true_iff.mp ha).1

private theorem scalar_pure_typed {A : Type} {t : dtyp_base} (m : EOUP A) (f : A → dvalue_base)
    (typed : ∀ a, dvalue_has_dtyp (DVALUE_Base (f a)) (DTYPE_Base t)) {v : dvalue_base}
    (h : absorb_pois m (fun x ↦ pure (f x)) = raise_ret v) :
    dvalue_has_dtyp (DVALUE_Base v) (DTYPE_Base t) := by
  obtain ⟨opt, _, h⟩ := EOU_bind_ret_inv m _ v h
  cases opt with
  | none => cases h; exact DVALUE_Base_typ _ _ rfl rfl
  | some a => cases h; exact typed a

theorem memory_bytes_to_dvalue_base_has_dtyp (dt : dtyp_base) {dbs : List memory_byte}
    {v : dvalue_base} (hs : serializable_base dt) (hw : List.Forall memory_byte_wf dbs)
    (hl : dbs.length ≤ store_size_dtyp (DTYPE_Base dt)) (hr : memory_bytes_to_dvalue_base dbs dt = raise_ret v) :
    dvalue_has_dtyp (DVALUE_Base v) (DTYPE_Base dt) := by
  cases dt <;> try contradiction
  case DTYPE_FP fp =>
    cases fp <;> try contradiction
    all_goals apply scalar_pure_typed _ _ _ hr; intro a; exact DVALUE_Base_typ _ _ rfl rfl
  case DTYPE_I w =>
    apply scalar_pure_typed _ _ _ hr; intro a
    exact DVALUE_Base_typ _ _ (by simp [dvalue_base_has_dtyp_base]) rfl
  case DTYPE_Pointer =>
    apply scalar_pure_typed _ _ _ hr; intro a; exact DVALUE_Base_typ _ _ rfl rfl
  case DTYPE_B sz =>
    rw [memory_bytes_to_dvalue_base] at hr
    split at hr
    · cases hr; exact DVALUE_Base_typ _ _ rfl rfl
    · obtain ⟨bv, hb, hr⟩ := EOU_bind_ret_inv (memory_bytes_to_byte_value sz dbs) _ v hr
      cases hp : dvalue_bv_all_poison bv <;> simp only [hp, Bool.false_eq_true, if_false, if_true] at hr
      · cases hr
        exact DVALUE_Base_typ _ _ (by simp [dvalue_base_has_dtyp_base])
          (memory_bytes_to_byte_value_canonical hw hl hb hp)
      · cases hr; exact DVALUE_Base_typ _ _ rfl rfl

theorem read_struct_loop_has_dtyp (rd : List memory_byte → dtyp → EOU dvalue) (np : Nat)
    (pad : Option Nat) (dts : List dtyp) (offset : Nat) {dbs : List memory_byte} {vs : List dvalue}
    (hrd : ∀ t ∈ dts, ∀ mb v, List.Forall memory_byte_wf mb → rd mb t = raise_ret v → dvalue_has_dtyp v t)
    (hnv : ∀ t ∈ dts, NO_VOID t) (hw : List.Forall memory_byte_wf dbs)
    (hr : read_struct_loop rd np pad offset dts dbs = raise_ret vs) : List.Forall₂ dvalue_has_dtyp vs dts := by
  induction dts generalizing offset dbs vs with
  | nil => change raise_ret [] = raise_ret vs at hr; cases hr; exact .nil
  | cons t ts ih =>
    rw [read_struct_loop_cons] at hr
    obtain ⟨f, hf, hr⟩ := EOU_bind_ret_inv _ _ _ hr
    obtain ⟨fs, hfs, hr⟩ := EOU_bind_ret_inv _ _ _ hr
    change raise_ret (f :: fs) = raise_ret vs at hr; cases hr
    constructor
    · let padding := if pad.isSome then pad_amount (dtyp_alignment t).preferred_alignment offset else 0
      by_cases hc : offset + padding + store_size_dtyp t ≤ np
      · rw [if_pos hc] at hf; cases hf; exact poison_of_dtyp_has_dtyp _ (hnv t (by simp))
      · rw [if_neg hc] at hf
        exact hrd t (by simp) _ _ (Forall_take_N _ _ _ (Forall_drop_N _ _ _ hw)) hf
    · apply ih (hr := hfs)
      · exact fun t' ht ↦ hrd t' (List.mem_cons_of_mem _ ht)
      · exact fun t' ht ↦ hnv t' (List.mem_cons_of_mem _ ht)
      · exact Forall_drop_N _ _ _ (Forall_drop_N _ _ _ hw)

theorem read_array_loop_has_dtyp (rd : List memory_byte → dtyp → EOU dvalue) (np stride : Nat)
    {t : dtyp} (n offset : Nat) {dbs : List memory_byte} {vs : List dvalue}
    (hrd : ∀ mb v, List.Forall memory_byte_wf mb → rd mb t = raise_ret v → dvalue_has_dtyp v t)
    (hnv : NO_VOID t) (hw : List.Forall memory_byte_wf dbs)
    (hr : read_array_loop rd np stride t n offset dbs = raise_ret vs) :
    List.Forall (fun v ↦ dvalue_has_dtyp v t) vs ∧ vs.length = n := by
  induction n generalizing offset dbs vs with
  | zero => change raise_ret [] = raise_ret vs at hr; cases hr; exact ⟨trivial, rfl⟩
  | succ n ih =>
    rw [read_array_loop_cons] at hr
    obtain ⟨v, hv, hr⟩ := EOU_bind_ret_inv _ _ _ hr
    obtain ⟨tl, ht, hr⟩ := EOU_bind_ret_inv _ _ _ hr
    change raise_ret (v :: tl) = raise_ret vs at hr; cases hr
    obtain ⟨hvs, hlen⟩ := ih _ (hw := Forall_drop_N _ _ _ hw) (hr := ht)
    refine ⟨(List.forall_cons _ _ _).mpr ⟨?_, hvs⟩, by simp [hlen]⟩
    split at hv
    · cases hv; exact poison_of_dtyp_has_dtyp _ hnv
    · exact hrd _ _ (Forall_take_N _ _ _ hw) hv

theorem packed_bits_to_dvalue_has_dtyp {tb : dtyp_base} {m : Positive} (bits : List memory_bit)
    (ht : tb = DTYPE_I m ∨ tb = DTYPE_B m) (hm : m.val % 8 ≠ 0) (hl : bits.length = m.val) :
    dvalue_has_dtyp (packed_bits_to_dvalue tb m bits) (DTYPE_Base tb) := by
  rcases ht with rfl | rfl
  · simp only [packed_bits_to_dvalue]
    split <;> apply DVALUE_Base_typ <;> simp [dvalue_base_has_dtyp_base, dvalue_base_canonical]
  · have hc : is_pointer_chunk m bits = false := by
      cases hc : is_pointer_chunk m bits with
      | false => rfl
      | true => obtain ⟨_, _, _, _, h, _, _⟩ := chunk_run hc; contradiction
    unfold packed_bits_to_dvalue
    cases hp : bits.all is_poison_bit <;> cases hi : bits.all is_int_bit <;>
      simp only [hp, hi, Bool.false_eq_true, if_false, if_true] <;> apply DVALUE_Base_typ <;>
      simp [dvalue_base_has_dtyp_base, dvalue_base_canonical, dvalue_bv_canonical, hl, hc, hi, hp]

theorem packed_bits_to_elts_has_dtyp {tb : dtyp_base} {m : Positive} (n : Nat) (bits : List memory_bit)
    (ht : tb = DTYPE_I m ∨ tb = DTYPE_B m) (hm : m.val % 8 ≠ 0) (hl : n * m.val ≤ bits.length) :
    List.Forall (fun v ↦ dvalue_has_dtyp v (DTYPE_Base tb)) (packed_bits_to_elts tb m n bits) ∧
    (packed_bits_to_elts tb m n bits).length = n := by
  induction n generalizing bits with
  | zero => exact ⟨trivial, rfl⟩
  | succ n ih =>
    rw [Nat.succ_mul] at hl
    have hlen := take_length_exact bits m.val (by omega)
    obtain ⟨hvs, hn⟩ := ih (bits.drop m.val) (by simp only [List.length_drop]; omega)
    rw [packed_bits_to_elts, List.forall_cons, List.length_cons, hn]
    exact ⟨⟨packed_bits_to_dvalue_has_dtyp _ ht hm hlen, hvs⟩, rfl⟩

private theorem typed_struct {p : Bool} {ts : List dtyp} {vs : List dvalue}
    (ht : List.Forall₂ dvalue_has_dtyp vs ts) :
    dvalue_has_dtyp (canonicalize_agg (DTYPE_Struct p ts) vs) (DTYPE_Struct p ts) := by
  unfold canonicalize_agg
  cases hp : agg_is_poison (DTYPE_Struct p ts) vs <;> simp only [hp, Bool.false_eq_true, if_false, if_true]
  · exact DVALUE_Struct_typ p hp ht
  · exact DVALUE_Poison_typ_agg _ (agg_is_poison_nonempty _ _ hp)

private theorem typed_array {v : Bool} {n : Nat} {t : dtyp} {vs : List dvalue}
    (hnv : NO_VOID t) (ht : List.Forall (fun x ↦ dvalue_has_dtyp x t) vs ∧ vs.length = n) :
    dvalue_has_dtyp (canonicalize_agg (DTYPE_Array v n t) vs) (DTYPE_Array v n t) := by
  unfold canonicalize_agg
  cases hp : agg_is_poison (DTYPE_Array v n t) vs <;> simp only [hp, Bool.false_eq_true, if_false, if_true]
  · exact DVALUE_Array_typ v n hnv hp (List.forall_iff_forall_mem.mp ht.1) ht.2
  · exact DVALUE_Poison_typ_agg _ (agg_is_poison_nonempty _ _ hp)

private theorem map_read_inv {A B : Type} (f : A → B) (m : EOU A) {b : B}
    (h : f <$> m = raise_ret b) : ∃ a, m = raise_ret a ∧ f a = b := by
  cases m <;> cases h
  exact ⟨_, rfl, rfl⟩

theorem memory_bytes_to_dvalue_has_dtyp (dt : dtyp) {mb : List memory_byte} {dv : dvalue} :
    serializable dt → List.Forall memory_byte_wf mb → memory_bytes_to_dvalue mb dt = raise_ret dv →
    dvalue_has_dtyp dv dt := by
  induction dt using dtyp_ind generalizing mb dv with
  | base b =>
    intro hs hw hr
    rw [memory_bytes_to_dvalue] at hr
    obtain ⟨v, hv, rfl⟩ := map_read_inv DVALUE_Base _ hr
    exact memory_bytes_to_dvalue_base_has_dtyp _ (by simpa only [serializable] using hs)
      (Forall_take_N _ _ _ hw) (take_length_le _ _) hv
  | struct p ts ih =>
    intro hs hw hr
    rw [read_struct_unfold] at hr
    generalize hp : poison_split mb = pair at hr
    rcases pair with ⟨np, rest⟩
    cases rest with
    | nil => cases hr; exact poison_of_dtyp_has_dtyp _ (serializable_NO_VOID _ hs)
    | cons b rest =>
      obtain ⟨vs, hvs, rfl⟩ := map_read_inv _ _ hr
      apply typed_struct
      rw [serializable] at hs
      have hf := List.forall_iff_forall_mem.mp ((FORALL_forall serializable ts).mp hs)
      exact read_struct_loop_has_dtyp _ _ _ _ _
        (fun t ht mb' v' hw' hr' ↦ ih t ht (hf t ht) hw' hr')
        (fun t ht ↦ serializable_NO_VOID _ (hf t ht)) hw hvs
  | array v n t ih =>
    intro hs hw hr
    rw [read_array_unfold] at hr
    generalize hp : poison_split mb = pair at hr
    rcases pair with ⟨np, rest⟩
    cases rest with
    | nil => cases hr; exact poison_of_dtyp_has_dtyp _ (serializable_NO_VOID _ hs)
    | cons b rest =>
      have hs' : serializable t := by simpa only [serializable] using hs
      cases ep : packed_vector_type (DTYPE_Array v n t) with
      | none =>
        simp only [ep] at hr
        obtain ⟨vs, hvs, hr⟩ := EOU_bind_ret_inv _ _ _ hr
        cases hr
        exact typed_array (serializable_NO_VOID _ hs') (read_array_loop_has_dtyp _ _ _ _ _
          (fun _ _ ↦ ih hs') (serializable_NO_VOID _ hs') hw hvs)
      | some pair =>
        rcases pair with ⟨tb, m⟩
        obtain ⟨n', eq, ht, hm⟩ := packed_vector_type_Some _ ep
        injection eq with hv hn ht'
        subst v; subst n'; subst t
        simp only [ep] at hr; cases hr
        apply typed_array (serializable_NO_VOID _ hs')
        unfold packed_vector_elts
        rw [show (get_bits_of_memory_byte_list (n * m.val) mb []).reverse = _ from
          reader_bits_fwd (n * m.val) mb]
        apply packed_bits_to_elts_has_dtyp _ _ ht hm
        rw [get_bits_fwd_length _ hw]

theorem memory_bytes_to_dvalue_idempotent (dt : dtyp) {dv : dvalue} {mb1 mb2 : List memory_byte}
    (hs : serializable dt) (hw : List.Forall memory_byte_wf mb1) (hr : memory_bytes_to_dvalue mb1 dt = raise_ret dv)
    (hs₂ : dvalue_to_memory_bytes dt dv none = raise_ret mb2) : memory_bytes_to_dvalue mb2 dt = raise_ret dv :=
  memory_bytes_round_trip1 none hs (memory_bytes_to_dvalue_has_dtyp dt hs hw hr) hs₂

theorem memory_byte_of_dvalue_bv_wf {sz : Positive} (bv : dvalue_bv sz) (idx : Nat) :
    memory_byte_wf (memory_byte_of_dvalue_bv bv idx) := by
  cases bv with
  | BYTE_Pointer | BYTE_I => trivial
  | BYTE_Mixed bits =>
    simp only [memory_byte_of_dvalue_bv, memory_byte_wf, List.length_append]
    split <;> simp_all [List.length_take] <;> omega

theorem poison_memory_byte_wf : memory_byte_wf (poison_memory_byte (Pa := Pa)) := rfl

theorem Forall_wf_poison_app (k : Nat) {acc : List memory_byte} (hw : List.Forall memory_byte_wf acc) :
    List.Forall memory_byte_wf (List.replicate k poison_memory_byte ++ acc) := by
  induction k with
  | zero => exact hw
  | succ k ih =>
    rw [List.replicate_succ, List.cons_append, List.forall_cons]
    exact ⟨poison_memory_byte_wf, ih⟩

theorem accumulate_padding_wf (o : Nat) (q : Option Nat) {acc : List memory_byte}
    (hw : List.Forall memory_byte_wf acc) : List.Forall memory_byte_wf (accumulate_padding o q acc).2 := by
  rw [accumulate_padding_shape]; exact Forall_wf_poison_app _ hw

theorem accumulate_padding_bytes_wf (o n : Nat) {acc : List memory_byte} (hw : List.Forall memory_byte_wf acc) :
    List.Forall memory_byte_wf (accumulate_padding_bytes o n acc).2 := by
  rw [accumulate_padding_bytes_shape]; exact Forall_wf_poison_app _ hw

theorem acc_memory_bytes_of_dvalue_base_wf (dtb : dtyp_base) (dv : dvalue_base) (offset : Nat)
    {acc : List memory_byte} (hw : List.Forall memory_byte_wf acc) :
    List.Forall memory_byte_wf (acc_memory_bytes_of_dvalue_base dtb dv offset acc).2 := by
  simp only [acc_memory_bytes_of_dvalue_base, rev_loop_acc_app, List.forall_iff_forall_mem,
    List.mem_append, List.mem_reverse, List.mem_map] at ⊢
  intro b hb
  rcases hb with ⟨i, _, rfl⟩ | hb
  · cases dv <;> first | apply memory_byte_of_dvalue_bv_wf | apply poison_memory_byte_wf | trivial
  · exact List.forall_iff_forall_mem.mp hw b hb

theorem struct_bytes_loop_wf
    (ser : dtyp → dvalue → Nat → Option Nat → List memory_byte → EOU (Nat × List memory_byte))
    (ta pad : Option Nat) (fields : List dvalue) (types : List dtyp) (offset : Nat) {acc : List memory_byte}
    {r : Nat × List memory_byte} (hs : ∀ f ∈ fields, ∀ dt o ta' acc' r', List.Forall memory_byte_wf acc' →
      ser dt f o ta' acc' = raise_ret r' → List.Forall memory_byte_wf r'.2)
    (hw : List.Forall memory_byte_wf acc) (hr : struct_bytes_loop ser ta pad fields types offset acc = raise_ret r) :
    List.Forall memory_byte_wf r.2 := by
  induction fields generalizing types offset acc with
  | nil =>
    cases types with
    | nil =>
      rw [struct_bytes_loop_nil] at hr
      cases hr
      exact accumulate_padding_wf _ _ (accumulate_padding_wf _ _ hw)
    | cons t ts => contradiction
  | cons f fs ih =>
    cases types with
    | nil => contradiction
    | cons t ts =>
      rw [struct_bytes_loop_cons] at hr
      obtain ⟨⟨coff, bs⟩, hser, htl⟩ := EOU_bind_ret_inv _ _ _ hr
      have hf := hs f (by simp) t 0 none _ (coff, bs) (accumulate_padding_wf _ _ hw) hser
      exact ih _ _ (hs := fun f' hf' ↦ hs f' (List.mem_cons_of_mem _ hf'))
        (hw := accumulate_padding_bytes_wf
          ((accumulate_padding offset (pad.map fun _ ↦ (dtyp_alignment t).preferred_alignment) acc).1 + coff)
          (alloc_size_dtyp t - store_size_dtyp t) hf) (hr := htl)

theorem array_bytes_loop_wf
    (ser : dtyp → dvalue → Nat → Option Nat → List memory_byte → EOU (Nat × List memory_byte))
    (ta : Option Nat) (dt : dtyp) (elt_pad : Nat) (elts : List dvalue) (offset : Nat) {acc : List memory_byte}
    {r : Nat × List memory_byte} (hs : ∀ e ∈ elts, ∀ o ta' acc' r', List.Forall memory_byte_wf acc' →
      ser dt e o ta' acc' = raise_ret r' → List.Forall memory_byte_wf r'.2)
    (hw : List.Forall memory_byte_wf acc) (hr : array_bytes_loop ser ta dt elt_pad elts offset acc = raise_ret r) :
    List.Forall memory_byte_wf r.2 := by
  induction elts generalizing offset acc with
  | nil => rw [array_bytes_loop_nil] at hr; cases hr; exact accumulate_padding_wf _ _ hw
  | cons e es ih =>
    rw [array_bytes_loop_cons] at hr
    obtain ⟨⟨coff, bs⟩, hser, htl⟩ := EOU_bind_ret_inv _ _ _ hr
    have he := hs e (by simp) 0 none _ (coff, bs) hw hser
    exact ih _ (hs := fun e' he' ↦ hs e' (List.mem_cons_of_mem _ he'))
      (hw := accumulate_padding_bytes_wf (offset + coff) elt_pad he) (hr := htl)

theorem packed_fwd_wf (nb : Nat) (bits : List memory_bit) : List.Forall memory_byte_wf (packed_fwd nb bits) := by
  apply bytes_of_bits_wf
  simp only [List.length_append, List.length_replicate]; omega

theorem packed_vector_bytes_wf (m : Positive) (dt : dtyp) (elts : List dvalue) (offset : Nat)
    (ta : Option Nat) {acc : List memory_byte} {r : Nat × List memory_byte} (hw : List.Forall memory_byte_wf acc)
    (hr : packed_vector_bytes m dt elts offset ta acc = raise_ret r) : List.Forall memory_byte_wf r.2 := by
  obtain ⟨bits, _, hr⟩ := EOU_bind_ret_inv (map_monad (packed_elt_bits m) elts) _ r hr
  cases hr
  apply accumulate_padding_wf
  rw [acc_packed_bits_fwd, List.forall_iff_forall_mem]
  intro b hb
  rcases List.mem_append.mp hb with h | h
  · exact List.forall_iff_forall_mem.mp (packed_fwd_wf _ _) b (List.mem_reverse.mp h)
  · exact List.forall_iff_forall_mem.mp hw b h

theorem acc_dvalue_to_memory_bytes_h_wf (dv : dvalue) (dt : dtyp) (offset : Nat) (ta : Option Nat)
    {acc : List memory_byte} {r : Nat × List memory_byte} : List.Forall memory_byte_wf acc →
    acc_dvalue_to_memory_bytes_h dt dv offset ta acc = raise_ret r → List.Forall memory_byte_wf r.2 := by
  induction dv using dvalue_ind generalizing dt offset ta acc r with
  | base db =>
    intro hw hr
    cases dt with
    | DTYPE_Base b =>
      rw [ser_base_unfold] at hr; cases hr
      exact accumulate_padding_wf _ _ (acc_memory_bytes_of_dvalue_base_wf b db offset hw)
    | DTYPE_Struct p ts =>
      cases db <;> first | rw [ser_struct_poison_unfold] at hr | simp [acc_dvalue_to_memory_bytes_h] at hr
      cases hr; exact accumulate_padding_wf _ _ (accumulate_padding_bytes_wf offset _ hw)
    | DTYPE_Array v n t =>
      cases db <;> first | rw [ser_array_poison_unfold] at hr | simp [acc_dvalue_to_memory_bytes_h] at hr
      cases hr; exact accumulate_padding_wf _ _ (accumulate_padding_bytes_wf offset _ hw)
  | struct p fields ih =>
    intro hw hr
    cases dt with
    | DTYPE_Struct pk ts =>
      rw [ser_struct_unfold] at hr
      exact struct_bytes_loop_wf _ _ _ _ _ _ (fun f hf dt o ta _ _ ↦ ih f hf dt o ta) hw hr
    | _ => simp [acc_dvalue_to_memory_bytes_h] at hr
  | array p es ih =>
    intro hw hr
    cases dt with
    | DTYPE_Array v n t =>
      rw [ser_array_unfold] at hr
      cases hp : packed_vector_type (DTYPE_Array v n t) with
      | none =>
        rw [hp] at hr
        exact array_bytes_loop_wf _ _ _ _ _ _ (fun e he o ta _ _ ↦ ih e he _ o ta) hw hr
      | some pair =>
        rcases pair with ⟨tb,m⟩; rw [hp] at hr
        exact packed_vector_bytes_wf _ _ _ _ _ hw hr
    | _ => simp [acc_dvalue_to_memory_bytes_h] at hr

theorem dvalue_to_memory_bytes_wf (dt : dtyp) (dv : dvalue) (ta : Option Nat) {mb : List memory_byte}
    (hw : dvalue_to_memory_bytes dt dv ta = raise_ret mb) : List.Forall memory_byte_wf mb := by
  obtain ⟨⟨o, bs⟩, hs, hr⟩ := EOU_bind_ret_inv (acc_dvalue_to_memory_bytes_h dt dv 0 ta []) _ mb hw
  cases hr
  have hbs := acc_dvalue_to_memory_bytes_h_wf dv dt 0 ta (acc := []) (r := (o, bs)) trivial hs
  apply List.forall_iff_forall_mem.mpr
  intro b hb
  exact List.forall_iff_forall_mem.mp hbs b (List.mem_reverse.mp hb)

theorem memory_bytes_to_dvalue_idempotent_written (dt : dtyp) (dv0 : dvalue) (ta : Option Nat)
    {dv : dvalue} {mb1 mb2 : List memory_byte} (hs : serializable dt)
    (hw₁ : dvalue_to_memory_bytes dt dv0 ta = raise_ret mb1) (hr : memory_bytes_to_dvalue mb1 dt = raise_ret dv)
    (hw₂ : dvalue_to_memory_bytes dt dv none = raise_ret mb2) : memory_bytes_to_dvalue mb2 dt = raise_ret dv :=
  memory_bytes_to_dvalue_idempotent dt hs (dvalue_to_memory_bytes_wf dt dv0 ta hw₁) hr hw₂

end Vellvm.Theory.MemoryBytesFacts
