import Vellvm.Theory.MemoryBytesFacts.Reader
import Vellvm.Utils.ZUtil
import Mathlib.Data.List.GetD

namespace Vellvm.Theory.MemoryBytesFacts
open Vellvm Vellvm.Syntax.DynamicTypes Vellvm.Utils.ListUtil Vellvm.Utils.ZUtil
open Vellvm.Semantics Vellvm.Semantics.Interfaces.Params Vellvm.Semantics.Interfaces.Sizeof
open Vellvm.Semantics.DynamicValues Vellvm.Semantics.MemoryBytes Vellvm.Semantics.EOU
open Vellvm.Semantics.VellvmIntegers
open Vellvm.Numeric.Integers (bit_int)

variable [Pa : Params]

def byte_layout : dtyp → Prop
  | .DTYPE_Base (.DTYPE_B n) => n.val % 8 = 0
  | .DTYPE_Base _ | .DTYPE_Struct false _ => False
  | .DTYPE_Array true _ t => byte_layout t
  | .DTYPE_Array false _ t => byte_layout t ∧ alloc_size_dtyp t = store_size_dtyp t
  | .DTYPE_Struct true ts =>
    ts.foldr (fun t r ↦ (byte_layout t ∧ alloc_size_dtyp t = store_size_dtyp t) ∧ r) True

theorem byte_layout_not_packed : ∀ (vv : Bool) (sz : Nat) (t : dtyp), byte_layout t →
    packed_vector_type (DTYPE_Array vv sz t) = none := by
  intro v n t ht
  cases v with
  | false => rfl
  | true =>
    cases t with
    | DTYPE_Base b => cases b <;> simp_all [byte_layout, packed_vector_type]
    | DTYPE_Struct _ _ => rfl
    | DTYPE_Array _ _ _ => rfl

def same_bits (a b : memory_byte) : Prop := memory_byte_to_memory_bits a = memory_byte_to_memory_bits b

theorem forallb_psn_repeat : ∀ (l : List memory_bit), l.all is_poison_bit = true →
    l = List.replicate l.length Bit_psn := by
  intro l
  induction l with
  | nil => intro _; rfl
  | cons b bs ih =>
    intro h
    obtain ⟨hb, ht⟩ := Bool.and_eq_true_iff.mp h
    cases b <;> try contradiction
    rw [List.length_cons, List.replicate_succ, ← ih ht]

theorem same_bits_poison : ∀ (b : memory_byte), memory_byte_wf b → is_all_poison_byte b = true →
    same_bits b poison_memory_byte := by
  intro b hw h
  cases b with
  | BYTE_Pointer _ _ | BYTE_I _ => contradiction
  | BYTE_Mixed bits =>
    change bits.length = 8 at hw
    change bits.all is_poison_bit = true at h
    change bits = List.replicate 8 Bit_psn
    simpa only [hw] using forallb_psn_repeat bits h

theorem same_bits_all_poison : ∀ {dbs : List memory_byte}, List.Forall memory_byte_wf dbs →
    dbs.all is_all_poison_byte = true →
    List.Forall₂ same_bits dbs (List.replicate dbs.length poison_memory_byte) := by
  intro dbs
  induction dbs with
  | nil => intro _ _; exact .nil
  | cons b bs ih =>
    intro hw h
    obtain ⟨hb, ht⟩ := (List.forall_cons _ _ _).mp hw
    obtain ⟨hp, hs⟩ := Bool.and_eq_true_iff.mp h
    rw [List.length_cons, List.replicate_succ]
    exact .cons (same_bits_poison b hb hp) (ih ht hs)

theorem write_base_block : ∀ {dtb : dtyp_base} {v : dvalue_base} {acc : List memory_byte} {o bs},
    acc_dvalue_to_memory_bytes_h (DTYPE_Base dtb) (DVALUE_Base v) 0 none acc = raise_ret (o, bs) →
    bs = ((Nseq 0 (store_size_dtyp (DTYPE_Base dtb))).map (base_byte_gen v)).reverse ++ acc := by
  intro dtb v acc o bs h
  rw [ser_base_unfold, acc_base_unfold] at h
  change raise_ret (_, N.rev_loop_acc (base_byte_gen v) _ 0 acc) = raise_ret (o, bs) at h
  exact (congrArg Prod.snd (EOU.raise_ret.inj h)).symm.trans (rev_loop_acc_app _ _ _ _)

theorem write_poison_layout : ∀ (dt : dtyp) (acc : List memory_byte) {o bs}, byte_layout dt →
    acc_dvalue_to_memory_bytes_h dt (DVALUE_Base DVALUE_Poison) 0 none acc = raise_ret (o, bs) →
    bs = List.replicate (store_size_dtyp dt) poison_memory_byte ++ acc := by
  intro dt acc o bs _ h
  cases dt with
  | DTYPE_Base b =>
    have hb := write_base_block h
    change bs = ((Nseq 0 _).map (fun _ ↦ poison_memory_byte)).reverse ++ acc at hb
    simpa only [map_const_Nseq, List.reverse_replicate] using hb
  | DTYPE_Struct _ _ | DTYPE_Array _ _ _ =>
    rw [@ser_poison_agg Pa _ none acc trivial] at h
    exact (congrArg Prod.snd (EOU.raise_ret.inj h)).symm

theorem all_pointer_bits_from_map : ∀ (p : Pa.PTR.ptr) (l : List memory_bit) (s : Nat),
    all_pointer_bits_from p s l = true → l = (Nseq s l.length).map (Bit_ptr p) := by
  intro p l
  induction l with
  | nil => intro _ _; rfl
  | cons b bs ih =>
    intro s h
    cases b with
    | Bit_psn | Bit_bit _ => contradiction
    | Bit_ptr q i =>
      cases e : Pa.PTR.eq_dec_ptr p q with
      | inr hne => simp [all_pointer_bits_from, Numeric.Rocqlib.chooseSide, e, hne] at h
      | inl he =>
        subst q
        simp [all_pointer_bits_from, Numeric.Rocqlib.chooseSide, e] at h
        obtain ⟨rfl, hr⟩ := h
        simp only [List.length_cons, Nseq, List.map_cons, List.cons.injEq, true_and]
        simpa only [Nat.add_comm 1] using ih _ hr

theorem same_bits_pointer_byte : ∀ (b : memory_byte) (p : Pa.PTR.ptr) (j : Nat),
    memory_byte_wf b → pointer_byte_at p j b = true → same_bits b (BYTE_Pointer p j) := by
  intro b p j hw h
  cases b with
  | BYTE_I _ => contradiction
  | BYTE_Pointer q i =>
    cases e : Pa.PTR.eq_dec_ptr p q with
    | inr _ => simp [pointer_byte_at, valid_pointer_byte, e, pure, EOUP_Monad] at h
    | inl hp =>
      subst q
      change (match valid_pointer_byte p j (BYTE_Pointer p i) with
        | .raise_ret (some r) => r | _ => false) = true at h
      simp [valid_pointer_byte, e, pure, EOUP_Monad] at h
      subst i; rfl
  | BYTE_Mixed bits =>
    have hv : valid_pointer_bits p (j*8) 0 bits = raise_ret (some true) := by
      unfold pointer_byte_at at h
      change (match valid_pointer_bits p (j*8) 0 bits with
        | .raise_ret (some r) => r | _ => false) = true at h
      split at h <;> simp_all <;> rfl
    have hp := @valid_pointer_bits_implies Pa bits p (j*8) 0 hv
    have hm := all_pointer_bits_from_map _ _ _ hp
    change bits.length = 8 at hw
    unfold same_bits
    rw [BYTE_Pointer_bits]
    simpa only [memory_byte_to_memory_bits, dvalue_bv_to_memory_bits, hw, Nat.add_zero,
      Nat.mul_comm j] using hm

theorem pointer_slice_from_same_bits : ∀ (p : Pa.PTR.ptr) {dbs : List memory_byte} (k : Nat),
    List.Forall memory_byte_wf dbs → pointer_slice_from p k dbs = true →
    List.Forall₂ same_bits dbs ((Nseq k dbs.length).map (BYTE_Pointer p)) := by
  intro p dbs
  induction dbs with
  | nil => intro _ _ _; exact .nil
  | cons b bs ih =>
    intro k hw h
    obtain ⟨hb, ht⟩ := (List.forall_cons _ _ _).mp hw
    obtain ⟨hp, hs⟩ := Bool.and_eq_true_iff.mp h
    apply List.Forall₂.cons (same_bits_pointer_byte b p k hb hp)
    simpa only [Nat.add_comm 1] using ih _ ht hs

theorem pointer_slice_some : ∀ (dbs : List memory_byte) {p k}, memory_bytes_to_pointer_slice dbs = some (p,k) →
    pointer_slice_from p k dbs = true := by
  intro dbs p k h
  unfold memory_bytes_to_pointer_slice at h
  split at h <;> try contradiction
  all_goals try dsimp only at h
  all_goals split at h <;> simp_all

theorem take_drop_concat_bytes : ∀ {dbs : List memory_byte} {i : Nat}, List.Forall memory_byte_wf dbs →
    i < dbs.length → take 8 (drop (8*i) (dbs.map memory_byte_to_memory_bits).flatten) =
      memory_byte_to_memory_bits (dbs.getD i poison_memory_byte) := by
  intro dbs
  induction dbs with
  | nil => intro i _ hi; simp at hi
  | cons b bs ih =>
    intro i hw hi
    obtain ⟨hb, hbs⟩ := (List.forall_cons _ _ _).mp hw
    have hl := @memory_byte_bits_length Pa b hb
    simp only [List.map_cons, List.flatten_cons]
    cases i with
    | zero => simpa only [Nat.mul_zero, drop, List.drop_zero, List.getD_cons_zero] using
        take_app_exact _ _ 8 hl
    | succ i =>
      rw [show 8 * (i+1) = 8 + 8*i by omega, ← drop_drop, drop_app_exact _ _ 8 hl]
      exact @ih i hbs (Nat.lt_of_succ_lt_succ hi)

theorem mixed_bytes_same_bits : ∀ {dbs : List memory_byte}, List.Forall memory_byte_wf dbs →
    List.Forall₂ same_bits dbs ((Nseq 0 dbs.length).map
      (mixed_byte (dbs.map memory_byte_to_memory_bits).flatten)) := by
  intro dbs hw
  apply Forall2_nth_Nseq _ _ poison_memory_byte
  intro i hi
  have hm : dbs.getD i poison_memory_byte ∈ dbs := by
    rw [List.getD_eq_getElem _ _ hi]; exact List.getElem_mem hi
  have hb := @memory_byte_bits_length Pa _ ((List.forall_iff_forall_mem.mp hw) _ hm)
  unfold same_bits
  rw [Nat.zero_add, memory_byte_to_memory_bits_mixed]
  let m := take 8 (drop (8*i) (dbs.map memory_byte_to_memory_bits).flatten)
  change _ = m ++ (if !(m.length == 8) then List.replicate (8-m.length) Bit_psn else [])
  have hm' : m = _ := take_drop_concat_bytes hw hi
  rw [hm', hb]; simp

theorem no_ptr_psn_bits : ∀ (l : List memory_bit), l.any is_ptr_bit = false → l.any is_poison_bit = false →
    ∃ bis : List int1, l = bis.map Bit_bit := by
  intro l
  induction l with
  | nil => intro _ _; exact ⟨[], rfl⟩
  | cons b bs ih =>
    intro hp hs
    cases b with
    | Bit_ptr _ _ => simp [is_ptr_bit] at hp
    | Bit_psn => simp [is_poison_bit] at hs
    | Bit_bit x =>
      obtain ⟨ys, hy⟩ := ih (by simpa [is_ptr_bit] using hp) (by simpa [is_poison_bit] using hs)
      exact ⟨x :: ys, congrArg (Bit_bit x :: ·) hy⟩

theorem same_bits_int_byte : ∀ (b : memory_byte) {z : Int}, memory_byte_wf b →
    (memory_byte_to_memory_bits b).any is_ptr_bit = false →
    (memory_byte_to_memory_bits b).any is_poison_bit = false →
    memory_byte_to_Z b = raise_ret (NoPois z) → same_bits b (BYTE_I (Numeric.Integers.repr z)) := by
  intro b z hw hp hs hz
  cases b with
  | BYTE_Pointer p i => rw [BYTE_Pointer_bits] at hp; contradiction
  | BYTE_I y =>
    change raise_ret (some (Numeric.Integers.unsigned y)) = raise_ret (some z) at hz
    cases hz
    change same_bits (BYTE_I y) (BYTE_I (Numeric.Integers.repr (Numeric.Integers.unsigned y)))
    rw [Numeric.Integers.repr_unsigned] <;> rfl
  | BYTE_Mixed bits =>
    obtain ⟨xs, rfl⟩ := no_ptr_psn_bits bits hp hs
    change (xs.map (@Bit_bit Pa)).length = 8 at hw
    change memory_bits_to_Z (xs.map Bit_bit) = raise_ret (some z) at hz
    rw [memory_bits_to_Z_ints] at hz
    cases hz
    have h := @memory_byte_of_bits_int Pa xs (by simpa using hw)
    rw [memory_byte_of_bits, forallb_int_map, if_pos rfl, int_bits_to_Z_map] at h
    exact h.symm

def byte_val (b : memory_byte) : Int :=
  match memory_byte_to_Z b with
  | .raise_ret (some z) => z
  | _ => 0

theorem memory_byte_to_Z_no_psn : ∀ (b : memory_byte), (memory_byte_to_memory_bits b).any is_poison_bit = false →
    memory_byte_to_Z b = raise_ret (NoPois (byte_val b)) := by
  intro b h
  cases b with
  | BYTE_Pointer _ _ | BYTE_I _ => rfl
  | BYTE_Mixed bits =>
    change bits.any is_poison_bit = false at h
    have aux : ∃ zs, map_monad (m := EOUP) memory_bit_to_bit bits = raise_ret (some zs) := by
      induction bits with
      | nil => exact ⟨[], rfl⟩
      | cons b bs ih =>
        obtain ⟨hb, ht⟩ := Bool.or_eq_false_iff.mp h
        obtain ⟨zs, hz⟩ := ih ht
        rw [map_monad_cons_EOUP, hz]
        cases b <;> first | contradiction | exact ⟨_, rfl⟩
    obtain ⟨zs, hz⟩ := aux
    simp only [byte_val, memory_byte_to_Z, memory_bits_to_Z, hz] <;> rfl

theorem byte_val_range : ∀ (b : memory_byte), memory_byte_wf b →
    (memory_byte_to_memory_bits b).any is_ptr_bit = false →
    (memory_byte_to_memory_bits b).any is_poison_bit = false →
    0 ≤ byte_val b ∧ byte_val b < 256 := by
  intro b hw hp hs
  cases b with
  | BYTE_Pointer p i => rw [BYTE_Pointer_bits] at hp; contradiction
  | BYTE_I x => exact Numeric.Integers.unsigned_range x
  | BYTE_Mixed bits =>
    obtain ⟨xs, rfl⟩ := no_ptr_psn_bits bits hp hs
    change (xs.map (@Bit_bit Pa)).length = 8 at hw
    have hl : xs.length = 8 := by simpa using hw
    have hr := concat_bits_Z_range xs
    rw [hl, show (2 : Int) ^ (8 : Nat) = 256 by decide] at hr
    simpa only [byte_val, memory_byte_to_Z, memory_bits_to_Z_ints] using hr

theorem map_monad_byte_to_Z_no_psn : ∀ (dbs : List memory_byte),
    (∀ b ∈ dbs, (memory_byte_to_memory_bits b).any is_poison_bit = false) →
    map_monad (m := EOUP) memory_byte_to_Z dbs = raise_ret (NoPois (dbs.map byte_val)) := by
  intro dbs
  induction dbs with
  | nil => intro _; rfl
  | cons b bs ih =>
    intro h
    rw [map_monad_cons_EOUP, memory_byte_to_Z_no_psn b (h _ (.head _)),
      ih (fun a ha ↦ h a (.tail _ ha))]; rfl

omit Pa in
theorem extract_byte_vint_concat : ∀ {sz : Positive} {zs : List Int} {i : Nat},
    8 * (zs.length : Int) = (sz.val : Int) → List.Forall (fun z ↦ 0 ≤ z ∧ z < 256) zs →
    i < zs.length → extract_byte_vint (Numeric.Integers.repr (concat_bytes_Z zs) : bit_int sz) i = zs.getD i 0 := by
  intro sz zs i hl hf hi
  have hr := concat_digits_range 8 zs (by decide) hf
  change 8 * Int.ofNat zs.length = Int.ofNat sz.val at hl
  rw [← concat_bytes_Z_digits, hl] at hr
  have hm : @Numeric.Integers.modulus sz = (2 : Int)^sz.val := by
    simpa only [Int.natCast_pow, Int.cast_ofNat_Int] using
      (show @Numeric.Integers.modulus sz = ((2 ^ sz.val : Nat) : Int) from Numeric.Integers.modulus_def)
  have hrhi : concat_bytes_Z zs < (2 : Int)^sz.val := hr.2
  have hu : Numeric.Integers.unsigned (Numeric.Integers.repr (w := sz) (concat_bytes_Z zs)) =
      concat_bytes_Z zs := Numeric.Integers.unsigned_repr _ ⟨hr.1, by
        unfold Numeric.Integers.max_unsigned; rw [hm]; omega⟩
  have hindex : 8 * ((i : Int) + 1) ≤ (sz.val : Int) := by
    change 8 * (zs.length : Int) = (sz.val : Int) at hl; omega
  rw [extract_byte_vint_spec (Numeric.Integers.repr (w := sz) (concat_bytes_Z zs)) i hindex]
  change Numeric.Integers.unsigned (Numeric.Integers.repr (w := sz) _) / _ % _ = _
  rw [hu, concat_bytes_Z_digits]
  exact concat_digits_nth 8 zs i (by decide) hf hi

theorem int_bytes_same_bits : ∀ {sz : Positive} {dbs : List memory_byte},
    List.Forall memory_byte_wf dbs → 8 * dbs.length = sz.val →
    (dbs.map memory_byte_to_memory_bits).flatten.any is_ptr_bit = false →
    (dbs.map memory_byte_to_memory_bits).flatten.any is_poison_bit = false →
    List.Forall₂ same_bits dbs ((Nseq 0 dbs.length).map
      (memory_byte_of_dvalue_bv (BYTE_I (Numeric.Integers.repr (concat_bytes_Z (dbs.map byte_val)) : bit_int sz)))) := by
  intro sz dbs hw hl hp hs
  have localFacts (b : memory_byte) (hb : b ∈ dbs) :=
    And.intro (List.forall_iff_forall_mem.mp hw b hb)
      (And.intro (existsb_concat_map _ _ _ _ hp hb) (existsb_concat_map _ _ _ _ hs hb))
  have hr : List.Forall (fun z ↦ 0 ≤ z ∧ z < 256) (dbs.map byte_val) := by
    apply List.forall_iff_forall_mem.mpr
    intro z hz
    obtain ⟨b, hb, rfl⟩ := List.mem_map.mp hz
    obtain ⟨h₁, h₂, h₃⟩ := localFacts b hb
    exact byte_val_range b h₁ h₂ h₃
  apply Forall2_nth_Nseq _ _ poison_memory_byte
  intro i hi
  have hi' : i < (dbs.map byte_val).length := by simpa using hi
  have hm : dbs[i] ∈ dbs := List.getElem_mem hi
  obtain ⟨h₁, h₂, h₃⟩ := localFacts _ hm
  simp only [Nat.zero_add, memory_byte_of_dvalue_bv, extract_byte_vint_concat
    (by simpa only [List.length_map] using (show 8 * (dbs.length : Int) = (sz.val : Int) by omega)) hr hi',
    List.getD_eq_getElem _ _ hi, List.getD_eq_getElem _ _ hi', List.getElem_map]
  exact same_bits_int_byte _ h₁ h₂ h₃ (memory_byte_to_Z_no_psn _ h₃)

theorem bits_value_same_bits : ∀ {sz : Positive} {dbs : List memory_byte},
    List.Forall memory_byte_wf dbs → 8 * dbs.length = sz.val →
    List.Forall₂ same_bits dbs ((Nseq 0 dbs.length).map
      (memory_byte_of_dvalue_bv (memory_bytes_to_bits_value sz dbs))) := by
  intro sz dbs hw hl
  have h8 : sz.val % 8 = 0 := by omega
  have hd := (reader_bits_fwd sz.val dbs).trans (@get_bits_fwd_concat Pa dbs sz.val hw hl)
  change (get_bits_of_memory_byte_list sz.val dbs []).reverse = _ at hd
  simp only [memory_bytes_to_bits_value, hd]
  split
  · exact mixed_bytes_same_bits hw
  · rename_i h
    have hn : ((dbs.map memory_byte_to_memory_bits).flatten.any is_ptr_bit ||
        (dbs.map memory_byte_to_memory_bits).flatten.any is_poison_bit) = false :=
      Bool.eq_false_iff.mpr h
    obtain ⟨hp, hs⟩ := Bool.or_eq_false_iff.mp hn
    have hint : memory_bytes_to_int sz dbs = raise_ret (some (concat_bytes_Z (dbs.map byte_val))) := by
      simp only [memory_bytes_to_int, h8, bne_self_eq_false, Bool.false_eq_true, if_false]
      rw [map_monad_byte_to_Z_no_psn dbs (fun b hb ↦ existsb_concat_map _ _ _ _ hs hb)]
      rfl
    rw [hint]
    exact int_bytes_same_bits hw hl hp hs

theorem bits_value_all_poison : ∀ {sz : Positive} {dbs : List memory_byte},
    List.Forall memory_byte_wf dbs → 8 * dbs.length = sz.val →
    dvalue_bv_all_poison (memory_bytes_to_bits_value sz dbs) = true →
    dbs.all is_all_poison_byte = true := by
  intro sz dbs hw hl h
  have hd := (reader_bits_fwd sz.val dbs).trans (@get_bits_fwd_concat Pa dbs sz.val hw hl)
  change (get_bits_of_memory_byte_list sz.val dbs []).reverse = _ at hd
  simp only [memory_bytes_to_bits_value, hd] at h
  split at h
  · apply List.all_eq_true.mpr
    intro b hb
    have hbits := forallb_concat_map is_poison_bit memory_byte_to_memory_bits dbs b h hb
    cases b with
    | BYTE_Pointer p i => rw [BYTE_Pointer_bits] at hbits; contradiction
    | BYTE_I x => rw [BYTE_I_bits] at hbits; contradiction
    | BYTE_Mixed bits => exact hbits
  · split at h <;> contradiction

theorem packed_extent_store : ∀ (dts : List dtyp), FORALL (fun t ↦ byte_layout t ∧ alloc_size_dtyp t = store_size_dtyp t) dts →
    struct_fields_extent true dts = dts.foldr (fun t a ↦ store_size_dtyp t + a) 0 := by
  intro ts h
  simp only [struct_fields_extent, if_true, fold_left_add_right, Nat.zero_add]
  induction ts with
  | nil => rfl
  | cons t ts ih =>
    change (_ ∧ alloc_size_dtyp t = _) ∧ _ at h
    simp only [List.foldr_cons, h.1.2, ih h.2]

theorem byte_layout_serializable : ∀ (dt : dtyp), byte_layout dt → serializable dt := by
  intro dt
  induction dt using dtyp_ind with
  | base b => cases b <;> simp [byte_layout, serializable, serializable_base]
  | struct p ts ih =>
    cases p with
    | false => simp [byte_layout]
    | true =>
      intro hl
      rw [serializable]
      apply (FORALL_forall _ _).mpr
      apply List.forall_iff_forall_mem.mpr
      have h : FORALL (fun t ↦ byte_layout t ∧ alloc_size_dtyp t = store_size_dtyp t) ts := by
        simpa only [byte_layout, FORALL] using hl
      intro t ht
      exact ih t ht (List.forall_iff_forall_mem.mp ((FORALL_forall _ _).mp h) t ht).1
  | array v n t ih => cases v <;> simp only [byte_layout, serializable] <;> grind

theorem byte_layout_empty_store_size : ∀ (dt : dtyp), byte_layout dt → dtyp_is_empty dt = true → store_size_dtyp dt = 0 := by
  intro dt
  induction dt using dtyp_ind with
  | base b => simp [dtyp_is_empty]
  | struct p ts ih =>
    cases p with
    | false => simp [byte_layout]
    | true =>
      intro hl he
      have hs : FORALL (fun t ↦ byte_layout t ∧ alloc_size_dtyp t = store_size_dtyp t) ts := by
        simpa only [FORALL, byte_layout] using hl
      rw [store_size_dtyp_Packed_struct, packed_extent_store ts hs]
      have hf := List.forall_iff_forall_mem.mp ((FORALL_forall _ _).mp hs)
      have hem : ts.all dtyp_is_empty = true := by simpa only [dtyp_is_empty] using he
      have hall (t : dtyp) (ht : t ∈ ts) := ih t ht (hf t ht).1 (List.all_eq_true.mp hem t ht)
      clear ih hl hs he hf hem
      induction ts with
      | nil => rfl
      | cons t ts ih =>
        rw [List.foldr_cons, hall t (.head _), Nat.zero_add]
        exact ih fun u hu ↦ hall u (.tail _ hu)
  | array v n t ih =>
    intro hl he
    have ht : byte_layout t := by cases v <;> simp_all [byte_layout]
    have sz : store_size_dtyp (DTYPE_Array v n t) = n * store_size_dtyp t := by
      cases v with
      | true => exact store_size_unpacked_vector _ _ (byte_layout_not_packed _ _ _ ht)
      | false => rw [store_size_dtyp_array]; rw [byte_layout] at hl; rw [hl.2]
    rw [sz]
    have hem : n = 0 ∨ dtyp_is_empty t = true := by simpa [dtyp_is_empty] using he
    rcases hem with rfl | hem <;> simp_all

def rt_bytes (dt : dtyp) (mb : List memory_byte) (dv : dvalue) : Prop :=
  (dv = poison_of_dtyp dt → mb.all is_all_poison_byte = true) ∧
  ∀ acc o bs, acc_dvalue_to_memory_bytes_h dt dv 0 none acc = raise_ret (o, bs) →
    ∃ w, bs = w ++ acc ∧ List.Forall₂ same_bits mb w.reverse

theorem rt_bytes_poison : ∀ (dt : dtyp) {mb : List memory_byte}, byte_layout dt → List.Forall memory_byte_wf mb →
    mb.length = store_size_dtyp dt → mb.all is_all_poison_byte = true →
    rt_bytes dt mb (poison_of_dtyp dt) := by
  intro dt mb hl hw hlen hp
  refine ⟨fun _ ↦ hp, ?_⟩
  intro acc o bs h
  cases he : dtyp_is_empty dt with
  | false =>
    rw [poison_of_dtyp_nonempty dt he] at h
    refine ⟨_, write_poison_layout dt acc hl h, ?_⟩
    rw [List.reverse_replicate, ← hlen]; exact same_bits_all_poison hw hp
  | true =>
    rw [poison_of_dtyp_empty dt he] at h
    have hs := byte_layout_serializable dt hl
    have ht := @empty_dvalue_has_dtyp Pa dt (serializable_NO_VOID dt hs) he
    obtain ⟨w, hbs, hn, _⟩ := @round_trip_h Pa _ dt ht hs none acc o bs h
    have h0 := byte_layout_empty_store_size dt hl he
    have hmb : mb = [] := List.length_eq_zero_iff.mp (hlen.trans h0)
    have hz : w = [] := List.length_eq_zero_iff.mp (hn.trans h0)
    subst mb; subst w; exact ⟨[], hbs, .nil⟩

private theorem byteValue_readback {sz : Positive} {mb : List memory_byte} {v : dvalue_bv sz}
    (hw : List.Forall memory_byte_wf mb) (hn : 8 * mb.length = sz.val)
    (h : memory_bytes_to_byte_value sz mb = raise_ret v) :
    (dvalue_bv_all_poison v = true → mb.all is_all_poison_byte = true) ∧
    List.Forall₂ same_bits mb ((Nseq 0 mb.length).map (memory_byte_of_dvalue_bv v)) := by
  have fallback : (dvalue_bv_all_poison (memory_bytes_to_bits_value sz mb) = true →
      mb.all is_all_poison_byte = true) ∧ List.Forall₂ same_bits mb
        ((Nseq 0 mb.length).map (memory_byte_of_dvalue_bv (memory_bytes_to_bits_value sz mb))) :=
    ⟨bits_value_all_poison hw hn, bits_value_same_bits hw hn⟩
  unfold memory_bytes_to_byte_value at h
  cases es : memory_bytes_to_pointer_slice mb with
  | none => rw [es] at h; cases h; exact fallback
  | some pk =>
    obtain ⟨p, k⟩ := pk
    rw [es] at h
    cases ha : pointer_chunk_aligned sz k with
    | false => simp only [ha, Bool.false_eq_true, if_false] at h; cases h; exact fallback
    | true =>
      simp only [ha, if_true] at h
      cases h
      refine ⟨by intro h; contradiction, ?_⟩
      have hal : (k*8) % sz.val = 0 := by
        have := (Bool.and_eq_true_iff.mp ha).2; simpa using this
      have hstart : sz.val * (k*8 / sz.val) / 8 = k := by
        have he := Nat.mod_add_div (k*8) sz.val
        rw [hal, Nat.zero_add] at he
        rw [he]; omega
      change List.Forall₂ same_bits mb ((Nseq 0 mb.length).map
        (fun i ↦ BYTE_Pointer p (sz.val * (k*8 / sz.val) / 8 + i)))
      rw [hstart, map_Nseq_shift, Nat.add_zero]
      exact pointer_slice_from_same_bits p k hw (pointer_slice_some mb es)

theorem rt_bytes_B : ∀ (sz : Positive) {mb : List memory_byte} {dv : dvalue}, sz.val % 8 = 0 →
    List.Forall memory_byte_wf mb → mb.length = store_size_dtyp (DTYPE_Base (DTYPE_B sz)) →
    memory_bytes_to_dvalue mb (DTYPE_Base (DTYPE_B sz)) = raise_ret dv →
    rt_bytes (DTYPE_Base (DTYPE_B sz)) mb dv := by
  intro sz mb dv h8 hw hlen hr
  have hl : byte_layout (DTYPE_Base (DTYPE_B sz)) := by simpa only [byte_layout] using h8
  have hn : 8 * mb.length = sz.val := by rw [hlen]; exact store_size_B_bytes sz h8
  rw [memory_bytes_to_dvalue, List.take_of_length_le (Nat.le_of_eq hlen), memory_bytes_to_dvalue_base] at hr
  cases hap : all_poison_bytes mb with
  | true =>
    simp only [hap, if_true] at hr
    cases hr
    simpa only [poison_of_dtyp_base] using rt_bytes_poison _ hl hw hlen ((all_poison_bytes_forallb mb).symm.trans hap)
  | false =>
    simp only [hap, Bool.false_eq_true, if_false] at hr
    cases eb : memory_bytes_to_byte_value sz mb with
    | raise_error _ | raise_oom _ | raise_ub _ => rw [eb] at hr; contradiction
    | raise_ret bv =>
      rw [eb] at hr
      obtain ⟨hps, hbits⟩ := byteValue_readback hw hn eb
      change (DVALUE_Base <$> (if dvalue_bv_all_poison bv then pure DVALUE_Poison
        else pure (DVALUE_B sz bv) : EOU dvalue_base)) = raise_ret dv at hr
      cases ep : dvalue_bv_all_poison bv with
      | true => rw [ep] at hr; cases hr; simpa only [poison_of_dtyp_base] using rt_bytes_poison _ hl hw hlen (hps ep)
      | false =>
        rw [ep] at hr; cases hr
        refine ⟨?_, ?_⟩
        · rw [poison_of_dtyp_base]; intro h; cases h
        intro acc o bs hb
        refine ⟨_, write_base_block hb, ?_⟩
        simpa only [List.reverse_reverse, ← hlen] using (show List.Forall₂ same_bits mb
          ((Nseq 0 mb.length).map (base_byte_gen (DVALUE_B sz bv))) from hbits)

private theorem layoutChunk {t : dtyp} {np offset : Nat} {dbs : List memory_byte} {v : dvalue}
    (hl : byte_layout t) (hw : List.Forall memory_byte_wf dbs) (hs : store_size_dtyp t ≤ dbs.length)
    (hpre : (take (np-offset) dbs).all is_all_poison_byte = true)
    (ih : ∀ (chunk : List memory_byte) (v : dvalue), List.Forall memory_byte_wf chunk →
      chunk.length = store_size_dtyp t → memory_bytes_to_dvalue chunk t = raise_ret v → rt_bytes t chunk v)
    (h : (if offset + store_size_dtyp t ≤ np then pure (poison_of_dtyp t)
      else memory_bytes_to_dvalue (take (store_size_dtyp t) dbs) t) = raise_ret v) :
    rt_bytes t (take (store_size_dtyp t) dbs) v := by
  have hc := take_length_exact _ _ hs
  have hf := Forall_take_N _ (store_size_dtyp t) _ hw
  split at h
  · rename_i hle
    cases h
    apply rt_bytes_poison t hl hf hc
    simpa only [drop, List.drop_zero] using
      forallb_sub dbs (n := np-offset) 0 (store_size_dtyp t) (by omega) hpre
  · exact ih _ _ hf hc h

private theorem tailPrefix {dbs : List memory_byte} {np off : Nat} (n : Nat)
    (h : (take (np-off) dbs).all is_all_poison_byte = true) :
    (take (np-(off+n)) (drop n dbs)).all is_all_poison_byte = true := by
  have hd := forallb_drop_pres _ _ n h
  simpa only [drop_take, Nat.sub_sub] using hd

private theorem layoutAppend {dbs w₁ w₂ : List memory_byte} {n : Nat}
    (h₁ : List.Forall₂ same_bits (take n dbs) w₁.reverse)
    (h₂ : List.Forall₂ same_bits (drop n dbs) w₂.reverse) :
    List.Forall₂ same_bits dbs (w₂ ++ w₁).reverse := by
  simpa only [take_drop_app, List.reverse_append] using List.rel_append h₁ h₂

theorem read_array_loop_bytes : ∀ {t : dtyp} (np n offset : Nat) {dbs : List memory_byte} {elts : List dvalue},
    byte_layout t →
    (∀ (chunk : List memory_byte) (v : dvalue), List.Forall memory_byte_wf chunk →
      chunk.length = store_size_dtyp t → memory_bytes_to_dvalue chunk t = raise_ret v → rt_bytes t chunk v) →
    List.Forall memory_byte_wf dbs → dbs.length = n * store_size_dtyp t →
    (take (np-offset) dbs).all is_all_poison_byte = true →
    read_array_loop memory_bytes_to_dvalue np (store_size_dtyp t) t n offset dbs = raise_ret elts →
    (dtyp_is_empty t = false → elts.all dvalue_is_poison = true → dbs.all is_all_poison_byte = true) ∧
    (∀ off acc o bs, array_bytes_loop acc_dvalue_to_memory_bytes_h none t 0 elts off acc = raise_ret (o,bs) →
      ∃ w, bs = w ++ acc ∧ List.Forall₂ same_bits dbs w.reverse) := by
  intro t np n
  induction n with
  | zero =>
    intro offset dbs elts _ _ _ hlen _ hr
    have hnil : dbs = [] := List.length_eq_zero_iff.mp (by simpa using hlen)
    subst dbs
    change raise_ret [] = raise_ret elts at hr
    cases hr
    refine ⟨fun _ _ ↦ rfl, ?_⟩
    intro off acc o bs h
    rw [array_bytes_loop_nil] at h; cases h; exact ⟨[], rfl, .nil⟩
  | succ n ih =>
    intro offset dbs elts hl hel hw hlen hpre hr
    rw [read_array_loop_cons] at hr
    obtain ⟨v, hv, hr⟩ := EOU_bind_ret_inv _ _ _ hr
    obtain ⟨vs, hvs, hr⟩ := EOU_bind_ret_inv _ _ _ hr
    change raise_ret (v :: vs) = raise_ret elts at hr
    cases hr
    rw [Nat.succ_mul] at hlen
    have hf := layoutChunk hl hw (by omega) hpre hel hv
    have htail := Forall_drop_N _ (store_size_dtyp t) _ hw
    obtain ⟨ihp, ihw⟩ := ih (offset + store_size_dtyp t) hl hel htail
      (by rw [length_drop_N]; omega) (tailPrefix _ hpre) hvs
    constructor
    · intro hne hps
      obtain ⟨h₁, h₂⟩ := Bool.and_eq_true_iff.mp hps
      have hhead := hf.1 ((dvalue_is_poison_true v h₁).trans (poison_of_dtyp_nonempty t hne).symm)
      simpa only [← List.all_append, take_drop_app] using
        (Bool.and_eq_true_iff.mpr ⟨hhead, ihp hne h₂⟩)
    · intro off acc o bs h
      rw [array_bytes_loop_cons] at h
      obtain ⟨⟨coff, cbs⟩, hc, h⟩ := EOU_bind_ret_inv _ _ _ h
      obtain ⟨w₁, rfl, h₁⟩ := hf.2 acc coff cbs hc
      change array_bytes_loop _ none t 0 vs (off+coff) (w₁ ++ acc) = raise_ret (o,bs) at h
      obtain ⟨w₂, hb, h₂⟩ := ihw _ _ _ _ h
      exact ⟨w₂ ++ w₁, by simpa only [List.append_assoc] using hb, layoutAppend h₁ h₂⟩

theorem read_struct_loop_bytes : ∀ (np : Nat) (dts : List dtyp) (offset : Nat) {dbs : List memory_byte} {vs : List dvalue},
    FORALL (fun t ↦ byte_layout t ∧ alloc_size_dtyp t = store_size_dtyp t) dts →
    (∀ t ∈ dts, ∀ (chunk : List memory_byte) (v : dvalue), List.Forall memory_byte_wf chunk →
      chunk.length = store_size_dtyp t → memory_bytes_to_dvalue chunk t = raise_ret v → rt_bytes t chunk v) →
    List.Forall memory_byte_wf dbs → dbs.length = dts.foldr (fun t a ↦ store_size_dtyp t + a) 0 →
    (take (np-offset) dbs).all is_all_poison_byte = true →
    read_struct_loop memory_bytes_to_dvalue np none offset dts dbs = raise_ret vs →
    (fields_all_poison dts vs = true → dbs.all is_all_poison_byte = true) ∧
    (∀ off acc o bs, struct_bytes_loop acc_dvalue_to_memory_bytes_h none none vs dts off acc = raise_ret (o,bs) →
      ∃ w, bs = w ++ acc ∧ List.Forall₂ same_bits dbs w.reverse) := by
  intro np ts
  induction ts with
  | nil =>
    intro offset dbs vs _ _ _ hlen _ hr
    have hnil : dbs = [] := List.length_eq_zero_iff.mp hlen
    subst dbs
    change raise_ret [] = raise_ret vs at hr
    cases hr
    refine ⟨fun _ ↦ rfl, ?_⟩
    intro off acc o bs h
    rw [struct_bytes_loop_nil] at h; cases h; exact ⟨[], rfl, .nil⟩
  | cons t ts ih =>
    intro offset dbs vs hl hel hw hlen hpre hr
    obtain ⟨⟨hlt, htight⟩, hls⟩ := hl
    rw [read_struct_loop_cons] at hr
    simp only [Option.isSome, Bool.false_eq_true, if_false, Nat.add_zero, drop, List.drop_zero,
      htight] at hr
    obtain ⟨v, hv, hr⟩ := EOU_bind_ret_inv _ _ _ hr
    obtain ⟨vs', hvs, hr⟩ := EOU_bind_ret_inv _ _ _ hr
    change raise_ret (v :: vs') = raise_ret vs at hr
    cases hr
    simp only [List.foldr_cons] at hlen
    have hf := layoutChunk hlt hw (by omega) hpre (hel t (.head _)) hv
    obtain ⟨ihp, ihw⟩ := ih (offset + store_size_dtyp t) hls (fun u hu ↦ hel u (.tail _ hu))
      (Forall_drop_N _ _ _ hw) (by rw [length_drop_N]; omega) (tailPrefix _ hpre) hvs
    constructor
    · intro hps
      obtain ⟨h₁, h₂⟩ := Bool.and_eq_true_iff.mp hps
      have hhead : (take (store_size_dtyp t) dbs).all is_all_poison_byte = true := by
        cases he : dtyp_is_empty t with
        | true => rw [byte_layout_empty_store_size t hlt he]; rfl
        | false =>
          apply hf.1
          rw [poison_of_dtyp_nonempty t he]
          exact dvalue_is_poison_true _ (by simpa only [he, Bool.false_or] using h₁)
      simpa only [← List.all_append, take_drop_app] using
        (Bool.and_eq_true_iff.mpr ⟨hhead, ihp h₂⟩)
    · intro off acc o bs h
      rw [struct_bytes_loop_cons] at h
      simp only [Option.map_none, accumulate_padding, htight, Nat.sub_self] at h
      obtain ⟨⟨coff, cbs⟩, hc, h⟩ := EOU_bind_ret_inv _ _ _ h
      obtain ⟨w₁, rfl, h₁⟩ := hf.2 acc coff cbs hc
      change struct_bytes_loop _ none none vs' ts (off+coff) (w₁ ++ acc) = raise_ret (o,bs) at h
      obtain ⟨w₂, hb, h₂⟩ := ihw _ _ _ _ h
      exact ⟨w₂ ++ w₁, by simpa only [List.append_assoc] using hb, layoutAppend h₁ h₂⟩

private theorem layoutEmptyOrDistinct {dt : dtyp} {mb : List memory_byte} {v : dvalue}
    (hl : byte_layout dt) (hlen : mb.length = store_size_dtyp dt)
    (hne : v ≠ DVALUE_Base DVALUE_Poison) (heq : v = poison_of_dtyp dt) :
    mb.all is_all_poison_byte = true := by
  cases he : dtyp_is_empty dt with
  | false => exact (hne (heq.trans (poison_of_dtyp_nonempty _ he))).elim
  | true =>
    have hz := hlen.trans (byte_layout_empty_store_size dt hl he)
    rw [List.length_eq_zero_iff.mp hz]; rfl

theorem bytes_round_trip_h : ∀ (dt : dtyp), byte_layout dt → ∀ {mb : List memory_byte} {dv : dvalue},
    List.Forall memory_byte_wf mb → mb.length = store_size_dtyp dt →
    memory_bytes_to_dvalue mb dt = raise_ret dv → rt_bytes dt mb dv := by
  intro dt
  induction dt using dtyp_ind with
  | base b =>
    intro hl mb dv hw hlen hr
    cases b <;> simp only [byte_layout] at hl <;> try contradiction
    exact rt_bytes_B _ hl hw hlen hr
  | struct p ts ih =>
    intro hl mb dv hw hlen hr
    cases p with
    | false => simp [byte_layout] at hl
    | true =>
      have hs : FORALL (fun t ↦ byte_layout t ∧ alloc_size_dtyp t = store_size_dtyp t) ts := by
        simpa only [byte_layout, FORALL] using hl
      have hf := List.forall_iff_forall_mem.mp ((FORALL_forall _ _).mp hs)
      have hpre := poison_split_prefix mb
      obtain ⟨np, rest, es⟩ : ∃ n r, poison_split mb = (n, r) := ⟨_, _, rfl⟩
      rw [es] at hpre
      rw [read_struct_unfold, es] at hr
      cases rest with
      | nil =>
        cases hr
        apply rt_bytes_poison _ hl hw hlen
        rw [← all_poison_bytes_forallb]; simp [all_poison_bytes, es]
      | cons b bs =>
        change (canonicalize_agg (DTYPE_Struct true ts) <$>
          read_struct_loop memory_bytes_to_dvalue np none 0 ts mb) = raise_ret dv at hr
        cases ev : read_struct_loop memory_bytes_to_dvalue np none 0 ts mb with
        | raise_error _ | raise_oom _ | raise_ub _ => rw [ev] at hr; contradiction
        | raise_ret vs =>
          rw [ev] at hr; cases hr
          obtain ⟨hps, hwrite⟩ := read_struct_loop_bytes np ts 0 hs
            (fun t ht c v ↦ @ih t ht (hf t ht).1 c v) hw
            (hlen.trans ((store_size_dtyp_Packed_struct ts).trans (packed_extent_store ts hs)))
            (by simpa using hpre) ev
          unfold canonicalize_agg
          cases ep : agg_is_poison (DTYPE_Struct true ts) vs with
          | true =>
            simp only [if_true]
            rw [← poison_of_dtyp_nonempty _ (@agg_is_poison_nonempty Pa _ _ ep)]
            apply rt_bytes_poison _ hl hw hlen
            exact hps (Bool.and_eq_true_iff.mp ep).2
          | false =>
            simp only [Bool.false_eq_true, ite_false]
            refine ⟨layoutEmptyOrDistinct hl hlen (by intro h; cases h), ?_⟩
            intro acc o out h
            rw [ser_struct_unfold] at h
            exact hwrite 0 acc o out h
  | array v n t ih =>
    intro hl mb dv hw hlen hr
    have ht : byte_layout t := by
      cases v <;> rw [byte_layout] at hl
      · exact hl.1
      · exact hl
    have tight : (if v then store_size_dtyp t else alloc_size_dtyp t) = store_size_dtyp t := by
      cases v with
      | true => rfl
      | false => rw [byte_layout] at hl; exact hl.2
    have pad : (if v then 0 else alloc_size_dtyp t - store_size_dtyp t) = 0 := by
      cases v with
      | true => rfl
      | false =>
        change alloc_size_dtyp t = store_size_dtyp t at tight
        change alloc_size_dtyp t - store_size_dtyp t = 0
        rw [tight, Nat.sub_self]
    have npack := byte_layout_not_packed v n t ht
    have hn : mb.length = n * store_size_dtyp t := by
      rw [hlen]
      cases v with
      | true => exact store_size_unpacked_vector _ _ npack
      | false => rw [store_size_dtyp_array]; simpa only [Bool.false_eq_true, if_false] using congrArg (n*·) tight
    have hpre := poison_split_prefix mb
    obtain ⟨np, rest, es⟩ : ∃ n r, poison_split mb = (n, r) := ⟨_, _, rfl⟩
    rw [es] at hpre
    rw [read_array_unfold, es] at hr
    cases rest with
    | nil =>
      cases hr
      apply rt_bytes_poison _ hl hw hlen
      rw [← all_poison_bytes_forallb]; simp [all_poison_bytes, es]
    | cons b bs =>
      simp only [npack, tight] at hr
      obtain ⟨vs, ev, hr⟩ := EOU_bind_ret_inv _ _ _ hr
      cases hr
      obtain ⟨hps, hwrite⟩ := read_array_loop_bytes np n 0 ht (fun c v ↦ @ih ht c v) hw hn
        (by simpa using hpre) ev
      unfold canonicalize_agg
      cases ep : agg_is_poison (DTYPE_Array v n t) vs with
      | true =>
        have he := @agg_is_poison_nonempty Pa _ _ ep
        have he' : dtyp_is_empty t = false := (Bool.or_eq_false_iff.mp (by
          simpa only [dtyp_is_empty] using he)).2
        simp only [if_true]
        rw [← poison_of_dtyp_nonempty _ he]
        exact rt_bytes_poison _ hl hw hlen (hps he' (Bool.and_eq_true_iff.mp ep).2)
      | false =>
        simp only [Bool.false_eq_true, ite_false]
        refine ⟨layoutEmptyOrDistinct hl hlen (by intro h; cases h), ?_⟩
        intro acc o out h
        rw [ser_array_unfold, npack] at h
        exact hwrite 0 acc o out (by simpa only [pad] using h)

theorem memory_bytes_round_trip_bytes : ∀ (dt : dtyp) {mb : List memory_byte} {dv : dvalue} {mb' : List memory_byte},
    byte_layout dt → List.Forall memory_byte_wf mb → mb.length = store_size_dtyp dt →
    memory_bytes_to_dvalue mb dt = raise_ret dv → dvalue_to_memory_bytes dt dv none = raise_ret mb' →
    List.Forall₂ same_bits mb mb' := by
  intro dt mb dv out hl hw hlen hr hwrite
  unfold dvalue_to_memory_bytes at hwrite
  obtain ⟨⟨o, bs⟩, hb, h⟩ := EOU_bind_ret_inv _ _ _ hwrite
  change raise_ret bs.reverse = raise_ret out at h
  cases h
  obtain ⟨w, rfl, hs⟩ := (bytes_round_trip_h dt hl hw hlen hr).2 [] o bs hb
  simpa using hs

end Vellvm.Theory.MemoryBytesFacts
