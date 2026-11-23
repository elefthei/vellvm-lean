import Vellvm.Theory.MemoryBytesFacts.Aggregate
import Vellvm.Utils.ZUtil

namespace Vellvm.Theory.MemoryBytesFacts
open Vellvm Vellvm.Numeric Vellvm.Semantics Vellvm.Semantics.Interfaces.Params
open Vellvm.Semantics.DynamicValues Vellvm.Semantics.MemoryBytes Vellvm.Semantics.VellvmIntegers
open Vellvm.Semantics.EOU Vellvm.Syntax.DynamicTypes Vellvm.Utils.ListUtil Vellvm.Utils.ZUtil
open Vellvm.Numeric.Integers (bit_int)
universe u
variable [Pa : Params]

def memory_byte_wf : memory_byte → Prop
  | BYTE_Mixed bits => bits.length = 8
  | _ => True

theorem memory_byte_bits_length (mb : memory_byte) :
    memory_byte_wf mb → (memory_byte_to_memory_bits mb).length = 8 := by
  cases mb <;> simp [memory_byte_wf, memory_byte_to_memory_bits, dvalue_bv_to_memory_bits,
    memory_bits_from, rev_loop_acc_length]

def get_bits_fwd (n : Nat) : List memory_byte → List memory_bit
  | [] => List.replicate n Bit_psn
  | b :: bs => if n < 8 then take n (memory_byte_to_memory_bits b)
      else memory_byte_to_memory_bits b ++ get_bits_fwd (n - 8) bs

theorem get_bits_fwd_spec (dbs : List memory_byte) (n : Nat) (acc : List memory_bit) :
    get_bits_of_memory_byte_list n dbs acc = (get_bits_fwd n dbs).reverseAux acc := by
  induction dbs generalizing n acc with
  | nil => cases n <;> simp [get_bits_fwd, get_bits_of_memory_byte_list, rev_loop_acc_const, List.reverseAux_eq]
  | cons b bs ih =>
    by_cases h : n < 8 <;> simp [get_bits_fwd, get_bits_of_memory_byte_list, h, ih,
      List.reverseAux_eq, List.append_assoc]

theorem reader_bits_fwd (n : Nat) (dbs : List memory_byte) :
    (get_bits_of_memory_byte_list n dbs []).reverseAux [] = get_bits_fwd n dbs := by
  simp [get_bits_fwd_spec, List.reverseAux_eq]

theorem get_bits_fwd_length {dbs : List memory_byte} (n : Nat) :
    List.Forall memory_byte_wf dbs → (get_bits_fwd n dbs).length = n := by
  intro hw
  induction dbs generalizing n with
  | nil => simp [get_bits_fwd]
  | cons b bs ih =>
    obtain ⟨hb, hs⟩ := (List.forall_cons _ _ _).mp hw
    have hl := memory_byte_bits_length b hb
    by_cases h : n < 8
    · simp [get_bits_fwd, h, take, hl, Nat.min_eq_left h.le]
    · simp [get_bits_fwd, h, hl, ih _ hs]; omega

omit Pa in
theorem concat_bits_Z_digits (l : List Int) :
    concat_bits_Z l = concat_digits 1 l := by
  induction l <;> simp [concat_bits_Z, concat_digits, shiftl, Int.shiftLeft_eq, *, mul_comm]

omit Pa in
theorem concat_bytes_Z_digits (l : List Int) :
    concat_bytes_Z l = concat_digits 8 l := by
  induction l <;> simp [concat_bytes_Z, concat_digits, shiftl, Int.shiftLeft_eq, *, mul_comm]

omit Pa in
theorem bit_unsigned_range (b : int1) :
    0 ≤ unsigned b ∧ unsigned b < (2 : Int) ^ (1 : Nat) := by
  exact Integers.unsigned_range b

omit Pa in
theorem extract_bit_vint_spec {sz : Positive} (x : bit_int sz) {i : Nat} :
    i < sz.val → extract_bit_vint x i = unsigned x / 2 ^ i % 2 := by
  intro hi
  have hwidth := @Integers.wordsize_max_unsigned sz
  have hidx : Integers.unsigned (Integers.repr (w := sz) (i : Int)) = i :=
    Integers.unsigned_repr _ ⟨by omega, by change (sz.val : Int) ≤ _ at hwidth; omega⟩
  have hshift : Integers.unsigned (Integers.shru x (Integers.repr (i : Int))) =
      unsigned x / 2 ^ i := by
    have hind := congrArg Int.toNat hidx
    change (Integers.repr (w := sz) (i : Int)).bits.toNat = i at hind
    change Int.ofNat (x.bits >>> (Integers.repr (w := sz) (i : Int)).bits.toNat).toNat =
      (x.bits.toNat : Int) / 2 ^ i
    rw [hind, BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]
    simp only [Int.ofNat_eq_natCast, Int.natCast_ediv, Int.natCast_pow, Int.cast_ofNat_Int]
  change Integers.unsigned (Integers.repr ((Integers.unsigned (Integers.shru x (Integers.repr (i : Int)))).fmod
    (Integers.unsigned (Integers.repr (w := sz) 2)))) = _
  rw [hshift]
  by_cases h1 : sz.val = 1
  · obtain rfl : sz = ⟨1, by decide⟩ := Subtype.ext h1
    obtain rfl : i = 0 := by omega
    have hr := bit_unsigned_range x
    change 0 ≤ unsigned x ∧ unsigned x < 2 at hr
    change Integers.unsigned (Integers.repr ((unsigned x / 2 ^ (0 : Nat)).fmod 0)) = _
    change 0 ≤ Integers.unsigned x ∧ Integers.unsigned x < 2 at hr
    simp [show VInt.unsigned x = Integers.unsigned x from rfl, Int.emod_eq_of_lt hr.1 hr.2, Integers.repr_unsigned]
  · have ht : Integers.unsigned (Integers.repr (w := sz) 2) = 2 :=
      Integers.unsigned_repr _ ⟨by decide, by change (sz.val : Int) ≤ _ at hwidth; have := sz.property; omega⟩
    rw [ht, Int.fmod_eq_emod_of_nonneg _ (by decide)]
    apply Integers.unsigned_repr
    have hp := Int.emod_lt_of_pos (unsigned x / 2 ^ i) (by decide : (0 : Int) < 2)
    have := sz.property
    change (sz.val : Int) ≤ _ at hwidth
    exact ⟨Int.emod_nonneg _ (by decide), by omega⟩

omit Pa in
theorem extract_bit_vint_8 (x : int8) {i : Nat} :
    i < 8 → extract_bit_vint x i = unsigned x / 2 ^ i % 2 := by
  exact extract_bit_vint_spec x

theorem BYTE_I_bits (x : int8) :
    memory_byte_to_memory_bits (BYTE_I (Pa := Pa) x) =
    (Nseq 0 8).map (fun i ↦ Bit_bit (VInt.repr (extract_bit_vint x i))) := by
  simp [memory_byte_to_memory_bits, dvalue_bv_to_memory_bits, memory_bits_from, rev_loop_acc_app]
  intro _ _; rfl

theorem get_bits_fwd_concat {dbs : List memory_byte} {n : Nat} :
    List.Forall memory_byte_wf dbs → 8 * dbs.length = n →
    get_bits_fwd n dbs = (dbs.map memory_byte_to_memory_bits).flatten := by
  intro hw hn
  induction dbs generalizing n with
  | nil => simp at hn; subst n; rfl
  | cons b bs ih =>
    obtain ⟨_, hs⟩ := (List.forall_cons _ _ _).mp hw
    simp only [List.length_cons] at hn
    simp [get_bits_fwd, show ¬n < 8 by omega, ih hs (show 8 * bs.length = n - 8 by omega)]

theorem memory_bits_to_Z_ints (bis : List int1) :
    memory_bits_to_Z (bis.map (Bit_bit (Pa := Pa))) = raise_ret (some (concat_bits_Z (bis.map unsigned))) := by
  have h : map_monad (m := EOUP) memory_bit_to_bit (bis.map (Bit_bit (Pa := Pa))) =
      raise_ret (some (bis.map unsigned)) := by
    induction bis with
    | nil => rfl
    | cons b bs ih => rw [List.map_cons, map_monad_cons_EOUP, ih]; rfl
  rw [memory_bits_to_Z, h]; rfl

def bytes_of_bits : Nat → List memory_bit → List memory_byte
  | 0, _ => []
  | n + 1, bits => memory_byte_of_bits (take 8 bits) :: bytes_of_bits n (drop 8 bits)

theorem acc_bits_to_memory_bytes_fwd (n : Nat) (bits : List memory_bit) (acc : List memory_byte) :
    acc_bits_to_memory_bytes n bits acc = (bytes_of_bits n bits).reverse ++ acc := by
  induction n generalizing bits acc with
  | zero => rfl
  | succ n ih => simp [acc_bits_to_memory_bytes, bytes_of_bits, ih, List.append_assoc, take, drop]

theorem all_int_bits_map (bits : List memory_bit) :
    bits.all is_int_bit = true →
    ∃ bis : List int1, bits = bis.map Bit_bit := by
  induction bits with
  | nil => exact fun _ ↦ ⟨[], rfl⟩
  | cons b bs ih =>
    rw [List.all_cons, Bool.and_eq_true]; rintro ⟨hb, hs⟩
    obtain ⟨ys, rfl⟩ := ih hs
    cases b with
    | Bit_bit x => exact ⟨x :: ys, rfl⟩
    | _ => cases hb

theorem forallb_int_map (bis : List int1) :
    (bis.map (Bit_bit (Pa := Pa))).all is_int_bit = true := by
  induction bis <;> simp [List.all_cons, is_int_bit, *]

theorem int_bits_to_Z_map (bis : List int1) :
    int_bits_to_Z (bis.map (Bit_bit (Pa := Pa))) = concat_bits_Z (bis.map unsigned) := by
  induction bis <;> simp [int_bits_to_Z, concat_bits_Z, *] <;> rfl

omit Pa in
theorem concat_bits_Z_range (bis : List int1) :
    0 ≤ concat_bits_Z (bis.map unsigned) ∧ concat_bits_Z (bis.map unsigned) < 2 ^ bis.length := by
  induction bis with
  | nil => decide
  | cons b bs ih =>
    have hb := bit_unsigned_range b
    simp only [List.map_cons, concat_bits_Z, List.length_cons, pow_succ]
    change 0 ≤ unsigned b ∧ unsigned b < 2 at hb
    omega

omit Pa in
theorem concat_bits_Z_nth (bis : List int1) {i : Nat} :
    i < bis.length →
    concat_bits_Z (bis.map unsigned) / 2 ^ i % 2 = unsigned (bis.getD i (VInt.repr 0)) := by
  intro hi
  rw [concat_bits_Z_digits]
  have hr : List.Forall (fun z ↦ 0 ≤ z ∧ z < zPow 2 1) (bis.map unsigned) := by
    rw [List.forall_iff_forall_mem]; intro z hz
    obtain ⟨b, _, rfl⟩ := List.mem_map.mp hz
    exact bit_unsigned_range b
  have h := concat_digits_nth 1 (bis.map unsigned) i (by decide) hr (by simpa using hi)
  rw [one_mul] at h
  change concat_digits 1 (bis.map unsigned) / 2 ^ i % 2 = (bis.map unsigned).getD i 0 at h
  rw [h]; exact List.getD_map bis (VInt.repr 0) unsigned

omit Pa in
theorem repr_unsigned_bit (b : int1) :
    VInt.repr (unsigned b) = b := by
  exact Integers.repr_unsigned b

theorem memory_bits_from_map (f : Nat → memory_bit) (n s : Nat) :
    memory_bits_from f n s = (Nseq s n).map f := by
  simp [memory_bits_from, rev_loop_acc_app]

def int_elt_bits {m : Positive} (x : bit_int m) : List int1 :=
  (Nseq 0 m.val).map (fun i ↦ VInt.repr (extract_bit_vint x i))

theorem int_elt_bits_eq {m : Positive} (x : bit_int m) :
    memory_bits_from (fun i ↦ Bit_bit (Pa := Pa) (VInt.repr (extract_bit_vint x i))) m.val 0 =
      (int_elt_bits x).map Bit_bit := by
  simp [memory_bits_from_map, int_elt_bits, List.map_map, Function.comp_def]

omit Pa in
theorem int_elt_bits_length {m : Positive} (x : bit_int m) :
    (int_elt_bits x).length = m.val := by
  simp [int_elt_bits, Nseq_length]

omit Pa in
theorem int_elt_bits_value {m : Positive} (x : bit_int m) :
    concat_bits_Z ((int_elt_bits x).map unsigned) = unsigned x := by
  unfold int_elt_bits
  rw [List.map_map]
  let z := unsigned x
  have h : (Nseq 0 m.val).map (unsigned ∘ fun i ↦ (VInt.repr (extract_bit_vint x i) : int1)) =
      (Nseq 0 m.val).map (fun i ↦ z / 2 ^ i % 2) := by
    apply List.map_congr_left; intro i hi
    have aux := (In_Nseq _ _ _ hi).2
    simp only [Function.comp_apply, extract_bit_vint_spec x (by omega : i < m.val)]
    apply Integers.unsigned_repr
    change 0 ≤ z / 2 ^ i % 2 ∧ z / 2 ^ i % 2 ≤ 1
    omega
  rw [h, concat_bits_Z_extract, pow_zero, Int.ediv_one]
  apply Int.emod_eq_of_lt (Integers.unsigned_range x).1
  have hu := (Integers.unsigned_range x).2
  rw [Integers.modulus_def] at hu
  change z < (2 ^ m.val : Nat) at hu
  change z < 2 ^ m.val
  simpa using hu

theorem memory_byte_of_bits_int (bis : List int1) :
    bis.length = 8 →
    memory_byte_to_memory_bits (memory_byte_of_bits (bis.map (Bit_bit (Pa := Pa)))) = bis.map Bit_bit := by
  intro hl
  rw [memory_byte_of_bits, if_pos (forallb_int_map bis), BYTE_I_bits, int_bits_to_Z_map]
  let z := concat_bits_Z (bis.map unsigned)
  have hz := concat_bits_Z_range bis
  rw [hl] at hz
  have huv : unsigned (Integers.repr (w := ⟨8, by decide⟩) z) = z := by
    apply Integers.unsigned_repr
    change 0 ≤ z ∧ z ≤ 255
    change 0 ≤ z ∧ z < 256 at hz; omega
  have heq : (Nseq 0 8).map (fun i ↦ Bit_bit (Pa := Pa) (VInt.repr
      (extract_bit_vint (Integers.repr (w := ⟨8, by decide⟩) z) i))) =
      (Nseq 0 bis.length).map (fun i ↦ Bit_bit (bis.getD (i - 0) (VInt.repr 0))) := by
    rw [hl]; apply List.map_congr_left; intro i hi
    have hi' := (In_Nseq _ _ _ hi).2
    rw [extract_bit_vint_8 _ (by omega), huv, Nat.sub_zero, concat_bits_Z_nth bis (by omega), repr_unsigned_bit]
  rw [heq]
  simpa only [List.map_map, Function.comp_def] using
    congrArg (List.map (Bit_bit (Pa := Pa))) (map_Nseq_nth bis (VInt.repr 0) 0)

omit Pa in
theorem take_app_ge {A : Type u} (l r : List A) {n : Nat} :
    l.length ≤ n →
    take n (l ++ r) = l ++ take (n - l.length) r := by
  intro h; simp only [take, List.take_append, List.take_of_length_le h]

omit Pa in
theorem take_add {A : Type u} (l : List A) (a b : Nat) :
    take (a + b) l = take a l ++ take b (drop a l) := by
  exact List.take_add

theorem memory_byte_of_bits_bits (c : List memory_bit) :
    c.length = 8 →
    memory_byte_to_memory_bits (memory_byte_of_bits c) = c := by
  intro hl; cases h : c.all is_int_bit with
  | false => simp [memory_byte_of_bits, h, memory_byte_to_memory_bits, dvalue_bv_to_memory_bits]
  | true => obtain ⟨bis, rfl⟩ := all_int_bits_map c h; exact memory_byte_of_bits_int bis (by simpa using hl)

theorem memory_byte_of_bits_wf (c : List memory_bit) :
    c.length = 8 → memory_byte_wf (memory_byte_of_bits c) := by
  intro hl; unfold memory_byte_of_bits; split <;> simp [memory_byte_wf, hl]

theorem take_8_length (l : List memory_bit) :
    8 ≤ l.length → (take 8 l).length = 8 := by
  exact take_length_exact l 8

theorem drop_8_length (l : List memory_bit) :
    (drop 8 l).length = l.length - 8 := by
  exact List.length_drop

theorem bytes_of_bits_length (n : Nat) (l : List memory_bit) :
    (bytes_of_bits n l).length = n := by
  induction n generalizing l <;> simp [bytes_of_bits, *]

theorem bytes_of_bits_wf (n : Nat) (l : List memory_bit) :
    8 * n ≤ l.length →
    List.Forall memory_byte_wf (bytes_of_bits n l) := by
  intro h
  induction n generalizing l with
  | zero => trivial
  | succ n ih =>
    apply (List.forall_cons _ _ _).mpr
    exact ⟨memory_byte_of_bits_wf _ (take_8_length l (by omega)), ih _ (by rw [drop_8_length]; omega)⟩

theorem bytes_of_bits_bits (n : Nat) (l : List memory_bit) :
    8 * n ≤ l.length →
    ((bytes_of_bits n l).map memory_byte_to_memory_bits).flatten = take (8 * n) l := by
  intro h
  induction n generalizing l with
  | zero => simp [bytes_of_bits, take]
  | succ n ih =>
    simp only [bytes_of_bits, List.map_cons, List.flatten_cons]
    rw [memory_byte_of_bits_bits _ (take_8_length _ (by omega)), ih _ (by rw [drop_8_length]; omega),
      show 8 * (n + 1) = 8 + 8 * n by omega, take_add]

theorem get_bits_fwd_app {dbs : List memory_byte} (extra : List memory_byte) {k : Nat} :
    List.Forall memory_byte_wf dbs → k ≤ 8 * dbs.length →
    get_bits_fwd k (dbs ++ extra) = take k (dbs.map memory_byte_to_memory_bits).flatten := by
  intro hw hk
  induction dbs generalizing k with
  | nil =>
    obtain rfl : k = 0 := by simpa using hk
    cases extra <;> simp [get_bits_fwd, take]
  | cons b bs ih =>
    obtain ⟨hb, hs⟩ := (List.forall_cons _ _ _).mp hw
    have hl := memory_byte_bits_length b hb
    simp only [List.length_cons] at hk
    simp only [List.cons_append, get_bits_fwd, List.map_cons, List.flatten_cons]
    split
    · exact (take_app_le _ _ _ (by omega)).symm
    · rw [take_app_ge _ _ (by omega), hl, ih hs (by omega)]

theorem packed_bits_to_dvalue_poison (t : dtyp_base) (m : Positive) {bits : List memory_bit} :
    bits ≠ [] → bits.all is_poison_bit = true → packed_bits_to_dvalue t m bits = DVALUE_Base DVALUE_Poison := by
  intro hn h
  cases bits with
  | nil => exact (hn rfl).elim
  | cons b bs =>
    have hp : is_poison_bit b = true ∧ bs.all is_poison_bit = true := by
      simpa only [List.all_cons, Bool.and_eq_true] using h
    have hb := hp.1
    cases b <;> try cases hb
    all_goals cases t <;> simp [packed_bits_to_dvalue, h, memory_bits_to_Z_poison_cons]

theorem repeat_psn_ne (m : Positive) :
    List.replicate m.val (Bit_psn (Pa := Pa)) ≠ [] := by
  intro h; have := congrArg List.length h; simp at this; exact m.property.ne' this

theorem forallb_poison_bits_repeat (k : Nat) :
    (List.replicate k (Bit_psn (Pa := Pa))).all is_poison_bit = true := by
  induction k <;> simp [List.replicate_succ, List.all_cons, is_poison_bit, *]

theorem int_elt_bits_ne {m : Positive} (x : bit_int m) :
    (int_elt_bits x).map (Bit_bit (Pa := Pa)) ≠ [] := by
  intro h; have := congrArg List.length h; simp [int_elt_bits_length, m.property.ne'] at this

theorem forallb_poison_int_bits {bis : List int1} :
    bis ≠ [] →
    (bis.map (Bit_bit (Pa := Pa))).all is_poison_bit = false := by
  cases bis <;> simp [List.all_cons, is_poison_bit]

theorem map_Bit_bit_ne {bis : List int1} :
    (bis.map (Bit_bit (Pa := Pa))) ≠ [] → bis ≠ [] := by
  rintro h rfl; exact h rfl

theorem packed_elt_round_trip {tb : dtyp_base} {m : Positive} {e : dvalue} {bits : List memory_bit} :
    (tb = DTYPE_I m ∨ tb = DTYPE_B m) → m.val % 8 ≠ 0 → dvalue_has_dtyp e (DTYPE_Base tb) →
    packed_elt_bits m e = raise_ret bits → bits.length = m.val ∧ packed_bits_to_dvalue tb m bits = e := by
  intro ht hm hty he
  have poison (hp : e = DVALUE_Base DVALUE_Poison) :
      bits.length = m.val ∧ packed_bits_to_dvalue tb m bits = e := by
    subst e
    change raise_ret (List.replicate m.val Bit_psn) = raise_ret bits at he
    cases he
    exact ⟨List.length_replicate, packed_bits_to_dvalue_poison _ _ (repeat_psn_ne m) (forallb_poison_bits_repeat _)⟩
  cases hty with
  | DVALUE_Poison_typ_agg => exact poison rfl
  | DVALUE_Base_typ dv _ ht' hc =>
    rcases ht with rfl | rfl <;> cases dv <;>
      first | exact poison rfl | contradiction | simp [dvalue_base_has_dtyp_base] at ht'
    · rename_i w x
      obtain rfl : w = m := Subtype.ext ht'
      change raise_ret (memory_bits_from (fun i ↦ Bit_bit (VInt.repr (extract_bit_vint x i))) _ 0) =
        raise_ret bits at he
      rw [int_elt_bits_eq] at he
      cases he
      refine ⟨by simp [int_elt_bits_length], ?_⟩
      simp only [packed_bits_to_dvalue, memory_bits_to_Z_ints, int_elt_bits_value]
      rw [show Integers.repr (unsigned x) = x from Integers.repr_unsigned x]
    · rename_i w bv
      obtain rfl : w = m := Subtype.ext ht'
      cases bv with
      | BYTE_Pointer p i => simp [dvalue_base_canonical, dvalue_bv_canonical, hm] at hc
      | BYTE_I x =>
        change raise_ret (memory_bits_from (fun i ↦ Bit_bit (VInt.repr (extract_bit_vint x i))) _ 0) =
          raise_ret bits at he
        rw [int_elt_bits_eq] at he
        cases he
        have hn := map_Bit_bit_ne (Pa := Pa) (int_elt_bits_ne (Pa := Pa) x)
        refine ⟨by simp [int_elt_bits_length], ?_⟩
        simp only [packed_bits_to_dvalue, forallb_poison_int_bits hn, forallb_int_map,
          Bool.false_eq_true, if_false, if_true, int_bits_to_Z_map, int_elt_bits_value]
        rw [show Integers.repr (unsigned x) = x from Integers.repr_unsigned x]
      | BYTE_Mixed bs =>
        change raise_ret bs = raise_ret bits at he
        cases he
        simp only [dvalue_base_canonical, dvalue_bv_canonical, Bool.and_eq_true,
          beq_iff_eq, Bool.not_eq_true'] at hc
        obtain ⟨⟨⟨hl, _⟩, hi⟩, hp⟩ := hc
        exact ⟨hl, by simp [packed_bits_to_dvalue, hp, hi]⟩

theorem packed_bits_to_elts_concat (tb : dtyp_base) (m : Positive) {elts : List dvalue}
    {bitss : List (List memory_bit)} (rest : List memory_bit) :
    List.Forall₂ (fun e b ↦ b.length = m.val ∧ packed_bits_to_dvalue tb m b = e) elts bitss →
    packed_bits_to_elts tb m elts.length (bitss.flatten ++ rest) = elts := by
  intro h
  induction h with
  | nil => rfl
  | @cons e b es bs hb _ ih =>
    obtain ⟨hl, hd⟩ := hb
    simp only [List.length_cons, List.flatten_cons, List.append_assoc, packed_bits_to_elts]
    rw [← hl, List.take_left, List.drop_left, hd, ih]

theorem concat_length_uniform (tb : dtyp_base) (m : Positive) {elts : List dvalue}
    {bitss : List (List memory_bit)} :
    List.Forall₂ (fun e b ↦ b.length = m.val ∧ packed_bits_to_dvalue tb m b = e) elts bitss →
    bitss.flatten.length = elts.length * m.val := by
  intro h
  induction h with
  | nil => simp
  | cons hb _ ih =>
    simp only [List.flatten_cons, List.length_append, hb.1, ih, List.length_cons, Nat.succ_mul]
    omega

theorem get_bits_fwd_all_poison (dbs : List memory_byte) (n : Nat) :
    dbs.all is_all_poison_byte = true → (get_bits_fwd n dbs).all is_poison_bit = true := by
  intro h
  induction dbs generalizing n with
  | nil => exact forallb_poison_bits_repeat n
  | cons b bs ih =>
    simp only [List.all_cons, Bool.and_eq_true] at h
    obtain ⟨hb, hr⟩ := h
    cases b with
    | BYTE_Mixed bits =>
      change bits.all is_poison_bit = true at hb
      simp only [get_bits_fwd, memory_byte_to_memory_bits, dvalue_bv_to_memory_bits]
      split
      · exact forallb_take_pres _ _ _ hb
      · simp [List.all_append, hb, ih _ hr]
    | _ => cases hb

theorem packed_bits_to_elts_poison (tb : dtyp_base) (m : Positive) (n : Nat) (bits : List memory_bit) :
    bits.all is_poison_bit = true → n * m.val ≤ bits.length →
    (packed_bits_to_elts tb m n bits).all dvalue_is_poison = true := by
  intro h hl
  induction n generalizing bits with
  | zero => rfl
  | succ n ih =>
    rw [Nat.succ_mul] at hl
    have hlen := take_length_exact bits m.val (by omega)
    have hn : take m.val bits ≠ [] := by
      intro he; rw [he] at hlen; exact m.property.ne' hlen.symm
    rw [packed_bits_to_elts, packed_bits_to_dvalue_poison _ _ hn (forallb_take_pres _ _ _ h)]
    change (packed_bits_to_elts tb m n (drop m.val bits)).all dvalue_is_poison = true
    exact ih _ (forallb_drop_pres _ _ _ h) (by rw [length_drop_N]; omega)

def packed_fwd (nb : Nat) (bits : List memory_bit) : List memory_byte :=
  bytes_of_bits nb (bits ++ List.replicate (8 * nb - bits.length) (Bit_bit (VInt.repr 0)))

theorem acc_packed_bits_fwd (nb : Nat) (bits : List memory_bit) (acc : List memory_byte) :
    acc_packed_bits_to_memory_bytes nb bits acc = (packed_fwd nb bits).reverse ++ acc := by
  exact acc_bits_to_memory_bytes_fwd _ _ _

theorem packed_round_trip {tb : dtyp_base} {m : Positive} (sz : Nat) {elts : List dvalue}
    {bitss : List (List memory_bit)} :
    (tb = DTYPE_I m ∨ tb = DTYPE_B m) → m.val % 8 ≠ 0 →
    List.Forall (fun e ↦ dvalue_has_dtyp e (DTYPE_Base tb)) elts → elts.length = sz →
    map_monad (packed_elt_bits m) elts = raise_ret bitss →
    let fwd := packed_fwd ((sz * m.val + 7) / 8) bitss.flatten
    List.Forall memory_byte_wf fwd ∧ fwd.length = (sz * m.val + 7) / 8 ∧
      (∀ extra, packed_vector_elts tb m sz (fwd ++ extra) = elts) ∧
      (elts.all dvalue_is_poison = false → fwd.all is_all_poison_byte = false) := by
  intro ht hm hty hlen hbits
  have rel : List.Forall₂ (fun e b ↦ b.length = m.val ∧ packed_bits_to_dvalue tb m b = e) elts bitss := by
    replace hbits := (map_monad_EOU_Forall2 _ _ _).mp hbits
    clear hlen
    induction hbits with
    | nil => exact .nil
    | cons heb _ ih =>
      obtain ⟨he, hs⟩ := (List.forall_cons _ _ _).mp hty
      exact .cons (packed_elt_round_trip ht hm he heb) (ih hs)
  let k := sz * m.val
  let nb := (k + 7) / 8
  let bits := bitss.flatten
  have lb : bits.length = k := (concat_length_uniform tb m rel).trans (by rw [hlen])
  have fit : k ≤ 8 * nb := by dsimp [nb]; omega
  let padded := bits ++ List.replicate (8 * nb - bits.length) (Bit_bit (VInt.repr 0))
  have lp : padded.length = 8 * nb := by simp [padded]; omega
  let fwd := packed_fwd nb bits
  have wf : List.Forall memory_byte_wf fwd := bytes_of_bits_wf nb padded lp.ge
  have lf : fwd.length = nb := bytes_of_bits_length nb padded
  have readBack (extra : List memory_byte) : get_bits_fwd k (fwd ++ extra) = bits := by
    rw [get_bits_fwd_app _ wf (by omega)]
    change take k (((bytes_of_bits nb padded).map memory_byte_to_memory_bits).flatten) = bits
    rw [bytes_of_bits_bits nb padded lp.ge, take_take_le _ _ _ fit]
    exact take_app_exact _ _ _ lb
  have splitBack : packed_bits_to_elts tb m sz bits = elts := by
    simpa only [List.append_nil, hlen] using packed_bits_to_elts_concat tb m [] rel
  refine ⟨wf, lf, ?_, ?_⟩
  · intro extra
    change packed_bits_to_elts tb m sz ((get_bits_of_memory_byte_list k (fwd ++ extra) []).reverseAux []) = elts
    rw [reader_bits_fwd, readBack, splitBack]
  · intro live
    cases ha : fwd.all is_all_poison_byte with
    | false => rfl
    | true =>
      have hp := get_bits_fwd_all_poison fwd k ha
      have hr := readBack []; rw [List.append_nil] at hr
      rw [hr] at hp
      have hall := packed_bits_to_elts_poison tb m sz bits hp lb.ge
      rw [splitBack, live] at hall; contradiction

end Vellvm.Theory.MemoryBytesFacts
