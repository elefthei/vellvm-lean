import Vellvm.Theory.MemoryBytesFacts.Digits
import Vellvm.Theory.MemoryBytesFacts.Writer
import Vellvm.Numeric.Floats.BitsFacts
import Mathlib.Tactic.Ring

namespace Vellvm.Theory.MemoryBytesFacts
open Vellvm Vellvm.Numeric Vellvm.Semantics Vellvm.Semantics.EOU
open Vellvm.Semantics.DynamicValues Vellvm.Semantics.MemoryBytes
open Vellvm.Semantics.Interfaces.Params Vellvm.Semantics.Interfaces.Sizeof
open Vellvm.Syntax.DynamicTypes Vellvm.Syntax.LLVMAst Vellvm.Utils.ListUtil

/-- Iptr is unbounded in the infinite-pointer model and need not fit in its store size. -/
def serializable_base : dtyp_base → Prop
  | .DTYPE_I _ | .DTYPE_Pointer | .DTYPE_B _ | .DTYPE_FP .FP_float | .DTYPE_FP .FP_double => True
  | _ => False

def serializable : dtyp → Prop
  | .DTYPE_Base t => serializable_base t
  | .DTYPE_Struct _ ts => ts.foldr (fun t r ↦ serializable t ∧ r) True
  | .DTYPE_Array _ _ t => serializable t

theorem serializable_NO_VOID (dt : dtyp) : serializable dt → NO_VOID dt := by
  induction dt using dtyp_ind with
  | base t => cases t <;> simp [serializable, serializable_base, NO_VOID, NO_VOID_base]
  | struct p ts ih =>
    rw [serializable, NO_VOID]
    simp only [fold_right_forall, List.forall_iff_forall_mem]
    exact fun h t ht ↦ ih t ht (h t ht)
  | array v n t ih => simpa only [serializable, NO_VOID] using ih

variable [Pa : Params]

def base_byte_gen : dvalue_base → Nat → memory_byte := baseByteGen

theorem acc_base_unfold (dtb : dtyp_base) (v : dvalue_base) (off : Nat) (acc : List memory_byte) :
    acc_memory_bytes_of_dvalue_base dtb v off acc = (store_size_dtyp (DTYPE_Base dtb) + off,
      N.rev_loop_acc (base_byte_gen v) (store_size_dtyp (DTYPE_Base dtb)) 0 acc) := rfl

theorem base_block_length (dtb : dtyp_base) (v : dvalue_base) :
    ((Nseq 0 (store_size_dtyp (DTYPE_Base dtb))).map (base_byte_gen v)).length =
      store_size_dtyp (DTYPE_Base dtb) := by simp [Nseq_length]

theorem accumulate_poison_bytes_app (n : Nat) (acc : List memory_byte) :
    accumulate_poison_bytes n acc = List.replicate n poison_memory_byte ++ acc :=
  rev_loop_acc_const _ _ _ _

theorem is_all_poison_memory_byte : is_all_poison_byte poison_memory_byte = true := rfl

theorem poison_split_repeat (k : Nat) :
    poison_split (List.replicate k poison_memory_byte) = (k, []) := by
  induction k with
  | zero => rfl
  | succ k ih => simp [List.replicate_succ, poison_split, is_all_poison_memory_byte, ih, Nat.add_comm]

theorem poison_of_dtyp_base (db : dtyp_base) :
    poison_of_dtyp (DTYPE_Base db) = DVALUE_Base DVALUE_Poison := by
  simp [poison_of_dtyp, dtyp_is_empty]

theorem poison_of_dtyp_nonempty (t : dtyp) (h : dtyp_is_empty t = false) :
    poison_of_dtyp t = DVALUE_Base DVALUE_Poison := by simp [poison_of_dtyp, h]

theorem poison_of_dtyp_empty (t : dtyp) (h : dtyp_is_empty t = true) :
    poison_of_dtyp t = empty_dvalue_of_dtyp t := by simp [poison_of_dtyp, h]

theorem has_dtyp_empty {dt : dtyp} {dv : dvalue} :
    dvalue_has_dtyp dv dt → dtyp_is_empty dt = true → dv = empty_dvalue_of_dtyp dt := by
  induction dt using dtyp_ind generalizing dv with
  | base t => simp [dtyp_is_empty]
  | struct p ts ih =>
    intro h he
    cases h with
    | DVALUE_Poison_typ_agg => simp_all
    | DVALUE_Struct_typ =>
      rename_i hf hn
      clear hn
      simp only [empty_dvalue_of_dtyp, dvalue.DVALUE_Struct.injEq, true_and]
      rw [dtyp_is_empty, List.all_eq_true] at he
      induction hf with
      | nil => rfl
      | cons h _ rest =>
        simp only [List.map_cons, List.cons.injEq]
        exact ⟨ih _ (by simp) h (he _ (by simp)),
          rest (fun t ht ↦ ih t (.tail _ ht)) (fun t ht ↦ he t (.tail _ ht))⟩
  | array v n t ih =>
    intro h he
    cases h with
    | DVALUE_Poison_typ_agg => simp_all
    | DVALUE_Array_typ =>
      rename_i hl _ hf _
      rw [empty_dvalue_of_dtyp]
      congr 1
      refine List.eq_replicate_iff.mpr ⟨hl, fun x hx ↦ ih (hf x hx) ?_⟩
      have := List.length_pos_of_mem hx
      simpa [dtyp_is_empty, show n ≠ 0 by omega] using he

theorem struct_canonical_cases {p fs ts}
    (h : dvalue_has_dtyp (DVALUE_Struct p fs) (DTYPE_Struct p ts)) :
    DVALUE_Struct p fs = poison_of_dtyp (DTYPE_Struct p ts) ∨ fields_all_poison ts fs = false := by
  cases he : dtyp_is_empty (DTYPE_Struct p ts) with
  | true => exact .inl ((has_dtyp_empty h he).trans (poison_of_dtyp_empty _ he).symm)
  | false =>
    cases h
    right
    rename_i hn
    change (!dtyp_is_empty (DTYPE_Struct p ts) && fields_all_poison ts fs) = false at hn
    rw [he] at hn
    exact hn

theorem array_canonical_cases {v xs n t}
    (h : dvalue_has_dtyp (DVALUE_Array v xs) (DTYPE_Array v n t)) :
    DVALUE_Array v xs = poison_of_dtyp (DTYPE_Array v n t) ∨
      (dtyp_is_empty t = false ∧ xs.all dvalue_is_poison = false) := by
  cases he : dtyp_is_empty (DTYPE_Array v n t) with
  | true => exact .inl ((has_dtyp_empty h he).trans (poison_of_dtyp_empty _ he).symm)
  | false =>
    cases h with
    | DVALUE_Array_typ =>
      rename_i hn
      change (!dtyp_is_empty (DTYPE_Array v n t) && xs.all dvalue_is_poison) = false at hn
      rw [he] at hn
      exact .inr ⟨by cases ht : dtyp_is_empty t <;> simp_all [dtyp_is_empty], hn⟩

theorem agg_is_poison_nonempty (dt : dtyp) (vs : List dvalue) (h : agg_is_poison dt vs = true) :
    dtyp_is_empty dt = false := by
  simpa using (Bool.and_eq_true_iff.mp h).1

theorem empty_dvalue_has_dtyp (dt : dtyp) :
    NO_VOID dt → dtyp_is_empty dt = true → dvalue_has_dtyp (empty_dvalue_of_dtyp dt) dt := by
  induction dt using dtyp_ind with
  | base t => simp [dtyp_is_empty]
  | struct p ts ih =>
    intro hn he
    rw [empty_dvalue_of_dtyp]
    constructor
    · simp [agg_is_poison, he]
    · apply List.forall₂_map_left_iff.mpr
      apply List.forall₂_same.mpr
      intro t ht
      exact ih t ht (NO_VOID_Struct_fields p ts hn t ht)
        (List.all_eq_true.mp (by simpa only [dtyp_is_empty] using he) t ht)
  | array v n t ih =>
    intro hn he
    rw [empty_dvalue_of_dtyp]
    constructor
    · simpa only [NO_VOID] using hn
    · simp [agg_is_poison, he]
    · cases n with
      | zero => simp
      | succ n =>
        intro x hx
        have hx' := List.eq_of_mem_replicate hx
        subst x
        exact ih (by simpa only [NO_VOID] using hn) (by simpa [dtyp_is_empty] using he)
    · simp

theorem poison_of_dtyp_has_dtyp (t : dtyp) (hn : NO_VOID t) : dvalue_has_dtyp (poison_of_dtyp t) t := by
  cases he : dtyp_is_empty t with
  | false => rw [poison_of_dtyp_nonempty t he]; exact .DVALUE_Poison_typ_agg (t := t) he
  | true => rw [poison_of_dtyp_empty t he]; exact empty_dvalue_has_dtyp t hn he

def dvalue_poison_of_dtyp_dec (v : dvalue) (t : dtyp) : Decidable (v = poison_of_dtyp t) :=
  dvalue_eq_dec v (poison_of_dtyp t)

theorem read_repeat_poison_agg (dt : dtyp) (k : Nat)
    (ha : match dt with | .DTYPE_Base _ => False | _ => True) :
    memory_bytes_to_dvalue (List.replicate k poison_memory_byte) dt = raise_ret (poison_of_dtyp dt) := by
  cases dt <;> first | contradiction | simp only [memory_bytes_to_dvalue, poison_split_repeat]; rfl

theorem serializable_base_pos (t : dtyp_base) (h : serializable_base t) :
    0 < store_size_dtyp (DTYPE_Base t) := by
  cases t <;> try contradiction
  case DTYPE_I sz => rw [store_size_dtyp_int]; have := sz.property; omega
  case DTYPE_B sz => rw [store_size_dtyp_bytes]; have := sz.property; omega
  case DTYPE_Pointer => exact store_size_dtyp_ptr_pos
  case DTYPE_FP fp => cases fp <;> first | contradiction | rw [store_size_dtyp_float]; decide | rw [store_size_dtyp_double]; decide

theorem memory_byte_to_Z_poison : memory_byte_to_Z poison_memory_byte = raise_ret Pois := rfl

theorem memory_bits_to_Z_poison_cons (rest : List memory_bit) :
    memory_bits_to_Z (Bit_psn :: rest) = raise_ret Pois := rfl

theorem map_monad_byte_to_Z_poison {k : Nat} (h : 0 < k) :
    map_monad (m := EOUP) memory_byte_to_Z (List.replicate k poison_memory_byte) = raise_ret Pois := by
  cases k with
  | zero => omega
  | succ k => rw [List.replicate_succ]; exact map_monad_EOUP_pois_head _ _ _ memory_byte_to_Z_poison

theorem concat_bytes_Z_mixed_poison {extra k : Nat} (he : 0 < extra) (hk : 0 < k) :
    concat_bytes_Z_mixed extra (List.replicate k poison_memory_byte) = raise_ret Pois := by
  cases k with
  | zero => omega
  | succ k =>
    cases k with
    | zero => cases extra <;> first | omega | rfl
    | succ k => rw [List.replicate_succ, List.replicate_succ]; rfl

theorem memory_bytes_to_int_poison (sz : Positive) {k : Nat} (hk : 0 < k) :
    memory_bytes_to_int sz (List.replicate k poison_memory_byte) = raise_ret Pois := by
  by_cases he : sz.val % 8 = 0
  · simp only [memory_bytes_to_int, he, ne_eq, bne_self_eq_false, Bool.false_eq_true, if_false,
      map_monad_byte_to_Z_poison hk]; rfl
  · simpa [memory_bytes_to_int, he] using (concat_bytes_Z_mixed_poison (Nat.pos_of_ne_zero he) hk)

theorem memory_bytes_to_pointer_poison {k : Nat} (hk : 0 < k) :
    memory_bytes_to_pointer (List.replicate k poison_memory_byte) = raise_ret Pois := by
  cases k with
  | zero => omega
  | succ k => rw [List.replicate_succ]; rfl

theorem all_poison_bytes_repeat (k : Nat) : all_poison_bytes (List.replicate k poison_memory_byte) = true := by
  rw [all_poison_bytes, poison_split_repeat]; rfl

theorem read_base_block_poison (t : dtyp_base) (hs : serializable_base t) :
    memory_bytes_to_dvalue_base (List.replicate (store_size_dtyp (DTYPE_Base t)) poison_memory_byte) t =
      raise_ret DVALUE_Poison := by
  have hk := serializable_base_pos t hs
  cases t <;> try contradiction
  case DTYPE_FP fp =>
    cases fp <;> first | contradiction | rw [memory_bytes_to_dvalue_base, map_monad_byte_to_Z_poison hk]; rfl
  all_goals first
    | rw [memory_bytes_to_dvalue_base, memory_bytes_to_pointer_poison hk]; rfl
    | rw [memory_bytes_to_dvalue_base, memory_bytes_to_int_poison _ hk]; rfl
    | simp only [memory_bytes_to_dvalue_base, all_poison_bytes_repeat, if_true]; rfl

private theorem valid_self (p : Pa.PTR.ptr) (i : Nat) :
    valid_pointer_byte p i (BYTE_Pointer p i) = raise_ret (some true) := by
  rw [valid_pointer_byte]
  split <;> first | contradiction | simp only [beq_self_eq_true]; rfl

theorem valid_pointer_bytes_run (p : Pa.PTR.ptr) (n i : Nat) :
    valid_pointer_bytes p i ((Nseq i n).map (fun j ↦ BYTE_Pointer p j)) =
      (pure (i+n == store_size_dtyp DTYPE_Pointer) : EOUP Bool) := by
  induction n generalizing i with
  | zero => rfl
  | succ n ih =>
    simp only [Nseq, List.map_cons, valid_pointer_bytes, valid_self]
    change valid_pointer_bytes p (1+i) _ = _
    rw [Nat.add_comm 1 i, ih, show i+1+n = i+(n+1) by omega]

theorem memory_bytes_to_pointer_run (p : Pa.PTR.ptr) {n : Nat} (hp : 0 < n)
    (hs : n = store_size_dtyp DTYPE_Pointer) :
    memory_bytes_to_pointer ((Nseq 0 n).map (fun j ↦ BYTE_Pointer p j)) = raise_ret (some p) := by
  cases n with
  | zero => omega
  | succ n =>
    change (valid_pointer_bytes p 0 ((Nseq 0 (n+1)).map (fun j ↦ BYTE_Pointer p j)) >>=
      fun b ↦ if b then pure p else memory_bytes_to_address_ptr _) = _
    rw [valid_pointer_bytes_run, Nat.zero_add, hs, beq_self_eq_true]; rfl

theorem read_base_block_pointer (p : Pa.PTR.ptr) :
    memory_bytes_to_dvalue_base ((Nseq 0 (store_size_dtyp DTYPE_Pointer)).map
      (base_byte_gen (DVALUE_Pointer p))) DTYPE_Pointer = raise_ret (DVALUE_Pointer p) := by
  simp only [base_byte_gen, baseByteGen, memory_bytes_to_dvalue_base,
    memory_bytes_to_pointer_run p store_size_dtyp_ptr_pos rfl]; rfl

theorem map_monad_byte_to_Z_BYTE_I (f : Nat → VellvmIntegers.int8) (l : List Nat) :
    map_monad (m := EOUP) memory_byte_to_Z (l.map (fun i ↦ BYTE_I (f i))) =
      raise_ret (some (l.map (fun i ↦ Integers.unsigned (f i)))) := by
  induction l with
  | nil => rfl
  | cons a l ih => rw [List.map_cons, map_monad, ih]; rfl

theorem gen_plain {sz : Positive} (x : Integers.bit_int sz) (i : Nat) :
    memory_byte_of_dvalue_bv (BYTE_I x) i = BYTE_I (Integers.repr (extract_byte_vint x i)) := rfl

private abbrev digit {sz : Positive} (x : Integers.bit_int sz) (i : Nat) : VellvmIntegers.int8 :=
  Integers.repr (extract_byte_vint x i)

private theorem unsigned_byte_mod (v : Int) :
    Integers.unsigned (Integers.repr (v % 256) : VellvmIntegers.int8) = v % 256 := by
  apply Integers.unsigned_repr
  change 0 ≤ v % 256 ∧ v % 256 ≤ 255
  omega

private theorem low_digits {sz : Positive} (x : Integers.bit_int sz) (n : Nat) (hn : 8*n ≤ sz.val) :
    concat_bytes_Z ((Nseq 0 n).map (fun i ↦ Integers.unsigned (digit x i))) =
      Integers.unsigned x % 2^(8*n) := by
  have hmap : (Nseq 0 n).map (fun i ↦ Integers.unsigned (digit x i)) =
      (Nseq 0 n).map (fun i ↦ Integers.unsigned x / 2^(8*i) % 256) := by
    apply List.map_congr_left; intro i hi
    have hb := (In_Nseq n 0 i hi).2
    rw [digit, extract_byte_vint_spec_lt x i (by omega), unsigned_byte_mod]
  rw [hmap, concat_bytes_Z_extract]; simp

private theorem word_bound {sz : Positive} (x : Integers.bit_int sz) :
    0 ≤ Integers.unsigned x ∧ Integers.unsigned x < 2^sz.val := by
  have h := Integers.unsigned_range x
  have hm : @Integers.modulus sz = ((2^sz.val : Nat) : Int) := Integers.modulus_def
  simpa [hm] using h

theorem read_int_block_mult8 {sz : Positive} (x : Integers.bit_int sz) (he : sz.val % 8 = 0) :
    memory_bytes_to_dvalue_base ((Nseq 0 (store_size_dtyp (DTYPE_I sz))).map
      (memory_byte_of_dvalue_bv (BYTE_I x))) (DTYPE_I sz) = raise_ret (DVALUE_I sz x) := by
  have hl := store_size_int_mult8 sz he
  let n := store_size_dtyp (DTYPE_I sz)
  have hz : memory_bytes_to_int sz ((Nseq 0 n).map (fun i ↦ BYTE_I (digit x i))) =
      raise_ret (some (Integers.unsigned x)) := by
    simp only [memory_bytes_to_int, he, bne_self_eq_false, Bool.false_eq_true, if_false,
      map_monad_byte_to_Z_BYTE_I]
    change raise_ret (some (concat_bytes_Z _)) = _
    rw [low_digits x n hl.le, hl, Int.emod_eq_of_lt (word_bound x).1 (word_bound x).2]
  rw [memory_bytes_to_dvalue_base]
  change absorb_pois (memory_bytes_to_int sz ((Nseq 0 n).map (fun i ↦ BYTE_I (digit x i)))) _ = _
  rw [hz]; change raise_ret (DVALUE_I sz (Integers.repr (Integers.unsigned x))) = _
  rw [Integers.repr_unsigned]

theorem memory_bits_to_Z_of_bits (zs : List Int) : memory_bits_to_Z (zs.map Z_to_memory_bit) =
    raise_ret (some (concat_bits_Z (zs.map (fun z ↦ z % 2)))) := by
  have H : map_monad (m := EOUP) memory_bit_to_bit (zs.map Z_to_memory_bit) =
      raise_ret (some (zs.map (fun z ↦ z % 2))) := by
    induction zs with
    | nil => rfl
    | cons z zs ih =>
      rw [List.map_cons, map_monad_cons_EOUP, ih]
      change raise_ret (some (Integers.unsigned (Integers.repr z : VellvmIntegers.int1) :: _)) = _
      rw [Integers.unsigned_repr_eq, Int.fmod_eq_emod_of_nonneg _ (by decide)]; rfl
  rw [memory_bits_to_Z, H]; rfl

private theorem shift_byte (z : Int) : z <<< 8 = 256*z :=
  (Int.shiftLeft_eq_mul_pow z 8).trans (Int.mul_comm _ _)

theorem concat_bytes_Z_mixed_cons_app (e : Nat) (b : memory_byte) (ys : List VellvmIntegers.int8)
    (lastb : memory_byte) : concat_bytes_Z_mixed e (b :: (ys.map BYTE_I ++ [lastb])) = (do
      let z ← memory_byte_to_Z b
      let r ← concat_bytes_Z_mixed e (ys.map BYTE_I ++ [lastb])
      pure (z + (r <<< 8)) : EOUP Int) := by
  simp only [shift_byte]
  cases ys <;> apply concat_bytes_Z_mixed_cons2

theorem concat_bytes_Z_mixed_app_ret (e : Nat) (ys : List VellvmIntegers.int8) (lastb : memory_byte)
    (v : Int) (hv : concat_bytes_Z_mixed e [lastb] = raise_ret (some v)) :
    concat_bytes_Z_mixed e (ys.map BYTE_I ++ [lastb]) =
      raise_ret (some (concat_bytes_Z (ys.map Integers.unsigned) + v * 2^(8*ys.length))) := by
  induction ys with
  | nil => simpa [concat_bytes_Z] using hv
  | cons y ys ih =>
    simp only [List.map_cons, List.cons_append, concat_bytes_Z_mixed_cons_app, ih,
      concat_bytes_Z, List.length_cons]
    change raise_ret (some (Integers.unsigned y + ((_ + v * 2^(8*ys.length)) <<< 8))) = _
    simp only [shift_byte, Nat.mul_succ, Int.pow_add]
    congr 2; ring

theorem read_int_block_mixed {sz : Positive} (x : Integers.bit_int sz) (he : sz.val % 8 ≠ 0) :
    memory_bytes_to_dvalue_base ((Nseq 0 (store_size_dtyp (DTYPE_I sz))).map
      (memory_byte_of_dvalue_bv (BYTE_I x))) (DTYPE_I sz) = raise_ret (DVALUE_I sz x) := by
  let e := sz.val % 8
  obtain ⟨hpos, hsize⟩ := store_size_int_mixed sz he
  obtain ⟨m, hm⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : store_size_dtyp (DTYPE_I sz) ≠ 0)
  have hw : 8*m + e = sz.val := by dsimp [e]; omega
  let z := Integers.unsigned x
  have hq₀ : 0 ≤ z / 2^(8*m) := Int.ediv_nonneg (word_bound x).1 (by positivity)
  have hq : z / 2^(8*m) < 2^e := by
    apply (Int.ediv_lt_iff_lt_mul (by positivity)).mpr
    rw [← Int.pow_add, Nat.add_comm e, hw]; exact (word_bound x).2
  have h8 : (2:Int)^e ≤ 256 := by
    change (2:Int)^e ≤ 2^8
    exact pow_le_pow_right₀ (by decide) (by dsimp [e]; omega)
  have hlast : concat_bytes_Z_mixed e [BYTE_I (digit x m)] = raise_ret (some (z / 2^(8*m))) := by
    change raise_ret (some (Integers.unsigned (digit x m) % 2^e)) = _
    rw [digit, extract_byte_vint_spec_lt x m (by dsimp [e] at hw; omega), unsigned_byte_mod]
    change raise_ret (some ((z / 2^(8*m) % 256) % 2^e)) = _
    rw [Int.emod_eq_of_lt hq₀ (lt_of_lt_of_le hq h8), Int.emod_eq_of_lt hq₀ hq]
  have hz : memory_bytes_to_int sz ((Nseq 0 (m+1)).map (fun i ↦ BYTE_I (digit x i))) =
      raise_ret (some z) := by
    simp only [memory_bytes_to_int, bne_iff_ne.mpr he, if_true]
    rw [Nseq_snoc, List.map_append]; simp only [Nat.zero_add, List.map_cons, List.map_nil]
    change concat_bytes_Z_mixed e _ = _
    have hmap : (Nseq 0 m).map (fun i ↦ (BYTE_I (digit x i) : memory_byte)) =
        ((Nseq 0 m).map (digit x)).map BYTE_I := by rw [List.map_map]; rfl
    rw [hmap, concat_bytes_Z_mixed_app_ret _ _ _ _ hlast]
    simp only [List.length_map, Nseq_length, List.map_map, Function.comp_def]
    rw [low_digits x m (by omega)]; exact congrArg (fun r ↦ raise_ret (some r)) (Int.emod_add_ediv_mul z _)
  rw [memory_bytes_to_dvalue_base, hm]
  change absorb_pois (memory_bytes_to_int sz ((Nseq 0 (m+1)).map (fun i ↦ BYTE_I (digit x i)))) _ = _
  rw [hz]; change raise_ret (DVALUE_I sz (Integers.repr z)) = _
  rw [Integers.repr_unsigned]

private theorem float_word {w : Positive} (x : Integers.bit_int w) (n : Nat)
    (hw : 8*n = w.val) (hm : 8 < @Integers.modulus w) :
    (concat_bytes_Z_vint ((Nseq 0 n).map (fun i ↦ Integers.unsigned
      (Integers.repr (extract_byte_Z (Integers.unsigned x) i) : VellvmIntegers.int8))) : Integers.bit_int w) = x := by
  change concat_bytes_vint (List.map (@Integers.repr w) _) = _
  rw [concat_bytes_vint_Z _ _ hm]
  simp only [extract_byte_Z_spec, unsigned_byte_mod, concat_bytes_Z_extract, Nat.mul_zero, pow_zero,
    Int.ediv_one, hw, Int.emod_eq_of_lt (word_bound x).1 (word_bound x).2, Integers.repr_unsigned]

theorem read_base_block_double (d : ll_double) : memory_bytes_to_dvalue_base
    ((Nseq 0 (store_size_dtyp (DTYPE_FP FP_double))).map (base_byte_gen (DVALUE_Double d)))
      (DTYPE_FP FP_double) = raise_ret (DVALUE_Double d) := by
  rw [store_size_dtyp_double, memory_bytes_to_dvalue_base]
  simp only [base_byte_gen, baseByteGen, map_monad_byte_to_Z_BYTE_I]
  change raise_ret (DVALUE_Double (Floats.Float.of_bits (concat_bytes_Z_vint _))) = _
  rw [float_word (Floats.Float.to_bits d) 8 rfl (by decide), Floats.Float.of_to_bits]

theorem read_base_block_float (f : ll_float) : memory_bytes_to_dvalue_base
    ((Nseq 0 (store_size_dtyp (DTYPE_FP FP_float))).map (base_byte_gen (DVALUE_Float f)))
      (DTYPE_FP FP_float) = raise_ret (DVALUE_Float f) := by
  rw [store_size_dtyp_float, memory_bytes_to_dvalue_base]
  simp only [base_byte_gen, baseByteGen, map_monad_byte_to_Z_BYTE_I]
  change raise_ret (DVALUE_Float (Floats.Float32.of_bits (concat_bytes_Z_vint _))) = _
  rw [float_word (Floats.Float32.to_bits f) 4 rfl (by decide), Floats.Float32.of_to_bits]

theorem memory_bytes_to_int_of_read {sz : Positive} {x : Integers.bit_int sz} (dbs : List memory_byte)
    (h : memory_bytes_to_dvalue_base dbs (DTYPE_I sz) = raise_ret (DVALUE_I sz x)) :
    ∃ v, memory_bytes_to_int sz dbs = raise_ret (some v) ∧ Integers.repr v = x := by
  rw [memory_bytes_to_dvalue_base, absorb_pois, catch_pois] at h
  cases e : memory_bytes_to_int sz dbs with
  | raise_error | raise_ub | raise_oom => simp [e, EOU.bind] at h
  | raise_ret r =>
    cases r with
    | none => simp [e, EOU.bind] at h
    | some z =>
      simp only [e, EOU.bind] at h
      change raise_ret (DVALUE_I sz (Integers.repr z)) = raise_ret (DVALUE_I sz x) at h
      exact ⟨z, rfl, by simpa using h⟩

theorem pointer_slice_from_run (p : Pa.PTR.ptr) (n i : Nat) :
    pointer_slice_from p i ((Nseq i n).map (fun j ↦ BYTE_Pointer p j)) = true := by
  induction n generalizing i with
  | zero => rfl
  | succ n ih => simp [Nseq, pointer_slice_from, pointer_byte_at, valid_self, Nat.add_comm 1 i, ih]

theorem BYTE_I_byte0 {sz : Positive} (x : Integers.bit_int sz) :
    memory_byte_of_dvalue_bv (BYTE_I x) 0 = BYTE_I (Integers.repr (extract_byte_vint x 0)) ∨
    ∃ b bs, memory_byte_of_dvalue_bv (BYTE_I x) 0 = BYTE_Mixed (Bit_bit b :: bs) := .inl rfl

theorem all_poison_BYTE_I_block {sz : Positive} (x : Integers.bit_int sz) {k : Nat} (hk : 0 < k) :
    all_poison_bytes ((Nseq 0 k).map (memory_byte_of_dvalue_bv (BYTE_I x))) = false := by
  cases k <;> first | omega | rfl

theorem pointer_slice_BYTE_I_block {sz : Positive} (x : Integers.bit_int sz) {k : Nat} (hk : 0 < k) :
    memory_bytes_to_pointer_slice ((Nseq 0 k).map (memory_byte_of_dvalue_bv (BYTE_I x))) = none := by
  cases k <;> first | omega | rfl

private theorem bit_origin (dbs : List memory_byte) (n : Nat) (acc : List memory_bit) (b : memory_bit)
    (h : b ∈ get_bits_of_memory_byte_list n dbs acc) :
    b ∈ acc ∨ (8*dbs.length < n ∧ b = Bit_psn) ∨ ∃ d ∈ dbs, b ∈ memory_byte_to_memory_bits d := by
  induction dbs generalizing acc n with
  | nil =>
    cases n with
    | zero => exact .inl h
    | succ n =>
      rw [get_bits_of_memory_byte_list, rev_loop_acc_const] at h
      simp only [beq_iff_eq, Nat.succ_ne_zero, if_false, List.mem_append] at h
      rcases h with hp | ha
      · exact .inr (.inl ⟨Nat.zero_lt_succ _, List.eq_of_mem_replicate hp⟩)
      · exact .inl ha
  | cons d ds ih =>
    rw [get_bits_of_memory_byte_list] at h
    split at h
    · simp only [List.reverseAux_eq, List.mem_append, List.mem_reverse] at h
      exact h.elim (fun hb ↦ .inr (.inr ⟨d, .head _, List.mem_of_mem_take hb⟩)) Or.inl
    · rcases ih _ _ h with ha | ⟨hlt, rfl⟩ | ⟨d', hd', hb⟩
      · simp only [List.reverseAux_eq, List.mem_append, List.mem_reverse] at ha
        exact ha.elim (fun hb ↦ .inr (.inr ⟨d, .head _, hb⟩)) Or.inl
      · exact .inr (.inl ⟨by simp only [List.length_cons]; omega, rfl⟩)
      · exact .inr (.inr ⟨d', .tail _ hd', hb⟩)

theorem In_get_bits (dbs : List memory_byte) (n : Nat) (acc : List memory_bit) (b : memory_bit)
    (h : b ∈ get_bits_of_memory_byte_list n dbs acc) :
    b ∈ acc ∨ b = Bit_psn ∨ ∃ d ∈ dbs, b ∈ memory_byte_to_memory_bits d :=
  (bit_origin dbs n acc b h).imp_right (Or.imp_left And.right)

theorem In_get_bits_full (dbs : List memory_byte) {n : Nat} (acc : List memory_bit) (b : memory_bit)
    (hn : n ≤ 8*dbs.length) (h : b ∈ get_bits_of_memory_byte_list n dbs acc) :
    b ∈ acc ∨ ∃ d ∈ dbs, b ∈ memory_byte_to_memory_bits d :=
  (bit_origin dbs n acc b h).imp_right fun h' ↦ h'.resolve_left fun hp ↦ (not_lt.mpr hn) hp.1

private theorem int_byte_bit {sz : Positive} {x : Integers.bit_int sz} {i : Nat} {b : memory_bit}
    (h : b ∈ memory_byte_to_memory_bits (memory_byte_of_dvalue_bv (BYTE_I x) i)) :
    ∃ v, b = Bit_bit v := by
  simp only [memory_byte_of_dvalue_bv, memory_byte_to_memory_bits, dvalue_bv_to_memory_bits,
    memory_bits_from] at h
  rcases In_rev_loop_acc _ _ _ _ _ (List.mem_reverse.mp h) with h | ⟨j, hj⟩
  · cases h
  · exact ⟨_, hj⟩

theorem BYTE_I_byte_no_ptr {sz : Positive} {x : Integers.bit_int sz} {i : Nat} {b : memory_bit}
    (h : b ∈ memory_byte_to_memory_bits (memory_byte_of_dvalue_bv (BYTE_I x) i)) :
    is_ptr_bit b = false := by obtain ⟨_, rfl⟩ := int_byte_bit h; rfl

theorem no_ptr_bits_BYTE_I_block {sz : Positive} (x : Integers.bit_int sz) (k : Nat) :
    ((get_bits_of_memory_byte_list sz.val ((Nseq 0 k).map (memory_byte_of_dvalue_bv (BYTE_I x))) []).reverseAux []).any is_ptr_bit = false := by
  apply List.any_eq_false.mpr; intro b hb
  simp only [List.reverseAux_eq, List.append_nil, List.mem_reverse] at hb
  rcases In_get_bits _ _ _ _ hb with h | rfl | ⟨d, hd, hb⟩
  · cases h
  · simp [is_ptr_bit]
  · obtain ⟨i, _, rfl⟩ := List.mem_map.mp hd
    simp [BYTE_I_byte_no_ptr hb]

theorem BYTE_I_byte_no_psn {sz : Positive} {x : Integers.bit_int sz} {i : Nat} {b : memory_bit}
    (h : b ∈ memory_byte_to_memory_bits (memory_byte_of_dvalue_bv (BYTE_I x) i)) :
    is_poison_bit b = false := by obtain ⟨_, rfl⟩ := int_byte_bit h; rfl

theorem no_psn_bits_BYTE_I_block {sz : Positive} (x : Integers.bit_int sz) (k : Nat) (hk : sz.val ≤ 8*k) :
    ((get_bits_of_memory_byte_list sz.val ((Nseq 0 k).map (memory_byte_of_dvalue_bv (BYTE_I x))) []).reverseAux []).any is_poison_bit = false := by
  apply List.any_eq_false.mpr; intro b hb
  simp only [List.reverseAux_eq, List.append_nil, List.mem_reverse] at hb
  rcases In_get_bits_full _ _ _ (by simpa [Nseq_length] using hk) hb with h | ⟨d, hd, hb⟩
  · cases h
  · obtain ⟨i, _, rfl⟩ := List.mem_map.mp hd
    simp [BYTE_I_byte_no_psn hb]

theorem not_all_int_no_ptr_pois (bs : List memory_bit) :
    (!bs.all is_int_bit) = true → bs.any is_ptr_bit = false → bs.any is_poison_bit = true := by
  induction bs with
  | nil => simp
  | cons b bs ih =>
    cases b <;> first | exact ih | simp [List.all_cons, List.any_cons, is_int_bit, is_ptr_bit, is_poison_bit]

theorem read_base_block_BYTE_I {sz : Positive} (x : Integers.bit_int sz) : memory_bytes_to_dvalue_base
    ((Nseq 0 (store_size_dtyp (DTYPE_B sz))).map (memory_byte_of_dvalue_bv (BYTE_I x))) (DTYPE_B sz) =
      raise_ret (DVALUE_B sz (BYTE_I x)) := by
  rw [store_size_B_I]
  have hk := serializable_base_pos (DTYPE_I sz) trivial
  have hi := if he : sz.val % 8 = 0 then read_int_block_mult8 x he else read_int_block_mixed x he
  obtain ⟨v, hv, rfl⟩ := memory_bytes_to_int_of_read _ hi
  simp only [memory_bytes_to_dvalue_base, all_poison_BYTE_I_block _ hk, Bool.false_eq_true, if_false,
    memory_bytes_to_byte_value, pointer_slice_BYTE_I_block _ hk, memory_bytes_to_bits_value,
    List.reverse, no_ptr_bits_BYTE_I_block, no_psn_bits_BYTE_I_block _ _ (store_size_int_bits sz),
    Bool.false_or, hv]; rfl

theorem all_poison_pointer_run (p : Pa.PTR.ptr) (i n : Nat) :
    all_poison_bytes ((Nseq i (n+1)).map (fun j ↦ BYTE_Pointer p j)) = false := rfl

theorem memory_bytes_to_pointer_slice_run (p : Pa.PTR.ptr) (i n : Nat) :
    memory_bytes_to_pointer_slice ((Nseq i (n+1)).map (fun j ↦ BYTE_Pointer p j)) = some (p,i) := by
  change (if pointer_slice_from p i ((Nseq i (n+1)).map (fun j ↦ BYTE_Pointer p j)) then _ else _) = _
  simp [pointer_slice_from_run]

theorem read_base_block_BYTE_Pointer (sz : Positive) (p : Pa.PTR.ptr) (k : Nat) (he : sz.val % 8 = 0) :
    memory_bytes_to_dvalue_base ((Nseq 0 (store_size_dtyp (DTYPE_B sz))).map
      (memory_byte_of_dvalue_bv (BYTE_Pointer (bit_sz := sz) p k))) (DTYPE_B sz) =
        raise_ret (DVALUE_B sz (BYTE_Pointer p k)) := by
  have hp := serializable_base_pos (DTYPE_B sz) trivial
  obtain ⟨n, hn⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : store_size_dtyp (DTYPE_B sz) ≠ 0)
  let start := sz.val*k/8
  have hstart : start*8 = sz.val*k := Nat.div_mul_cancel (Nat.dvd_mul_right_of_dvd (Nat.dvd_of_mod_eq_zero he) k)
  have ha : pointer_chunk_aligned sz start = true := by simp [pointer_chunk_aligned, he, hstart]
  have hk : start*8/sz.val = k := by rw [hstart, Nat.mul_div_right _ sz.property]
  rw [hn]
  change memory_bytes_to_dvalue_base ((Nseq 0 (n+1)).map (fun i ↦ BYTE_Pointer p (start+i))) _ = _
  rw [map_Nseq_shift (fun i ↦ (BYTE_Pointer p i : memory_byte)), Nat.add_zero]
  simp only [memory_bytes_to_dvalue_base, all_poison_pointer_run, Bool.false_eq_true, if_false,
    memory_bytes_to_byte_value, memory_bytes_to_pointer_slice_run, ha, if_true, hk]; rfl

end Vellvm.Theory.MemoryBytesFacts
