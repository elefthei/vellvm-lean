import Vellvm.Theory.I2F.I2F_exp.BytesBasic
import Vellvm.Theory.MemoryBytesFacts.Writer

namespace Vellvm.Theory.I2F.I2F_exp
open Vellvm Vellvm.Semantics Vellvm.Semantics.Interfaces.Params Vellvm.Semantics.EOU
open Vellvm.Semantics.MemoryBytes Vellvm.Semantics.DynamicValues Vellvm.Utils.ListUtil
open Vellvm.Theory.I2F.Refinement Vellvm.Syntax.DynamicTypes Vellvm.Numeric.Integers
universe u

def no_cut : {A : Type u} → EOU A → Prop := fun {_} c ↦ match c with
  | .raise_ub _ | .raise_oom _ => False
  | _ => True

theorem no_cut_ret : ∀ {A : Type u} (a : A), no_cut (raise_ret a) := by intros; trivial

theorem no_cut_bind_EOUP : ∀ {A B : Type u} (c : EOUP A) (k : A → EOUP B),
    no_cut c → (∀ a, no_cut (k a)) → no_cut (c >>= k : EOUP B) := by
  intro A B c k hc hk
  cases c with
  | raise_error => trivial
  | raise_ub | raise_oom => exact hc.elim
  | raise_ret x => cases x with | none => trivial | some a => exact hk a

theorem no_cut_map_monad_EOUP : ∀ {A B : Type u} (f : A → EOUP B),
    (∀ a, no_cut (f a)) → ∀ xs, no_cut (map_monad (m := EOUP) f xs) := by
  intro A B f hf xs
  induction xs with
  | nil => trivial
  | cons a xs ih => exact no_cut_bind_EOUP _ _ (hf a) fun _ ↦ no_cut_bind_EOUP _ _ ih fun _ ↦ True.intro

theorem no_cut_memory_bit_to_bit : ∀ [Pa : Params] b, no_cut (@memory_bit_to_bit Pa b) := by
  intro _ b; cases b <;> trivial

theorem no_cut_memory_bits_to_Z : ∀ [Pa : Params] bits, no_cut (@memory_bits_to_Z Pa bits) := by
  intro _ bits; exact no_cut_bind_EOUP _ _ (no_cut_map_monad_EOUP _ no_cut_memory_bit_to_bit bits) fun _ ↦ True.intro

theorem no_cut_memory_byte_to_Z : ∀ [Pa : Params] b, no_cut (@memory_byte_to_Z Pa b) := by
  intro _ b; cases b <;> first | trivial | apply no_cut_memory_bits_to_Z

theorem no_cut_concat_bytes_Z_mixed : ∀ [Pa : Params] extra bs, no_cut (@concat_bytes_Z_mixed Pa extra bs) := by
  intro _ extra bs
  induction bs with
  | nil => trivial
  | cons b bs ih =>
    cases bs with
    | nil => cases b <;> first | trivial | apply no_cut_memory_bits_to_Z
    | cons c cs =>
      rw [Theory.MemoryBytesFacts.concat_bytes_Z_mixed_cons2]
      apply no_cut_bind_EOUP _ _ (no_cut_memory_byte_to_Z b)
      intro z; exact no_cut_bind_EOUP _ _ ih fun _ ↦ True.intro

theorem no_cut_memory_bytes_to_int : ∀ [Pa : Params] sz bs, no_cut (@memory_bytes_to_int Pa sz bs) := by
  intro _ sz bs
  simp only [memory_bytes_to_int]
  split
  · apply no_cut_concat_bytes_Z_mixed
  · exact no_cut_bind_EOUP _ _ (no_cut_map_monad_EOUP _ no_cut_memory_byte_to_Z bs) fun _ ↦ True.intro

theorem no_cut_valid_pointer_bits : ∀ [Pa : Params] p base bits off, no_cut (@valid_pointer_bits Pa p base off bits) := by
  intro _ p base bits
  induction bits with
  | nil => intro off; trivial
  | cons b bs ih =>
    intro off
    cases b <;> first | trivial | (unfold valid_pointer_bits; split <;> first | trivial | (split <;> first | trivial | apply ih))

theorem no_cut_valid_pointer_byte : ∀ [Pa : Params] p idx b, no_cut (@valid_pointer_byte Pa p idx b) := by
  intro _ p idx b
  cases b with
  | BYTE_I => trivial
  | BYTE_Mixed => apply no_cut_valid_pointer_bits
  | BYTE_Pointer q j => simp only [valid_pointer_byte]; split <;> trivial

theorem no_cut_valid_pointer_bytes : ∀ [Pa : Params] p bs idx, no_cut (@valid_pointer_bytes Pa p idx bs) := by
  intro _ p bs
  induction bs with
  | nil => intro idx; trivial
  | cons b bs ih =>
    intro idx
    apply no_cut_bind_EOUP _ _ (no_cut_valid_pointer_byte p idx b)
    intro v; cases v <;> first | trivial | apply ih

end Vellvm.Theory.I2F.I2F_exp
