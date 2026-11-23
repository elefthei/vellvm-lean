import PortChecks.SourceType
import Vellvm.Theory.I2F.I2F_exp.BytesPointer

open Vellvm Vellvm.Semantics Vellvm.Semantics.Interfaces.Params Vellvm.Semantics.EOU
open Vellvm.Semantics.MemoryBytes Vellvm.Semantics.DynamicValues Vellvm.Utils.ListUtil
open Vellvm.Theory.I2F.Refinement Vellvm.Syntax.DynamicTypes Vellvm.Numeric.Integers
universe u v
open Vellvm.Semantics.Interfaces.Sizeof
open Vellvm.Theory.I2F.I2F_exp

#source_check "src/rocq/Theory/I2F/I2F_exp.v|Vellvm.Theory.I2F.I2F_exp|I2F_EOUP_fmap_NoPois"
  I2F_EOUP_fmap_NoPois : ∀ {A : Type u} {B : Type v} (R : A → B → Prop) (c : EOU A) (d : EOU B),
    I2F_EOU R c d → I2F_EOUP R ((some <$> c) : EOU (Option A)) ((some <$> d) : EOU (Option B))

#source_check "src/rocq/Theory/I2F/I2F_exp.v|Vellvm.Theory.I2F.I2F_exp|I2F_EOUP_memory_bytes_to_address_ptr"
  I2F_EOUP_memory_bytes_to_address_ptr : ∀ {bs bs'}, List.Forall₂ I2F_memory_byte bs bs' → I2F_EOUP I2F_Addr (@memory_bytes_to_address_ptr PInf  bs) (@memory_bytes_to_address_ptr PFin  bs')

#source_check "src/rocq/Theory/I2F/I2F_exp.v|Vellvm.Theory.I2F.I2F_exp|I2F_EOUP_no_cut_inv"
  I2F_EOUP_no_cut_inv : ∀ {A : Type u} {B : Type v} (R : A → B → Prop) {c : EOUP A} {d : EOUP B},
    I2F_EOUP R c d → no_cut c → no_cut d →
    (∃ a b, c = raise_ret (some a) ∧ d = raise_ret (some b) ∧ R a b) ∨
    (c = raise_ret none ∧ d = raise_ret none) ∨ (∃ s t, c = raise_error s ∧ d = raise_error t)
