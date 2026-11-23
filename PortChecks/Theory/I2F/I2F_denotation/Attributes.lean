import PortChecks.SourceType
import Vellvm.Theory.I2F.I2F_denotation.Attributes

open Vellvm Vellvm.Syntax.DynamicTypes Vellvm.Syntax.LLVMAst Vellvm.Semantics.DynamicValues
open Vellvm.Semantics.Attributes Vellvm.Semantics.LLVMEvents Vellvm.Tree
open Vellvm.Theory.I2F.Refinement Vellvm.Theory.I2F.I2F_denotation

namespace PortChecks.I2FDenotationAttributes

private abbrev InfCheck := assume_bundle_check (Pa := PInf) (E := @CFGEtop PInf) (B := NoChoice)
private abbrev FinCheck := assume_bundle_check (Pa := PFin) (E := @CFGEtop PFin) (B := NoChoice)

#source_check "src/rocq/Theory/I2F/I2F_denotation.v|Vellvm.Theory.I2F.I2F_denotation|I2F_assert_dereferenceable"
  I2F_assert_dereferenceable : ∀ (or_null : Bool) (n : Nat) {v1 : @dvalue PInf} {v2 : @dvalue PFin}
    (msg : IRString), I2F_dvalue v1 v2 → I2F_refine_CFG (fun _ _ ↦ True)
      (assert_dereferenceable (Pa := PInf) or_null n v1 msg)
      (assert_dereferenceable (Pa := PFin) or_null n v2 msg)

#source_check "src/rocq/Theory/I2F/I2F_denotation.v|Vellvm.Theory.I2F.I2F_denotation|I2F_assert_attrs_dereferenceable"
  I2F_assert_attrs_dereferenceable : ∀ (attrs : List param_attr) {v1 : @dvalue PInf} {v2 : @dvalue PFin}
    (msg : IRString), I2F_dvalue v1 v2 → I2F_refine_CFG (fun _ _ ↦ True)
      (assert_attrs_dereferenceable (Pa := PInf) attrs v1 msg)
      (assert_attrs_dereferenceable (Pa := PFin) attrs v2 msg)

#source_check "src/rocq/Theory/I2F/I2F_denotation.v|Vellvm.Theory.I2F.I2F_denotation|I2F_assert_load_dereferenceable"
  I2F_assert_load_dereferenceable : ∀ (md : List (metadata dtyp)) {v1 : @dvalue PInf} {v2 : @dvalue PFin}
    (msg : IRString), I2F_dvalue v1 v2 → I2F_refine_CFG (fun _ _ ↦ True)
      (assert_load_dereferenceable (Pa := PInf) md v1 msg)
      (assert_load_dereferenceable (Pa := PFin) md v2 msg)

#source_check "src/rocq/Theory/I2F/I2F_denotation.v|Vellvm.Theory.I2F.I2F_denotation|I2F_apply_attrs"
  I2F_apply_attrs : ∀ (attrs : List param_attr) (msg : IRString) (dt : dtyp)
    {v1 : @dvalue PInf} {v2 : @dvalue PFin}, I2F_dvalue v1 v2 → I2F_refine_CFG I2F_dvalue
      (apply_attrs (Pa := PInf) attrs msg dt v1) (apply_attrs (Pa := PFin) attrs msg dt v2)

#source_check "src/rocq/Theory/I2F/I2F_denotation.v|Vellvm.Theory.I2F.I2F_denotation|I2F_apply_args_attrs"
  I2F_apply_args_attrs : ∀ (attrss : List (List param_attr)) (msg : IRString)
    {xs : List (dtyp × @dvalue PInf)} {ys : List (dtyp × @dvalue PFin)}, I2F_targs xs ys →
    I2F_refine_CFG I2F_targs (apply_args_attrs (Pa := PInf) attrss msg xs)
      (apply_args_attrs (Pa := PFin) attrss msg ys)

#source_check "src/rocq/Theory/I2F/I2F_denotation.v|Vellvm.Theory.I2F.I2F_denotation|I2F_check_call_return"
  I2F_check_call_return : ∀ (fattrs : List fn_attr) (ret_attrs : List param_attr)
    (ranges : Option (List (int_syntax × int_syntax))) (loc : IRString) (ret_t : dtyp)
    {xs : List (@dvalue PInf)} {ys : List (@dvalue PFin)}
    {r1 : @dvalue PInf ⊕ @dvalue PInf} {r2 : @dvalue PFin ⊕ @dvalue PFin},
    List.Forall₂ I2F_dvalue xs ys → Sum.LiftRel I2F_dvalue I2F_dvalue r1 r2 →
    I2F_refine_CFG (Sum.LiftRel I2F_dvalue I2F_dvalue)
      (check_call_return (Pa := PInf) fattrs ret_attrs ranges loc ret_t xs r1)
      (check_call_return (Pa := PFin) fattrs ret_attrs ranges loc ret_t ys r2)

#source_check "src/rocq/Theory/I2F/I2F_denotation.v|Vellvm.Theory.I2F.I2F_denotation|I2F_assume_bundle_check"
  I2F_assume_bundle_check : InfCheck → FinCheck → Prop

example (l : InfCheck) (r : FinCheck) : I2F_assume_bundle_check l r =
    (∀ loc xs ys, List.Forall₂ I2F_dvalue xs ys → I2F_refine_CFG (fun _ _ ↦ True)
      (l loc xs) (r loc ys)) := rfl

#source_check "src/rocq/Theory/I2F/I2F_denotation.v|Vellvm.Theory.I2F.I2F_denotation|I2F_assume_nonnull"
  I2F_assume_nonnull : I2F_assume_bundle_check (assume_nonnull (Pa := PInf)) (assume_nonnull (Pa := PFin))

#source_check "src/rocq/Theory/I2F/I2F_denotation.v|Vellvm.Theory.I2F.I2F_denotation|I2F_assume_noundef"
  I2F_assume_noundef : I2F_assume_bundle_check (assume_noundef (Pa := PInf)) (assume_noundef (Pa := PFin))

#source_check "src/rocq/Theory/I2F/I2F_denotation.v|Vellvm.Theory.I2F.I2F_denotation|I2F_assume_align"
  I2F_assume_align : I2F_assume_bundle_check (assume_align (Pa := PInf)) (assume_align (Pa := PFin))

#source_check "src/rocq/Theory/I2F/I2F_denotation.v|Vellvm.Theory.I2F.I2F_denotation|I2F_assume_dereferenceable"
  I2F_assume_dereferenceable : ∀ (or_null : Bool), I2F_assume_bundle_check
    (assume_dereferenceable (Pa := PInf) or_null) (assume_dereferenceable (Pa := PFin) or_null)

#source_check "src/rocq/Theory/I2F/I2F_denotation.v|Vellvm.Theory.I2F.I2F_denotation|I2F_assume_bundle_checks"
  I2F_assume_bundle_checks : List.Forall₂ (fun a b ↦ a.1 = b.1 ∧ I2F_assume_bundle_check a.2 b.2)
    (assume_bundle_checks (Pa := PInf)) (assume_bundle_checks (Pa := PFin))

#source_check "src/rocq/Theory/I2F/I2F_denotation.v|Vellvm.Theory.I2F.I2F_denotation|I2F_find_bundle_check"
  I2F_find_bundle_check : ∀ (tag : IRString) {l : List (IRString × InfCheck)} {r : List (IRString × FinCheck)},
    List.Forall₂ (fun a b ↦ a.1 = b.1 ∧ I2F_assume_bundle_check a.2 b.2) l r →
    match (l.find? (fun p ↦ p.1 == tag)).map Prod.snd, (r.find? (fun p ↦ p.1 == tag)).map Prod.snd with
    | some a, some b => I2F_assume_bundle_check a b
    | none, none => True
    | _, _ => False

#source_check "src/rocq/Theory/I2F/I2F_denotation.v|Vellvm.Theory.I2F.I2F_denotation|I2F_bundle_check"
  I2F_bundle_check : ∀ (f : exp dtyp) (tag : IRString),
    match bundle_check (Pa := PInf) (E := @CFGEtop PInf) (B := NoChoice) f tag,
          bundle_check (Pa := PFin) (E := @CFGEtop PFin) (B := NoChoice) f tag with
    | some a, some b => I2F_assume_bundle_check a b
    | none, none => True
    | _, _ => False

end PortChecks.I2FDenotationAttributes
