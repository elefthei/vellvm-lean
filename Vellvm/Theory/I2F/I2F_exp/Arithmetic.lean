import Batteries.Tactic.OpenPrivate
import Vellvm.Theory.I2F.I2F_exp.Scalars
import Vellvm.Theory.I2F.I2F_exp.Values

namespace Vellvm.Theory.I2F.I2F_exp
open Vellvm Vellvm.Numeric Vellvm.Semantics Vellvm.Syntax
open DynamicValues VellvmIntegers Operations.Compare LLVMAst DynamicTypes
open Vellvm.Theory.I2F.Refinement

open Utils.ListUtil Semantics.EOU
open private binaryOp in eval_iop

private theorem laneMap {xs ys} (h : List.Forall₂ I2F_dvalue xs ys) :
    I2F_EOU (List.Forall₂ I2F_dvalue_base)
      (map_monad (@dvalue_to_dvalue_base PInf) xs) (map_monad (@dvalue_to_dvalue_base PFin) ys) :=
  I2F_EOU_map_monad2 _ _ h (fun _ _ hab ↦ I2F_dvalue_to_dvalue_base hab)

private theorem lanesRelated (f : @dvalue_base PInf → @dvalue_base PInf → EOU (@dvalue_base PInf))
    (g : @dvalue_base PFin → @dvalue_base PFin → EOU (@dvalue_base PFin))
    (hf : ∀ a b c d, I2F_dvalue_base a c → I2F_dvalue_base b d → I2F_EOU I2F_dvalue_base (f a b) (g c d))
    (dt : dtyp) {xs ys zs ws} (hx : List.Forall₂ I2F_dvalue xs ys) (hz : List.Forall₂ I2F_dvalue zs ws) :
    I2F_EOU I2F_dvalue
      (do let a ← map_monad (@dvalue_to_dvalue_base PInf) xs
          let b ← map_monad (@dvalue_to_dvalue_base PInf) zs
          let c ← vec_loop f (a.zip b)
          pure (@canonicalize_agg PInf dt (c.map (@DVALUE_Base PInf))))
      (do let a ← map_monad (@dvalue_to_dvalue_base PFin) ys
          let b ← map_monad (@dvalue_to_dvalue_base PFin) ws
          let c ← vec_loop g (a.zip b)
          pure (@canonicalize_agg PFin dt (c.map (@DVALUE_Base PFin)))) := by
  refine I2F_EOU_bind _ _ (laneMap hx) fun _ _ ha ↦ ?_
  refine I2F_EOU_bind _ _ (laneMap hz) fun _ _ hb ↦ ?_
  refine I2F_EOU_bind _ _ (I2F_EOU_vec_loop f g (Forall2_combine _ _ _ _ _ _ ha hb) hf) fun _ _ hc ↦ ?_
  exact I2F_EOU_ret _ _ (I2F_canonicalize_agg _ (Forall2_map_Base hc))

private theorem baseMap {x y} (h : I2F_EOU I2F_dvalue_base x y) :
    I2F_EOU I2F_dvalue (x >>= fun v ↦ pure (@DVALUE_Base PInf v))
      (y >>= fun v ↦ pure (@DVALUE_Base PFin v)) :=
  I2F_EOU_bind _ _ h fun _ _ hv ↦ I2F_EOU_ret _ _ (.I2F_dvalue_Base hv)

local macro "binary_cases" a:ident b:ident c:ident d:ident dt:ident ha:ident hb:ident scalar:term : tactic => `(tactic| (
  cases ($dt) with
  | DTYPE_Base _ | DTYPE_Struct _ _ =>
    cases ($ha) <;> cases ($hb) <;> first
      | exact I2F_EOU_error _ _
      | exact baseMap (($scalar) (by assumption) (by assumption))
  | DTYPE_Array flag n t =>
    cases flag with
    | false =>
      cases ($ha) <;> cases ($hb) <;> first
        | exact I2F_EOU_error _ _
        | exact baseMap (($scalar) (by assumption) (by assumption))
    | true =>
      have hx := I2F_vector_elts n $ha
      have hz := I2F_vector_elts n $hb
      cases x : @vector_elts PInf n $a <;> cases y : @vector_elts PFin n $c <;>
        cases z : @vector_elts PInf n $b <;> cases w : @vector_elts PFin n $d <;>
        simp only [binaryOp, eval_icmp, x, y, z, w] at hx hz ⊢ <;> first
          | contradiction | exact I2F_EOU_error _ _ | skip
      simp only [hx.length_eq, hz.length_eq]
      split <;> first
        | exact I2F_EOU_ub _ _
        | exact lanesRelated _ _ (fun _ _ _ _ h₁ h₂ ↦ ($scalar) h₁ h₂) _ hx hz))

theorem I2F_eval_iop : ∀ ⦃a b : @dvalue PInf⦄ ⦃c d : @dvalue PFin⦄ (op : ibinop) (dt : dtyp),
    I2F_dvalue a c → I2F_dvalue b d →
    I2F_EOU I2F_dvalue (@eval_iop PInf op dt a b) (@eval_iop PFin op dt c d) := by
  intro a b c d op dt ha hb
  unfold eval_iop
  binary_cases a b c d dt ha hb (I2F_eval_iop_integer_base op)

theorem I2F_eval_icmp : ∀ ⦃a b : @dvalue PInf⦄ ⦃c d : @dvalue PFin⦄ (ss : Bool) (op : icmp) (dt : dtyp),
    I2F_dvalue a c → I2F_dvalue b d →
    I2F_EOU I2F_dvalue (@eval_icmp PInf ss op dt a b) (@eval_icmp PFin ss op dt c d) := by
  intro a b c d ss op dt ha hb
  binary_cases a b c d dt ha hb (I2F_eval_icmp_base ss op)

theorem I2F_eval_fop : ∀ ⦃a b : @dvalue PInf⦄ ⦃c d : @dvalue PFin⦄ (op : fbinop) (dt : dtyp),
    I2F_dvalue a c → I2F_dvalue b d →
    I2F_EOU I2F_dvalue (@eval_fop PInf op dt a b) (@eval_fop PFin op dt c d) := by
  intro a b c d op dt ha hb
  unfold eval_fop
  binary_cases a b c d dt ha hb (I2F_eval_fop_base op)

theorem I2F_eval_fcmp : ∀ ⦃a b : @dvalue PInf⦄ ⦃c d : @dvalue PFin⦄ (op : fcmp) (dt : dtyp),
    I2F_dvalue a c → I2F_dvalue b d →
    I2F_EOU I2F_dvalue (@eval_fcmp PInf op dt a b) (@eval_fcmp PFin op dt c d) := by
  intro a b c d op dt ha hb
  unfold eval_fcmp
  binary_cases a b c d dt ha hb (I2F_eval_fcmp_base op)

theorem I2F_eval_fneg : ∀ (dt : dtyp) ⦃a : @dvalue PInf⦄ ⦃b : @dvalue PFin⦄, I2F_dvalue a b →
    I2F_EOU I2F_dvalue (@eval_fneg PInf dt a) (@eval_fneg PFin dt b) := by
  intro dt a b hab
  cases hab with
  | I2F_dvalue_Base h => exact baseMap (I2F_eval_fneg_base h)
  | I2F_dvalue_Struct _ _ => exact I2F_EOU_error _ _
  | I2F_dvalue_Array v h =>
    cases v
    · exact I2F_EOU_error _ _
    · refine I2F_EOU_bind _ _ (laneMap h) fun _ _ hs ↦ ?_
      refine I2F_EOU_bind _ _ (I2F_EOU_map_monad2 _ _ hs (fun _ _ h ↦ I2F_eval_fneg_base h)) fun _ _ hr ↦ ?_
      exact I2F_EOU_ret _ _ (I2F_canonicalize_agg dt (Forall2_map_Base hr))

end Vellvm.Theory.I2F.I2F_exp
