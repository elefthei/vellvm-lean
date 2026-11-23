import Vellvm.Semantics.DynamicValues.Canonical
import Vellvm.Semantics.DynamicValues.Show
import Vellvm.Numeric.Floats.Basic
import Vellvm.Syntax.ShowAST
import Vellvm.Syntax.AstLib

namespace Vellvm.Semantics.DynamicValues
open Interfaces.Params VellvmIntegers EOU Numeric Syntax.LLVMAst Syntax.DynamicTypes
open Utils.ListUtil Syntax.ShowAST

variable [Pa : Params]

private def boolValue (b : Bool) : dvalue_base :=
  DVALUE_I ⟨1, by decide⟩ (if b then Integers.one else Integers.zero)

def eval_int_op {I : Type u} [v : VMemInt I] [ToDvalueBase I] (op : ibinop) (x y : I) :
    EOU dvalue_base := do
  let poison := dvp v.mdtyp_of_int
  let ip := v.mdtyp_of_int == DTYPE_Iptr
  let tooWide := fun () => v.mbitwidth.any fun w => munsigned y ≥ (w.val : Int)
  let signedOverflow := fun () => v.mmin_signed == some (msigned x) && msigned y == -1
  let shiftedOut := fun () => munsigned x % Flocq.pow2 (munsigned y) != 0
  match op with
  | .Add u s =>
    if u && mequ (madd_carry x y mzero) mone || s && mequ (madd_overflow x y mzero) mone then
      return poison
    EOU.bind (madd x y) (pure ∘ tdb)
  | .Sub u s =>
    if u && mequ (msub_borrow x y mzero) mone || s && mequ (msub_overflow x y mzero) mone then
      return poison
    EOU.bind (msub x y) (pure ∘ tdb)
  | .Mul u s =>
    EOU.bind (mmul x y) fun r => do
      let up := decide (munsigned x * munsigned y > munsigned r)
      if ip then
        if up then return ← raise_oom "Multiplication overflow on iptr.".toUTF8
      else
        let sp := msigned x * msigned y
        if (u && up) || (s && (v.mmin_signed.any (fun n => n > sp) ||
                               v.mmax_signed.any (fun n => sp > n))) then return poison
      return tdb r
  | .Shl u s =>
    if !ip && tooWide () then return poison
    EOU.bind (mshl x y) fun r => do
      let up := decide (Flocq.shiftl (munsigned x) (munsigned y) > munsigned r)
      if ip then
        if up then return ← raise_oom "Shl unsigned overflow on iptr.".toUTF8
      else
        if u && up then return poison
        if s then
          if let some w := v.mbitwidth then
            return ← EOU.bind (mnegative r) fun n =>
              if Flocq.shiftr (munsigned x) ((w.val : Int) - munsigned y) !=
                  munsigned n * (Flocq.pow2 (munsigned y) - 1) then pure poison else pure (tdb r)
      return tdb r
  | .UDiv ex =>
    if munsigned y == 0 then return ← raise_ub "Unsigned division by 0.".toUTF8
    if ex && munsigned x % munsigned y != 0 then return poison
    return tdb (mdivu x y)
  | .SDiv ex =>
    if ip then return ← raise_error "Signed division for iptr.".toUTF8
    if msigned y == 0 then return ← raise_ub "Signed division by 0.".toUTF8
    if signedOverflow () then return ← raise_ub "Signed division overflow.".toUTF8
    if ex && msigned x % msigned y != 0 then return poison
    EOU.bind (mdivs x y) (pure ∘ tdb)
  | .LShr ex =>
    if (!ip && tooWide ()) || (ex && shiftedOut ()) then return poison
    return tdb (mshru x y)
  | .AShr ex =>
    if ip then return ← raise_error "Arithmetic shift for iptr.".toUTF8
    if tooWide () || (ex && shiftedOut ()) then return poison
    return tdb (mshr x y)
  | .URem =>
    if munsigned y == 0 then return ← raise_ub "Unsigned mod 0.".toUTF8
    return tdb (mmodu x y)
  | .SRem =>
    if ip then return ← raise_error "Signed division for iptr.".toUTF8
    if msigned y == 0 then return ← raise_ub "Signed mod 0.".toUTF8
    if signedOverflow () then return ← raise_ub "Signed mod overflow.".toUTF8
    EOU.bind (mmods x y) (pure ∘ tdb)
  | .And => return tdb (mand x y)
  | .Or b =>
    let r := mor x y
    if b && !mequ r (mxor x y) then return poison
    return tdb r
  | .Xor => return tdb (mxor x y)

def coerce_integer_to_int (bits : Option Positive) (i : Int) : EOU dvalue_base :=
  match bits with
  | some w => pure (DVALUE_I w (Integers.repr i))
  | none => DVALUE_Iptr <$> Pa.IPTR.VMemInt_iptr.mrepr i

def eval_iop_integer_base (op : ibinop) (a b : dvalue_base) : EOU dvalue_base := do
  match a, b with
  | .DVALUE_I w x, .DVALUE_I z y =>
    if h : z = w then return ← eval_int_op op x (h ▸ y)
    else return ← raise_error "ill_typed-iop: integer bitwidth mismatch.".toUTF8
  | .DVALUE_Iptr x, .DVALUE_Iptr y =>
    letI := Pa.IPTR.VMemInt_iptr
    return ← eval_int_op op x y
  | _, .DVALUE_Poison =>
    if Syntax.AstLib.iop_is_div op then return ← raise_ub "Division by poison.".toUTF8
    return DVALUE_Poison
  | .DVALUE_Poison, v =>
    if Syntax.AstLib.iop_is_div op then
      let y ← match v with
        | .DVALUE_I _ i => pure (Integers.signed i)
        | .DVALUE_Iptr i => pure (Pa.IPTR.to_Z i)
        | _ => raise_error "ill_typed-iop: division".toUTF8
      if y == 0 then return ← raise_ub "Division of poison by 0.".toUTF8
      if (match op with | .SDiv _ | .SRem => true | _ => false) && y == -1 then
        return ← raise_ub "Signed division/remainder poison overflow".toUTF8
    return DVALUE_Poison
  | _, _ => return ← raise_error "ill_typed-iop".toUTF8

private def binaryOp (op : dvalue_base → dvalue_base → EOU dvalue_base) (dt : dtyp)
    (a b : dvalue) (resultType : Nat → dtyp) (illegal : IRString) (lengthErr : Unit → IRString) :
    EOU dvalue := do
  match dt with
  | .DTYPE_Array true sz _ =>
    match vector_elts sz a, vector_elts sz b with
    | some xs, some ys =>
      if xs.length != ys.length then return ← raise_ub (lengthErr ())
      let xs ← map_monad dvalue_to_dvalue_base xs
      let ys ← map_monad dvalue_to_dvalue_base ys
      let zs ← vec_loop op (xs.zip ys)
      return canonicalize_agg (resultType sz) (zs.map DVALUE_Base)
    | _, _ => return ← raise_error illegal
  | _ => match a, b with
    | .DVALUE_Base x, .DVALUE_Base y => return DVALUE_Base (← op x y)
    | _, _ => return ← raise_error illegal

def eval_iop (op : ibinop) (dt : dtyp) (a b : dvalue) : EOU dvalue :=
  binaryOp (eval_iop_integer_base op) dt a b (fun _ => dt)
    "eval_iop called on illegal dvalue".toUTF8 fun _ =>
      "iop: ".toUTF8 ++ show_ibinop op ++ " of different-length vectors".toUTF8

def eval_int_icmp {I : Type u} [v : VMemInt I] (samesign : Bool) (op : icmp) (x y : I) :
    EOU dvalue_base := do
  let signedCmp := fun c (msg : String) =>
    if v.mdtyp_of_int == DTYPE_Iptr then raise_error msg.toUTF8 else pure (mcmp c x y)
  let c ← match op with
    | .Eq => pure (mcmpu .Ceq x y)
    | .Ne => pure (mcmpu .Cne x y)
    | .Ugt => pure (mcmpu .Cgt x y)
    | .Uge => pure (mcmpu .Cge x y)
    | .Ult => pure (mcmpu .Clt x y)
    | .Ule => pure (mcmpu .Cle x y)
    | .Sgt => signedCmp .Cgt "Signed '>' comparison on iptr type."
    | .Sge => signedCmp .Cge "Signed '>=' comparison on iptr type."
    | .Slt => signedCmp .Clt "Signed '<' comparison on iptr type."
    | .Sle => signedCmp .Cle "Signed '>' comparison on iptr type."
  return if samesign && !msamesign x y then dvp (DTYPE_I ⟨1, by decide⟩) else boolValue c

/-
Flocq Bits.v: Copyright (C) 2011–2018 Sylvie Boldo and Guillaume Melquiond.
Licensed under LGPL-3.0-or-later. LLVM's arithmetic uses the Bits NaN selector,
not CompCert's architecture-dependent quieting selector.
-/
private def firstNaN {p e : Int} (fallback : {n : Flocq.binary_float p e // Flocq.is_nan n = true}) :
    Flocq.Nan₂ p e
  | .B754_nan s m h, _ | _, .B754_nan s m h => ⟨.B754_nan s m h, rfl⟩
  | _, _ => fallback

private def nan64 : Flocq.Nan₂ 53 1024 :=
  firstNaN ⟨.B754_nan false ⟨2^51, by decide⟩ (by decide), rfl⟩

private def nan32 : Flocq.Nan₂ 24 128 :=
  firstNaN ⟨.B754_nan false ⟨2^22, by decide⟩ (by decide), rfl⟩

def double_op (op : fbinop) (x y : ll_double) : EOU dvalue_base :=
  match op with
  | .FAdd => pure (DVALUE_Double (Flocq.Bplus 53 1024 (by decide) (by decide) nan64 FT_Rounding x y))
  | .FSub => pure (DVALUE_Double (Flocq.Bminus 53 1024 (by decide) (by decide) nan64 FT_Rounding x y))
  | .FMul => pure (DVALUE_Double (Flocq.Bmult 53 1024 (by decide) (by decide) nan64 FT_Rounding x y))
  | .FDiv => pure (DVALUE_Double (Flocq.Bdiv 53 1024 (by decide) (by decide) nan64 FT_Rounding x y))
  | .FRem => raise_error "unimplemented double operation".toUTF8

def float_op (op : fbinop) (x y : ll_float) : EOU dvalue_base :=
  match op with
  | .FAdd => pure (DVALUE_Float (Flocq.Bplus 24 128 (by decide) (by decide) nan32 FT_Rounding x y))
  | .FSub => pure (DVALUE_Float (Flocq.Bminus 24 128 (by decide) (by decide) nan32 FT_Rounding x y))
  | .FMul => pure (DVALUE_Float (Flocq.Bmult 24 128 (by decide) (by decide) nan32 FT_Rounding x y))
  | .FDiv => pure (DVALUE_Float (Flocq.Bdiv 24 128 (by decide) (by decide) nan32 FT_Rounding x y))
  | .FRem => raise_error "unimplemented float operation".toUTF8

-- A signaling NaN is not quieted by Flocq Bits arithmetic.
example (sign : Bool) (pl : Positive) (valid : Flocq.nan_pl 24 pl = true) :
    float_op .FAdd (.B754_nan sign pl valid) (.B754_zero false) =
      raise_ret (DVALUE_Float (.B754_nan sign pl valid)) := rfl

def eval_fop_base (op : fbinop) (a b : dvalue_base) : EOU dvalue_base :=
  match a, b with
  | .DVALUE_Float x, .DVALUE_Float y => float_op op x y
  | .DVALUE_Double x, .DVALUE_Double y => double_op op x y
  | .DVALUE_Poison, _ | .DVALUE_Float _, .DVALUE_Poison | .DVALUE_Double _, .DVALUE_Poison =>
    pure DVALUE_Poison
  | _, _ => raise_error ("ill_typed-fop: ".toUTF8 ++ show_fbinop op ++ " ".toUTF8 ++
      show_dvalue_base a ++ " ".toUTF8 ++ show_dvalue_base b)

def eval_fop (op : fbinop) (dt : dtyp) (a b : dvalue) : EOU dvalue :=
  binaryOp (eval_fop_base op) dt a b (fun _ => dt) "eval_fop got illegal value".toUTF8 fun _ =>
    "fop: ".toUTF8 ++ show_fbinop op ++ " different-length vectors of type v1 = ".toUTF8 ++
      show_dvalue a ++ "v2 = ".toUTF8 ++ show_dvalue b

def eval_fneg_base : dvalue_base → EOU dvalue_base
  | .DVALUE_Float x => pure (DVALUE_Float (Floats.Float32.neg x))
  | .DVALUE_Double x => pure (DVALUE_Double (Floats.Float.neg x))
  | .DVALUE_Poison => pure DVALUE_Poison
  | _ => raise_error "ill_typed-fneg ".toUTF8

def eval_fneg (dt : dtyp) (v : dvalue) : EOU dvalue := do
  match v with
  | .DVALUE_Base b => return DVALUE_Base (← eval_fneg_base b)
  | .DVALUE_Array true xs =>
    let bs ← map_monad dvalue_to_dvalue_base xs
    let ys ← map_monad eval_fneg_base bs
    return canonicalize_agg dt (ys.map DVALUE_Base)
  | _ => return ← raise_error "eval_fneg got illegal value".toUTF8

def not_nan32 (x : ll_float) := !Flocq.is_nan x
def ordered32 (x y : ll_float) := not_nan32 x && not_nan32 y
def not_nan64 (x : ll_double) := !Flocq.is_nan x
def ordered64 (x y : ll_double) := not_nan64 x && not_nan64 y

private def cmpResult (ord : Bool) (cmp : Integers.comparison → Bool) : fcmp → Bool
  | .FFalse => false
  | .FOeq => ord && cmp .Ceq
  | .FOgt => ord && cmp .Cgt
  | .FOge => ord && cmp .Cge
  | .FOlt => ord && cmp .Clt
  | .FOle => ord && cmp .Cle
  | .FOne => ord && cmp .Cne
  | .FOrd => ord
  | .FUno => !ord
  | .FUeq => !ord || cmp .Ceq
  | .FUgt => !ord || cmp .Cgt
  | .FUge => !ord || cmp .Cge
  | .FUlt => !ord || cmp .Clt
  | .FUle => !ord || cmp .Cle
  | .FUne => !ord || cmp .Cne
  | .FTrue => true

def float_cmp (op : fcmp) (x y : ll_float) : dvalue_base :=
  boolValue (cmpResult (ordered32 x y) (fun c => Floats.Float32.cmp c x y) op)

def double_cmp (op : fcmp) (x y : ll_double) : dvalue_base :=
  boolValue (cmpResult (ordered64 x y) (fun c => Floats.Float.cmp c x y) op)

def eval_fcmp_base (op : fcmp) (a b : dvalue_base) : EOU dvalue_base :=
  match a, b with
  | .DVALUE_Float x, .DVALUE_Float y => pure (float_cmp op x y)
  | .DVALUE_Double x, .DVALUE_Double y => pure (double_cmp op x y)
  | .DVALUE_Poison, .DVALUE_Poison | .DVALUE_Poison, .DVALUE_Float _
  | .DVALUE_Poison, .DVALUE_Double _ | .DVALUE_Float _, .DVALUE_Poison
  | .DVALUE_Double _, .DVALUE_Poison => pure DVALUE_Poison
  | _, _ => raise_error "ill_typed-fcmp".toUTF8

def eval_fcmp (op : fcmp) (dt : dtyp) (a b : dvalue) : EOU dvalue :=
  binaryOp (eval_fcmp_base op) dt a b (fun sz => DTYPE_Array true sz (DTYPE_I ⟨1, by decide⟩))
    "eval_fcmp got illegal value".toUTF8 (fun _ => "fcmp of different-length vectors".toUTF8)

end Vellvm.Semantics.DynamicValues
