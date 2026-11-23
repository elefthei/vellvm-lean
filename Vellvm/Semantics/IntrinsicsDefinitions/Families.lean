module

public import Mathlib.Data.Int.Bitwise
public import Vellvm.Syntax.DynamicTypes

@[expose] public section
namespace Vellvm.Semantics.IntrinsicsDefinitions
open Syntax.LLVMAst Syntax.DynamicTypes

/-- Scalar unsigned values, integer vector lanes, or a poisoned argument. -/
inductive ival where
  | IV_Int (sz : Positive) (u : Int)
  | IV_Vector (elts : List (Positive × Int))
  | IV_Poison
export ival (IV_Int IV_Vector IV_Poison)

/-- Integer results are narrowed by the caller, including the value paired with an overflow flag. -/
inductive ires where
  | IR_Int (sz : Positive) (z : Int)
  | IR_Overflow (sz : Positive) (z : Int) (overflow : Bool)
  | IR_Poison
export ires (IR_Int IR_Overflow IR_Poison)

abbrev int_intrinsic := dtyp → List ival → Option ires

def imodulus (sz : Positive) : Int := 2 ^ sz.val

def isigned (sz : Positive) (u : Int) : Int :=
  let m := imodulus sz
  if 2 * u < m then u else u - m

def imin_signed (sz : Positive) : Int := -(2 ^ (sz.val - 1))
def imax_signed (sz : Positive) : Int := 2 ^ (sz.val - 1) - 1
def imax_unsigned (sz : Positive) : Int := imodulus sz - 1

def sclamp (sz : Positive) (z : Int) : Int := max (imin_signed sz) (min z (imax_signed sz))
def uclamp (sz : Positive) (z : Int) : Int := max 0 (min z (imax_unsigned sz))

def on_signed {A : Type u} (f : Int → Int → A) (sz : Positive) (a b : Int) : A :=
  f (isigned sz a) (isigned sz b)

def int_binary (f : Positive → Int → Int → ires) : int_intrinsic
  | _, [.IV_Int sz a, .IV_Int sz' b] => if sz == sz' then some (f sz a b) else none
  | _, _ => none

def int_arith (f : Positive → Int → Int → Int) : int_intrinsic :=
  int_binary fun sz a b ↦ IR_Int sz (f sz a b)

def llvm_smax := int_arith (on_signed max)
def llvm_smin := int_arith (on_signed min)
def llvm_umax := int_arith (fun _ ↦ max)
def llvm_umin := int_arith (fun _ ↦ min)

def signed_overflow (f : Int → Int → Int) : int_intrinsic :=
  int_binary fun sz a b ↦
    let z := on_signed f sz a b
    IR_Overflow sz z (z != sclamp sz z)

def unsigned_overflow (f : Int → Int → Int) : int_intrinsic :=
  int_binary fun sz a b ↦
    let z := f a b
    IR_Overflow sz z (z != uclamp sz z)

def llvm_sadd_with_overflow := signed_overflow (· + ·)
def llvm_ssub_with_overflow := signed_overflow (· - ·)
def llvm_smul_with_overflow := signed_overflow (· * ·)
def llvm_uadd_with_overflow := unsigned_overflow (· + ·)
def llvm_usub_with_overflow := unsigned_overflow (· - ·)
def llvm_umul_with_overflow := unsigned_overflow (· * ·)

def llvm_sadd_sat := int_arith (fun sz a b ↦ sclamp sz (on_signed (· + ·) sz a b))
def llvm_ssub_sat := int_arith (fun sz a b ↦ sclamp sz (on_signed (· - ·) sz a b))
def llvm_uadd_sat := int_arith (fun sz a b ↦ uclamp sz (a + b))
def llvm_usub_sat := int_arith (fun sz a b ↦ uclamp sz (a - b))

def shl_sat (f : Positive → Int → Int → Int) : int_intrinsic :=
  int_binary fun sz a b ↦ if (sz.val : Int) ≤ b then IR_Poison else IR_Int sz (f sz a b)

def llvm_sshl_sat := shl_sat (fun sz a b ↦ sclamp sz (isigned sz a <<< b))
def llvm_ushl_sat := shl_sat (fun sz a b ↦ uclamp sz (a <<< b))

def int_flagged (f : Positive → Int → Bool → ires) : int_intrinsic
  | _, [.IV_Int sz a, .IV_Int w flag] => if w.val == 1 then some (f sz a (flag != 0)) else none
  | _, _ => none

def llvm_abs := int_flagged fun sz a is_int_min_poison ↦
  let s := isigned sz a
  if is_int_min_poison && s == imin_signed sz then IR_Poison else IR_Int sz s.natAbs

def count_zeros (f : Positive → Int → Int) : int_intrinsic :=
  int_flagged fun sz a is_zero_poison ↦
    if a == 0 then (if is_zero_poison then IR_Poison else IR_Int sz sz.val) else IR_Int sz (f sz a)

def llvm_ctlz := count_zeros (fun sz a ↦ (sz.val : Int) - 1 - a.toNat.log2)
def llvm_cttz := count_zeros (fun _ a ↦ (Int.land a (-a)).toNat.log2)

def int_unary (f : Positive → Int → Int) : int_intrinsic
  | _, [.IV_Int sz a] => some (IR_Int sz (f sz a))
  | _, _ => none

def pos_popcount (p : Positive) : Int :=
  (p.val.log2 + 1).fold (fun i _ acc ↦ acc + (p.val.testBit i).toNat) 0

def llvm_ctpop := int_unary fun _ a ↦ match a with
  | .ofNat (n + 1) => pos_popcount ⟨n + 1, Nat.zero_lt_succ _⟩
  | _ => 0

def llvm_bitreverse := int_unary fun sz a ↦
  sz.val.fold (fun i _ acc ↦ 2 * acc + (a.testBit i).toNat) 0

def funnel_shift (f : Positive → Int → Int → Int) : int_intrinsic
  | _, [.IV_Int sz a, .IV_Int sz' b, .IV_Int sz'' c] =>
    if sz == sz' && sz == sz'' then some (IR_Int sz (f sz (a * imodulus sz + b) (c % sz.val)))
    else none
  | _, _ => none

def llvm_fshl := funnel_shift (fun sz ab c ↦ (ab <<< c) >>> (sz.val : Int))
def llvm_fshr := funnel_shift (fun _ ab c ↦ ab >>> c)

def three_way (f : Positive → Int → Int → Ordering) : int_intrinsic
  | .DTYPE_Base (.DTYPE_I r), [.IV_Int sz a, .IV_Int sz' b] =>
    if sz == sz' then some (IR_Int r (match f sz a b with | .lt => -1 | .eq => 0 | .gt => 1))
    else none
  | _, _ => none

def llvm_scmp := three_way (on_signed compare)
def llvm_ucmp := three_way (fun _ ↦ compare)

def vector_reduce (f : Positive → Int → Int → Int) : int_intrinsic
  | _, [.IV_Vector ((sz, a) :: elts)] =>
    some (IR_Int sz (elts.foldl (fun acc lane ↦ f sz acc lane.2 % imodulus sz) a))
  | _, _ => none

def llvm_vector_reduce_add := vector_reduce (fun _ ↦ (· + ·))
def llvm_vector_reduce_mul := vector_reduce (fun _ ↦ (· * ·))
def llvm_vector_reduce_and := vector_reduce (fun _ ↦ Int.land)
def llvm_vector_reduce_or := vector_reduce (fun _ ↦ Int.lor)
def llvm_vector_reduce_xor := vector_reduce (fun _ ↦ Int.xor)
def llvm_vector_reduce_smax := vector_reduce (on_signed max)
def llvm_vector_reduce_smin := vector_reduce (on_signed min)
def llvm_vector_reduce_umax := vector_reduce (fun _ ↦ max)
def llvm_vector_reduce_umin := vector_reduce (fun _ ↦ min)

/-- An overloaded intrinsic has one family for all type manglings. -/
inductive intrinsic_family where
  | Intr_int (f : int_intrinsic)
  | Intr_fabs
  | Intr_maxnum
  | Intr_minimum
  | Intr_throw
  | Intr_assume
  | Intr_va_start
  | Intr_va_end
  | Intr_va_copy
  | Intr_memcpy
  | Intr_memmove
  | Intr_memset
  | Intr_malloc
  | Intr_free
export intrinsic_family (Intr_int Intr_fabs Intr_maxnum Intr_minimum Intr_throw Intr_assume
  Intr_va_start Intr_va_end Intr_va_copy Intr_memcpy Intr_memmove Intr_memset Intr_malloc Intr_free)

def intrinsic_table : List ((IRString × Bool) × intrinsic_family) :=
  [(("fabs".toUTF8, true), Intr_fabs),
   (("maxnum".toUTF8, true), Intr_maxnum),
   (("minimum".toUTF8, true), Intr_minimum),
   (("memcpy".toUTF8, true), Intr_memcpy),
   (("memmove".toUTF8, true), Intr_memmove),
   (("memset".toUTF8, true), Intr_memset),
   (("vellvm.internal.throw".toUTF8, false), Intr_throw),
   (("assume".toUTF8, false), Intr_assume),
   (("va_start".toUTF8, false), Intr_va_start),
   (("va_end".toUTF8, false), Intr_va_end),
   (("va_copy".toUTF8, false), Intr_va_copy),
   (("smax".toUTF8, true), Intr_int llvm_smax),
   (("smin".toUTF8, true), Intr_int llvm_smin),
   (("umax".toUTF8, true), Intr_int llvm_umax),
   (("umin".toUTF8, true), Intr_int llvm_umin),
   (("sadd.with.overflow".toUTF8, true), Intr_int llvm_sadd_with_overflow),
   (("ssub.with.overflow".toUTF8, true), Intr_int llvm_ssub_with_overflow),
   (("smul.with.overflow".toUTF8, true), Intr_int llvm_smul_with_overflow),
   (("uadd.with.overflow".toUTF8, true), Intr_int llvm_uadd_with_overflow),
   (("usub.with.overflow".toUTF8, true), Intr_int llvm_usub_with_overflow),
   (("umul.with.overflow".toUTF8, true), Intr_int llvm_umul_with_overflow),
   (("sadd.sat".toUTF8, true), Intr_int llvm_sadd_sat),
   (("ssub.sat".toUTF8, true), Intr_int llvm_ssub_sat),
   (("uadd.sat".toUTF8, true), Intr_int llvm_uadd_sat),
   (("usub.sat".toUTF8, true), Intr_int llvm_usub_sat),
   (("sshl.sat".toUTF8, true), Intr_int llvm_sshl_sat),
   (("ushl.sat".toUTF8, true), Intr_int llvm_ushl_sat),
   (("abs".toUTF8, true), Intr_int llvm_abs),
   (("ctlz".toUTF8, true), Intr_int llvm_ctlz),
   (("cttz".toUTF8, true), Intr_int llvm_cttz),
   (("ctpop".toUTF8, true), Intr_int llvm_ctpop),
   (("bitreverse".toUTF8, true), Intr_int llvm_bitreverse),
   (("fshl".toUTF8, true), Intr_int llvm_fshl),
   (("fshr".toUTF8, true), Intr_int llvm_fshr),
   (("scmp".toUTF8, true), Intr_int llvm_scmp),
   (("ucmp".toUTF8, true), Intr_int llvm_ucmp),
   (("vector.reduce.add".toUTF8, true), Intr_int llvm_vector_reduce_add),
   (("vector.reduce.mul".toUTF8, true), Intr_int llvm_vector_reduce_mul),
   (("vector.reduce.and".toUTF8, true), Intr_int llvm_vector_reduce_and),
   (("vector.reduce.or".toUTF8, true), Intr_int llvm_vector_reduce_or),
   (("vector.reduce.xor".toUTF8, true), Intr_int llvm_vector_reduce_xor),
   (("vector.reduce.smax".toUTF8, true), Intr_int llvm_vector_reduce_smax),
   (("vector.reduce.smin".toUTF8, true), Intr_int llvm_vector_reduce_smin),
   (("vector.reduce.umax".toUTF8, true), Intr_int llvm_vector_reduce_umax),
   (("vector.reduce.umin".toUTF8, true), Intr_int llvm_vector_reduce_umin)]

def is_digit (c : UInt8) : Bool := 48 ≤ c && c ≤ 57

def startsManglingAt (s : IRString) (i : Nat) : Bool :=
  if h : i + 1 < s.size then
    let c := s[i]'(by omega)
    (c == 'i'.toUInt8 || c == 'f'.toUInt8 || c == 'p'.toUInt8 || c == 'v'.toUInt8) &&
      is_digit s[i + 1]
  else false

def starts_mangling (s : IRString) : Bool := startsManglingAt s 0

def hasPrefixAt (pre s : IRString) (start : Nat) : Bool :=
  if h : start + pre.size ≤ s.size then
    pre.size.all fun i hi ↦ pre[i] == s[start + i]'(by omega)
  else false

def namesAt (overloaded : Bool) (fam name : IRString) (start : Nat) : Bool :=
  let stop := start + fam.size
  hasPrefixAt fam name start &&
    (if h : stop < name.size then
      overloaded && name[stop] == '.'.toUInt8 && startsManglingAt name (stop + 1)
    else true)

def names_intrinsic (overloaded : Bool) (fam name : IRString) : Bool :=
  namesAt overloaded fam name 0

def strip_prefix (pre s : IRString) : Option IRString :=
  if pre.size == 0 then some s
  else if hasPrefixAt pre s 0 then some (s.extract pre.size s.size) else none

def lookup_intrinsic (name : IRString) : Option intrinsic_family :=
  let pre := "llvm.".toUTF8
  if hasPrefixAt pre name 0 then
    (intrinsic_table.find? (fun ((fam, overloaded), _) ↦ namesAt overloaded fam name pre.size)).map
      Prod.snd
  else if name == "malloc".toUTF8 then some Intr_malloc
  else if name == "free".toUTF8 then some Intr_free
  else none

def is_intrinsic : function_id → Bool
  | .Name s => (lookup_intrinsic s).isSome
  | _ => false

def intrinsic_exp {T : Type} : exp T → Option IRString
  | .EXP_Ident (.ID_Global (.Name s)) => if (lookup_intrinsic s).isSome then some s else none
  | _ => none

-- Only the start of the mangling is inspected; the remaining bytes need not be UTF-8.
#guard match lookup_intrinsic ("llvm.smax.i3".toUTF8.push 255) with
  | some (.Intr_int _) => true
  | _ => false

example (t : dtyp) : let w : Positive := ⟨3, by decide⟩
    llvm_smax t [IV_Int w 7, IV_Int w 4] = some (IR_Int w (-1)) := rfl

end Vellvm.Semantics.IntrinsicsDefinitions
