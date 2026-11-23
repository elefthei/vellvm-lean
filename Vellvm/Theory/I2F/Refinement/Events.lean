module

public import Vellvm.Theory.I2F.Refinement.Values
public import Vellvm.Semantics.LLVMEvents
public import Vellvm.Utils.rutt_cutoff
public import Vellvm.Utils.RelationsUtil
public import Vellvm.Numeric.Rocqlib

@[expose] public section
namespace Vellvm.Theory.I2F.Refinement
open Semantics.LLVMEvents
open Utils.rutt_cutoff (prerel postrel)
open Utils.RelationsUtil (prod_rel)
open Numeric.Rocqlib (option_rel)
open ITree (Effect)

variable {E₁ E₂ F₁ F₂ : Effect.{u}}

def sum_prerel (p : prerel E₁ F₁) (q : prerel E₂ F₂) : prerel (E₁ ⊕ₑ E₂) (F₁ ⊕ₑ F₂)
  | .inl e, .inl f => p e f
  | .inr e, .inr f => q e f
  | _, _ => False

def inl_prerel (p : prerel (E₁ ⊕ₑ E₂) (F₁ ⊕ₑ F₂)) : prerel E₁ F₁ :=
  fun e f ↦ p (.inl e) (.inl f)

def inr_prerel (p : prerel (E₁ ⊕ₑ E₂) (F₁ ⊕ₑ F₂)) : prerel E₂ F₂ :=
  fun e f ↦ p (.inr e) (.inr f)

abbrev sum_postrel (p : postrel E₁ F₁) (q : postrel E₂ F₂) : postrel (E₁ ⊕ₑ E₂) (F₁ ⊕ₑ F₂) :=
  Utils.rutt_cutoff.sum_postrel p q

def inl_postrel (p : postrel (E₁ ⊕ₑ E₂) (F₁ ⊕ₑ F₂)) : postrel E₁ F₁ :=
  fun e a f b ↦ p (.inl e) a (.inl f) b

def inr_postrel (p : postrel (E₁ ⊕ₑ E₂) (F₁ ⊕ₑ F₂)) : postrel E₂ F₂ :=
  fun e a f b ↦ p (.inr e) a (.inr f) b

def I2FE_Call : prerel (@CallE PInf) (@CallE PFin)
  | @CallRequest.Call .(PInf) t cc f xs, @CallRequest.Call .(PFin) t' cc' f' ys => t = t' ∧ cc = cc' ∧ I2F_dvalue f f' ∧ I2F_targs xs ys

def I2FE_ExternalCall : prerel (@ExternalCallE PInf) (@ExternalCallE PFin)
  | @ExternalCallRequest.ExternalCall .(PInf) t f xs, @ExternalCallRequest.ExternalCall .(PFin) t' f' ys => t = t' ∧ I2F_dvalue f f' ∧ I2F_targs xs ys
  | @ExternalCallRequest.IO_stdout .(PInf) xs, @ExternalCallRequest.IO_stdout .(PFin) ys => xs = ys
  | @ExternalCallRequest.IO_stderr .(PInf) xs, @ExternalCallRequest.IO_stderr .(PFin) ys => xs = ys
  | _, _ => False

def I2FE_Intrinsic : prerel (@IntrinsicE PInf) (@IntrinsicE PFin)
  | @IntrinsicRequest.Intrinsic .(PInf) t f xs va, @IntrinsicRequest.Intrinsic .(PFin) t' f' ys va' =>
    t = t' ∧ f = f' ∧ I2F_targs xs ys ∧ option_rel I2F_Addr va va'

def I2FE_Global : prerel (@GlobalE PInf) (@GlobalE PFin)
  | @GlobalRequest.GlobalWrite .(PInf) i x, @GlobalRequest.GlobalWrite .(PFin) j y => i = j ∧ I2F_dvalue x y
  | @GlobalRequest.GlobalRead .(PInf) i, @GlobalRequest.GlobalRead .(PFin) j => i = j
  | _, _ => False

def I2FE_Local : prerel (@LocalE PInf) (@LocalE PFin)
  | @LocalRequest.LocalWrite .(PInf) i x, @LocalRequest.LocalWrite .(PFin) j y => i = j ∧ I2F_dvalue x y
  | @LocalRequest.LocalRead .(PInf) i, @LocalRequest.LocalRead .(PFin) j => i = j
  | _, _ => False

def I2FE_Stack : prerel (@StackE PInf) (@StackE PFin)
  | @StackRequest.StackPush .(PInf) xs, @StackRequest.StackPush .(PFin) ys =>
    List.Forall₂ (prod_rel Eq I2F_dvalue) xs ys
  | @StackRequest.StackPop .(PInf), @StackRequest.StackPop .(PFin) | @StackRequest.StackGetExc .(PInf), @StackRequest.StackGetExc .(PFin) => True
  | @StackRequest.StackRaise .(PInf) x, @StackRequest.StackRaise .(PFin) y => I2F_dvalue x y
  | _, _ => False

def I2FE_Memory : prerel (@MemoryE PInf) (@MemoryE PFin)
  | @MemoryRequest.MemPush .(PInf), @MemoryRequest.MemPush .(PFin) | @MemoryRequest.MemPop .(PInf), @MemoryRequest.MemPop .(PFin) => True
  | @MemoryRequest.Alloca .(PInf) t n a, @MemoryRequest.Alloca .(PFin) t' n' a' => t = t' ∧ n = n' ∧ a = a'
  | @MemoryRequest.Load .(PInf) t a, @MemoryRequest.Load .(PFin) t' a' => t = t' ∧ I2F_dvalue a a'
  | @MemoryRequest.Store .(PInf) t a v, @MemoryRequest.Store .(PFin) t' a' v' => t = t' ∧ I2F_dvalue a a' ∧ I2F_dvalue v v'
  | @MemoryRequest.Conv .(PInf) c t v u, @MemoryRequest.Conv .(PFin) c' t' v' u' => c = c' ∧ t = t' ∧ I2F_dvalue v v' ∧ u = u'
  | _, _ => False

def I2FE_Draw : prerel (@DrawE PInf) (@DrawE PFin)
  | .Draw t, .Draw t' => t = t'

def I2FE_Exc : prerel (@LLVMExcE PInf) (@LLVMExcE PFin)
  | @LLVMExcRequest.LLVMExc .(PInf) x, @LLVMExcRequest.LLVMExc .(PFin) y => I2F_dvalue x y

def I2FE_OOM : prerel OOME OOME | .ThrowOOM _, .ThrowOOM _ => True
def I2FE_UB : prerel UBE UBE | .ThrowUB _, .ThrowUB _ => True
def I2FE_Debug : prerel DebugE DebugE | .Debug _, .Debug _ => True
def I2FE_Failure : prerel FailureE FailureE | .Throw _, .Throw _ => True

def I2FA_Call : postrel (@CallE PInf) (@CallE PFin)
  | @CallRequest.Call .(PInf) .., x, @CallRequest.Call .(PFin) .., y => I2F_exc_dvalue x y

def I2FA_ExternalCall : postrel (@ExternalCallE PInf) (@ExternalCallE PFin)
  | @ExternalCallRequest.ExternalCall .(PInf) .., x, @ExternalCallRequest.ExternalCall .(PFin) .., y => I2F_dvalue x y
  | @ExternalCallRequest.IO_stdout .(PInf) _, _, @ExternalCallRequest.IO_stdout .(PFin) _, _ | @ExternalCallRequest.IO_stderr .(PInf) _, _, @ExternalCallRequest.IO_stderr .(PFin) _, _ => True
  | _, _, _, _ => False

def I2FA_Intrinsic : postrel (@IntrinsicE PInf) (@IntrinsicE PFin)
  | @IntrinsicRequest.Intrinsic .(PInf) .., x, @IntrinsicRequest.Intrinsic .(PFin) .., y => I2F_exc_dvalue x y

def I2FA_Global : postrel (@GlobalE PInf) (@GlobalE PFin)
  | @GlobalRequest.GlobalRead .(PInf) _, x, @GlobalRequest.GlobalRead .(PFin) _, y => I2F_dvalue x y
  | @GlobalRequest.GlobalWrite .(PInf) .., _, @GlobalRequest.GlobalWrite .(PFin) .., _ => True
  | _, _, _, _ => False

def I2FA_Local : postrel (@LocalE PInf) (@LocalE PFin)
  | @LocalRequest.LocalRead .(PInf) _, x, @LocalRequest.LocalRead .(PFin) _, y => I2F_dvalue x y
  | @LocalRequest.LocalWrite .(PInf) .., _, @LocalRequest.LocalWrite .(PFin) .., _ => True
  | _, _, _, _ => False

def I2FA_Stack : postrel (@StackE PInf) (@StackE PFin)
  | @StackRequest.StackGetExc .(PInf), x, @StackRequest.StackGetExc .(PFin), y => option_rel I2F_dvalue x y
  | @StackRequest.StackPush .(PInf) _, _, @StackRequest.StackPush .(PFin) _, _ | @StackRequest.StackPop .(PInf), _, @StackRequest.StackPop .(PFin), _
  | @StackRequest.StackRaise .(PInf) _, _, @StackRequest.StackRaise .(PFin) _, _ => True
  | _, _, _, _ => False

def I2FA_Memory : postrel (@MemoryE PInf) (@MemoryE PFin)
  | @MemoryRequest.Alloca .(PInf) .., x, @MemoryRequest.Alloca .(PFin) .., y | @MemoryRequest.Load .(PInf) .., x, @MemoryRequest.Load .(PFin) .., y
  | @MemoryRequest.Conv .(PInf) .., x, @MemoryRequest.Conv .(PFin) .., y => I2F_dvalue x y
  | @MemoryRequest.MemPush .(PInf), _, @MemoryRequest.MemPush .(PFin), _ | @MemoryRequest.MemPop .(PInf), _, @MemoryRequest.MemPop .(PFin), _ | @MemoryRequest.Store .(PInf) .., _, @MemoryRequest.Store .(PFin) .., _ => True
  | _, _, _, _ => False

def I2FA_Draw : postrel (@DrawE PInf) (@DrawE PFin)
  | .Draw _, x, .Draw _, y => I2F_dvalue x y

def I2FA_Exc : postrel (@LLVMExcE PInf) (@LLVMExcE PFin) := fun _ _ _ _ ↦ False
def I2FA_OOM : postrel OOME OOME := fun _ _ _ _ ↦ False
def I2FA_UB : postrel UBE UBE := fun _ _ _ _ ↦ False
def I2FA_Debug : postrel DebugE DebugE := fun _ _ _ _ ↦ True
def I2FA_Failure : postrel FailureE FailureE := fun _ _ _ _ ↦ False

end Vellvm.Theory.I2F.Refinement
