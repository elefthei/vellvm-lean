import Vellvm.Semantics.Libraries
import Vellvm.Theory.I2F.I2F_denotation.Core
import Vellvm.Theory.I2F.I2F_memory.Address

namespace Vellvm.Theory.I2F.I2F_toplevel
open Semantics Semantics.Libraries Semantics.DynamicValues Semantics.LLVMEvents
open Semantics.EOU Syntax.DynamicTypes Syntax.LLVMAst
open I2F_denotation I2F_memory I2F_exp Refinement
open Utils.rutt_cutoff (ruttc_iter ruttc_ret)
open Utils.RelationsUtil (prod_rel)
open VellvmIntegers (int8)

private theorem stdout_related (bytes : List int8) :
    I2F_refine_CFG Eq (io_stdout (Pa := PInf) bytes) (io_stdout (Pa := PFin) bytes) :=
  cfg_emit (D₁ := @ExternalCallE PInf) (D₂ := @ExternalCallE PFin)
    (@IO_stdout PInf bytes) (@IO_stdout PFin bytes) rfl (fun _ _ _ ↦ Subsingleton.elim _ _)

private theorem ub_related (s t : IRString) :
    I2F_refine_CFG I2F_dvalue (raiseUB s) (raiseUB t) :=
  I2F_refine_lift' _ _ _ (.I2F_EOU_ub s (.raise_ub t))

private theorem unary_related (msg : IRString)
    (f : @dvalue PInf → @CFGtop PInf (@dvalue PInf))
    (g : @dvalue PFin → @CFGtop PFin (@dvalue PFin))
    (h : ∀ x y, I2F_dvalue x y → I2F_refine_CFG I2F_dvalue (f x) (g y)) :
    I2F_function_denotation (Libraries.Worker.unary (Pa := PInf) msg f)
      (Libraries.Worker.unary (Pa := PFin) msg g) := by
  intro cc rt xs ys hargs
  cases hargs with
  | nil => exact cfg_raise _ _ _
  | @cons x y xs ys hxy htail =>
    cases htail with
    | nil => exact cfg_bind (h _ _ hxy.2) fun _ _ hab ↦ ruttc_ret _ _ (Sum.LiftRel.inr hab)
    | cons => exact cfg_raise _ _ _

theorem I2F_putchar_denotation :
    I2F_function_denotation (@putchar_denotation PInf) (@putchar_denotation PFin) := by
  unfold putchar_denotation Libraries.Worker.putchar_denotation
  apply unary_related
  intro x y h
  cases h with
  | I2F_dvalue_Base hb =>
    cases hb with
    | @I2F_dvalue_Int sz i =>
      dsimp only [Libraries.Worker.putcharBody]
      by_cases hsz : sz.val = 32
      · simp only [ite_eq_left hsz]
        exact cfg_bind (stdout_related _) fun _ _ _ ↦
          ruttc_ret _ _ (.I2F_dvalue_Base (.I2F_dvalue_Int _))
      · simp only [ite_eq_right hsz]
        exact ub_related _ _
    | _ => exact ub_related _ _
  | _ => exact ub_related _ _

private theorem loadedByte_related {x y} (h : I2F_dvalue x y) :
    I2F_EOU Eq (Libraries.Worker.loadedByte (Pa := PInf) x)
      (Libraries.Worker.loadedByte (Pa := PFin) y) := by
  cases h with
  | I2F_dvalue_Base hb =>
    cases hb with
    | @I2F_dvalue_Int sz i =>
      obtain ⟨n, hn⟩ := sz
      by_cases hn8 : n = 8
      · subst n
        exact .I2F_EOU_ret _ _ rfl
      · simp only [Libraries.Worker.loadedByte]
        split <;> split <;> first | exact .I2F_EOU_error _ _ | grind
    | _ => exact .I2F_EOU_error _ _
  | _ => exact .I2F_EOU_error _ _

theorem I2F_i8_str_index (p : PInf.PTR.ptr) (q : PFin.PTR.ptr) (i : Int) (hp : I2F_Addr p q) :
    I2F_refine_CFG Eq (@i8_str_index PInf p i) (@i8_str_index PFin q i) := by
  unfold i8_str_index Libraries.Worker.i8_str_index
  refine cfg_bind (I2F_refine_lift' _ _ _ (I2F_from_Z i)) fun x y hxy ↦ ?_
  refine cfg_bind (I2F_refine_lift' _ _ _ (I2F_ptr_byte_offset p q x y hp hxy)) fun a b hab ↦ ?_
  apply cfg_bind (RR := I2F_dvalue)
  · exact cfg_emit (D₁ := @MemoryE PInf) (D₂ := @MemoryE PFin)
      (@Load PInf _ (@DVALUE_Base PInf (@DVALUE_Pointer PInf a)))
      (@Load PFin _ (@DVALUE_Base PFin (@DVALUE_Pointer PFin b)))
      ⟨rfl, I2F_dvalue_Base (.I2F_dvalue_Pointer a b hab)⟩ (fun _ _ h ↦ h)
  · exact fun _ _ h ↦ I2F_refine_lift' _ _ _ (loadedByte_related h)

private theorem putsAt_related {p q} (hp : I2F_Addr p q) :
    I2F_refine_CFG I2F_dvalue (Libraries.Worker.putsAt (Pa := PInf) p)
      (Libraries.Worker.putsAt (Pa := PFin) q) := by
  unfold Libraries.Worker.putsAt
  refine cfg_bind (I2F_i8_str_index _ _ 0 hp) fun first _ hfirst ↦ ?_
  subst hfirst
  apply cfg_bind (RR := Eq)
  · apply ruttc_iter _ _ _ _ Eq Eq _ _ _ _ _ rfl
    rintro ⟨c, bytes, off⟩ _ rfl
    dsimp only
    by_cases hc : c = Numeric.Integers.zero
    · simp only [ite_eq_left hc]
      exact ruttc_ret _ _ (.inr rfl)
    · simp only [ite_eq_right hc]
      exact cfg_bind (I2F_i8_str_index _ _ off hp) fun _ _ he ↦ by
        cases he
        exact ruttc_ret _ _ (.inl rfl)
  · rintro bytes _ rfl
    exact cfg_bind (stdout_related bytes.reverse) fun _ _ _ ↦
      ruttc_ret _ _ (.I2F_dvalue_Base (.I2F_dvalue_Int _))

theorem I2F_puts_denotation :
    I2F_function_denotation (@puts_denotation PInf) (@puts_denotation PFin) := by
  unfold puts_denotation Libraries.Worker.puts_denotation
  apply unary_related
  intro x y h
  cases h with
  | I2F_dvalue_Base hb =>
    cases hb with
    | I2F_dvalue_Pointer _ _ hp => exact putsAt_related hp
    | _ => exact ub_related _ _
  | _ => exact ub_related _ _

theorem I2F_LIBRARIES :
    List.Forall₂ (prod_rel Eq I2F_function_denotation) (@_LIBRARIES PInf) (@_LIBRARIES PFin) :=
  .cons ⟨rfl, I2F_puts_denotation⟩ (.cons ⟨rfl, I2F_putchar_denotation⟩ .nil)

theorem I2F_library_functions (ds : List (declaration dtyp)) :
    List.Forall₂ (prod_rel Eq I2F_function_denotation)
      (@library_functions PInf ds) (@library_functions PFin ds) := by
  unfold library_functions Libraries.Worker.library_functions
  induction selected ds with
  | nil => exact .nil
  | cons e es ih =>
    obtain ⟨name, b⟩ := e
    refine .cons ⟨rfl, ?_⟩ ih
    cases b with
    | puts => exact I2F_puts_denotation
    | putchar => exact I2F_putchar_denotation

end Vellvm.Theory.I2F.I2F_toplevel
