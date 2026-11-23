module

public import Vellvm.Types
public import Vellvm.Utils.ListUtil

@[expose] public section
namespace Vellvm.Semantics.EOU

open Vellvm.Utils.ListUtil
universe u v

inductive EOU (X : Type u) where
  | raise_error (s : IRString)
  | raise_oom (s : IRString)
  | raise_ub (s : IRString)
  | raise_ret (x : X)
  deriving DecidableEq

export EOU (raise_error raise_oom raise_ub raise_ret)

def EOU.bind {A : Type u} {B : Type v} (m : EOU A) (k : A → EOU B) : EOU B :=
  match m with
  | .raise_error s => .raise_error s
  | .raise_oom s => .raise_oom s
  | .raise_ub s => .raise_ub s
  | .raise_ret a => k a

instance EOU_monad : Monad EOU where
  pure := raise_ret
  bind := EOU.bind

theorem EOU_bind_ret_inv {A : Type u} {B : Type v} (m : EOU A) (k : A → EOU B) (v : B) :
    EOU.bind m k = raise_ret v → ∃ a, m = raise_ret a ∧ k a = raise_ret v := by
  cases m <;> simp [EOU.bind]

theorem map_monad_EOU_Forall2 {A : Type u} {B : Type v} (f : A → EOU B) (l : List A) (res : List B) :
    map_monad f l = raise_ret res ↔ List.Forall₂ (fun a b ↦ f a = raise_ret b) l res := by
  induction l generalizing res with
  | nil => cases res <;> simp [map_monad, pure]
  | cons x xs ih =>
    constructor
    · intro h
      obtain ⟨y, hy, h⟩ := EOU_bind_ret_inv (f x) _ res h
      obtain ⟨ys, hys, h⟩ := EOU_bind_ret_inv (map_monad f xs) _ res h
      change raise_ret (y :: ys) = raise_ret res at h
      cases h
      exact .cons hy ((ih ys).mp hys)
    · intro h
      cases h with
      | cons hy hys =>
        rw [map_monad, hy]
        change EOU.bind (map_monad f xs) _ = _
        rw [(ih _).mpr hys]
        rfl

theorem map_monad_EOU_success (A : Type u) (B : Type v) (f : A → EOU B) (l : List A) (b : List B) :
    map_monad f l = raise_ret b → ∀ a, a ∈ l → ∃ b, f a = raise_ret b := by
  intro h
  replace h := (map_monad_EOU_Forall2 f l b).mp h
  induction h with
  | nil => simp
  | cons hx _ ih =>
    intro a ha
    rcases List.mem_cons.mp ha with rfl | ha
    · exact ⟨_, hx⟩
    · exact ih a ha

def option_ub {X : Type u} (s : IRString) : Option X → EOU X
  | none => raise_ub s
  | some x => raise_ret x

abbrev MaybePoison := Option
abbrev Pois {A : Type u} : Option A := none
abbrev NoPois {A : Type u} : A → Option A := some

def EOUP (A : Type u) := EOU (Option A)

instance EOUP_Monad : Monad EOUP where
  pure x := raise_ret (some x)
  bind m k := EOU.bind m fun
    | none => raise_ret none
    | some a => k a

def catch_pois {A : Type u} {Z : Type v} (z_default : Z) (c : EOUP A) (k : A → EOU Z) : EOU Z :=
  EOU.bind c fun
    | none => raise_ret z_default
    | some v => k v

theorem map_monad_cons_EOUP {A : Type u} {B : Type v} (f : A → EOUP B) (x : A) (xs : List A) :
    map_monad (m := EOUP) f (x :: xs) =
      (f x >>= fun y ↦ map_monad (m := EOUP) f xs >>= fun ys ↦ pure (y :: ys) : EOUP (List B)) := rfl

theorem map_monad_EOUP_pois_head {A : Type u} {B : Type v} (f : A → EOUP B) (x : A) (rest : List A) :
    f x = raise_ret none → map_monad (m := EOUP) f (x :: rest) = raise_ret none := by
  intro h
  rw [map_monad, h]
  rfl

theorem seq_map_monad_acc_go_eq {A : Type u} (f : Nat → EOU A) (len : Nat) (acc : List A) (cur : Nat) :
    seq_map_monad_acc_go f acc cur len = (map_monad f (Nseq cur len) >>= fun bs ↦ pure (acc.reverseAux bs)) := by
  induction len generalizing acc cur with
  | zero => rfl
  | succ n ih =>
    simp only [seq_map_monad_acc_go, Nseq, map_monad]
    cases h : f cur <;> try rfl
    change seq_map_monad_acc_go f (_ :: acc) (cur+1) n = _
    rw [ih]
    cases map_monad f (Nseq (cur+1) n) <;> rfl

theorem seq_map_monad_acc_eq {A : Type u} (f : Nat → EOU A) (start len : Nat) :
    seq_map_monad_acc f start len = map_monad f (Nseq start len) := by
  rw [seq_map_monad_acc, seq_map_monad_acc_go_eq]
  cases map_monad f (Nseq start len) <;> rfl

end Vellvm.Semantics.EOU
