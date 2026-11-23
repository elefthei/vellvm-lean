import PortChecks.SourceType
import Vellvm.Semantics.EOU

open Vellvm.Semantics.EOU Vellvm.Utils.ListUtil
universe u v

#source_check "src/rocq/Semantics/EOU.v|Vellvm.Semantics.EOU|EOU_monad"
  EOU_monad : Monad EOU.{u}

#source_check "src/rocq/Semantics/EOU.v|Vellvm.Semantics.EOU|map_monad_EOU_Forall2"
  map_monad_EOU_Forall2 : ∀ {A : Type u} {B : Type v} (f : A → EOU B) (l : List A) (res : List B),
    map_monad f l = raise_ret res ↔ List.Forall₂ (fun a b ↦ f a = raise_ret b) l res

#source_check "src/rocq/Semantics/EOU.v|Vellvm.Semantics.EOU|map_monad_EOU_success"
  map_monad_EOU_success : ∀ (A : Type u) (B : Type v) (f : A → EOU B) (l : List A) (b : List B),
    map_monad f l = raise_ret b → ∀ a, a ∈ l → ∃ b, f a = raise_ret b

#source_check "src/rocq/Semantics/EOU.v|Vellvm.Semantics.EOU|EOUP_Monad"
  EOUP_Monad : Monad EOUP.{u}

#source_check "src/rocq/Semantics/EOU.v|Vellvm.Semantics.EOU|map_monad_cons_EOUP"
  map_monad_cons_EOUP : ∀ {A : Type u} {B : Type v} (f : A → EOUP B) (x : A) (xs : List A),
    map_monad (m := EOUP) f (x :: xs) =
      (f x >>= fun y ↦ map_monad (m := EOUP) f xs >>= fun ys ↦ pure (y :: ys) : EOUP (List B))

#source_check "src/rocq/Semantics/EOU.v|Vellvm.Semantics.EOU|map_monad_EOUP_pois_head"
  map_monad_EOUP_pois_head : ∀ {A : Type u} {B : Type v} (f : A → EOUP B) (x : A) (rest : List A),
    f x = raise_ret none → map_monad (m := EOUP) f (x :: rest) = raise_ret none

#source_check "src/rocq/Semantics/EOU.v|Vellvm.Semantics.EOU|EOU_bind_ret_inv"
  EOU_bind_ret_inv : ∀ {A : Type u} {B : Type v} (m : EOU A) (k : A → EOU B) (v : B),
    EOU.bind m k = raise_ret v → ∃ a, m = raise_ret a ∧ k a = raise_ret v

#source_check "src/rocq/Semantics/EOU.v|Vellvm.Semantics.EOU|seq_map_monad_acc_go_eq"
  seq_map_monad_acc_go_eq : ∀ {A : Type u} (f : Nat → EOU A) (len : Nat) (acc : List A) (cur : Nat),
    seq_map_monad_acc_go f acc cur len = (map_monad f (Nseq cur len) >>= fun bs ↦ pure (acc.reverseAux bs))

#source_check "src/rocq/Semantics/EOU.v|Vellvm.Semantics.EOU|seq_map_monad_acc_eq"
  seq_map_monad_acc_eq : ∀ {A : Type u} (f : Nat → EOU A) (start len : Nat),
    seq_map_monad_acc f start len = map_monad f (Nseq start len)
