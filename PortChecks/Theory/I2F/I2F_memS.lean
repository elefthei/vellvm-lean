import PortChecks.SourceType
import Vellvm.Theory.I2F.I2F_memS

open Vellvm Vellvm.Semantics.Interfaces.Memory Vellvm.Semantics.EOU Vellvm.Utils.ListUtil
open Vellvm.Theory.I2F.I2F_memS Vellvm.Theory.I2F.Refinement

universe u v w x y z p q

#source_check "src/rocq/Theory/I2F/I2F_memS.v|Vellvm.Theory.I2F.I2F_memS|I2F_memS"
  I2F_memS : ∀ {S1 : Type u} {S2 : Type v} {A1 : Type w} {A2 : Type x} {P : Type} {X1 : Type y} {X2 : Type z}, (S1 → S2 → Prop) → (X1 → X2 → Prop) → (memS S1 A1 P X1) → (memS S2 A2 P X2) → Prop

#source_check "src/rocq/Theory/I2F/I2F_memS.v|Vellvm.Theory.I2F.I2F_memS|I2F_Mret"
  I2F_Mret : ∀ {S1 : Type u} {S2 : Type v} {A1 : Type w} {A2 : Type x} {P : Type} {X1 : Type y} {X2 : Type z}
    (RS : S1 → S2 → Prop) (RR : X1 → X2 → Prop) (a : X1) (b : X2),
    RR a b → (@I2F_memS S1 S2 A1 A2 P X1 X2 RS RR) (Mret a) (Mret b)

#source_check "src/rocq/Theory/I2F/I2F_memS.v|Vellvm.Theory.I2F.I2F_memS|I2F_Merr"
  I2F_Merr : ∀ {S1 : Type u} {S2 : Type v} {A1 : Type w} {A2 : Type x} {P : Type} {X1 : Type y} {X2 : Type z}
    (RS : S1 → S2 → Prop) (RR : X1 → X2 → Prop) (s t : IRString),
    (@I2F_memS S1 S2 A1 A2 P X1 X2 RS RR) (Merr s) (Merr t)

#source_check "src/rocq/Theory/I2F/I2F_memS.v|Vellvm.Theory.I2F.I2F_memS|I2F_Mub_l"
  I2F_Mub_l : ∀ {S1 : Type u} {S2 : Type v} {A1 : Type w} {A2 : Type x} {P : Type} {X1 : Type y} {X2 : Type z}
    (RS : S1 → S2 → Prop) (RR : X1 → X2 → Prop) (s : IRString) (m : (memS S2 A2 P X2)),
    (@I2F_memS S1 S2 A1 A2 P X1 X2 RS RR) (Mub s) m

#source_check "src/rocq/Theory/I2F/I2F_memS.v|Vellvm.Theory.I2F.I2F_memS|I2F_Moom_r"
  I2F_Moom_r : ∀ {S1 : Type u} {S2 : Type v} {A1 : Type w} {A2 : Type x} {P : Type} {X1 : Type y} {X2 : Type z}
    (RS : S1 → S2 → Prop) (RR : X1 → X2 → Prop) (m : (memS S1 A1 P X1)) (s : IRString),
    (@I2F_memS S1 S2 A1 A2 P X1 X2 RS RR) m (Moom s)

#source_check "src/rocq/Theory/I2F/I2F_memS.v|Vellvm.Theory.I2F.I2F_memS|I2F_Mget"
  I2F_Mget : ∀ {S1 : Type u} {S2 : Type v} {A1 : Type w} {A2 : Type x} {P : Type} {X1 : Type y} {X2 : Type z}
    (RS : S1 → S2 → Prop) (RR : X1 → X2 → Prop) (f : S1 → (memS S1 A1 P X1)) (g : S2 → (memS S2 A2 P X2)),
    (∀ a b, RS a b → (@I2F_memS S1 S2 A1 A2 P X1 X2 RS RR) (f a) (g b)) → (@I2F_memS S1 S2 A1 A2 P X1 X2 RS RR) (Mget f) (Mget g)

#source_check "src/rocq/Theory/I2F/I2F_memS.v|Vellvm.Theory.I2F.I2F_memS|I2F_Mput"
  I2F_Mput : ∀ {S1 : Type u} {S2 : Type v} {A1 : Type w} {A2 : Type x} {P : Type} {X1 : Type y} {X2 : Type z}
    (RS : S1 → S2 → Prop) (RR : X1 → X2 → Prop) (a : S1) (b : S2) (f : Unit → (memS S1 A1 P X1)) (g : Unit → (memS S2 A2 P X2)),
    RS a b → (@I2F_memS S1 S2 A1 A2 P X1 X2 RS RR) (f ()) (g ()) → (@I2F_memS S1 S2 A1 A2 P X1 X2 RS RR) (Mput a f) (Mput b g)

#source_check "src/rocq/Theory/I2F/I2F_memS.v|Vellvm.Theory.I2F.I2F_memS|I2F_Mchoose"
  I2F_Mchoose : ∀ {S1 : Type u} {S2 : Type v} {A1 : Type w} {A2 : Type x} {P : Type} {X1 : Type y} {X2 : Type z}
    (RS : S1 → S2 → Prop) (RR : X1 → X2 → Prop) (c : memC) (f : @memCType P c → (memS S1 A1 P X1)) (g : @memCType P c → (memS S2 A2 P X2)),
    (∀ a, (@I2F_memS S1 S2 A1 A2 P X1 X2 RS RR) (f a) (g a)) → (@I2F_memS S1 S2 A1 A2 P X1 X2 RS RR) (Mchoose c f) (Mchoose c g)

#source_check "src/rocq/Theory/I2F/I2F_memS.v|Vellvm.Theory.I2F.I2F_memS|I2F_memS_ind"
  I2F_memS_ind : ∀ {S1 : Type u} {S2 : Type v} {A1 : Type w} {A2 : Type x} {P : Type} {X1 : Type y} {X2 : Type z}
    {RS : S1 → S2 → Prop} {RR : X1 → X2 → Prop} (Q : (memS S1 A1 P X1) → (memS S2 A2 P X2) → Prop),
    (∀ a b, RR a b → Q (Mret a) (Mret b)) →
    (∀ s t, Q (Merr s) (Merr t)) → (∀ s m, Q (Mub s) m) → (∀ m s, Q m (Moom s)) →
    (∀ f g, (∀ a b, RS a b → (@I2F_memS S1 S2 A1 A2 P X1 X2 RS RR) (f a) (g b)) → (∀ a b, RS a b → Q (f a) (g b)) → Q (Mget f) (Mget g)) →
    (∀ a b f g, RS a b → (@I2F_memS S1 S2 A1 A2 P X1 X2 RS RR) (f ()) (g ()) → Q (f ()) (g ()) → Q (Mput a f) (Mput b g)) →
    (∀ c f g, (∀ a, (@I2F_memS S1 S2 A1 A2 P X1 X2 RS RR) (f a) (g a)) → (∀ a, Q (f a) (g a)) → Q (Mchoose c f) (Mchoose c g)) →
    ∀ {m n}, (@I2F_memS S1 S2 A1 A2 P X1 X2 RS RR) m n → Q m n

#source_check "src/rocq/Theory/I2F/I2F_memS.v|Vellvm.Theory.I2F.I2F_memS|I2F_memS_sind"
  I2F_memS_sind : ∀ {S1 : Type u} {S2 : Type v} {A1 : Type w} {A2 : Type x} {P : Type} {X1 : Type y} {X2 : Type z}
    {RS : S1 → S2 → Prop} {RR : X1 → X2 → Prop} (Q : (memS S1 A1 P X1) → (memS S2 A2 P X2) → Prop),
    (∀ a b, RR a b → Q (Mret a) (Mret b)) →
    (∀ s t, Q (Merr s) (Merr t)) → (∀ s m, Q (Mub s) m) → (∀ m s, Q m (Moom s)) →
    (∀ f g, (∀ a b, RS a b → (@I2F_memS S1 S2 A1 A2 P X1 X2 RS RR) (f a) (g b)) → (∀ a b, RS a b → Q (f a) (g b)) → Q (Mget f) (Mget g)) →
    (∀ a b f g, RS a b → (@I2F_memS S1 S2 A1 A2 P X1 X2 RS RR) (f ()) (g ()) → Q (f ()) (g ()) → Q (Mput a f) (Mput b g)) →
    (∀ c f g, (∀ a, (@I2F_memS S1 S2 A1 A2 P X1 X2 RS RR) (f a) (g a)) → (∀ a, Q (f a) (g a)) → Q (Mchoose c f) (Mchoose c g)) →
    ∀ {m n}, (@I2F_memS S1 S2 A1 A2 P X1 X2 RS RR) m n → Q m n

#source_check "src/rocq/Theory/I2F/I2F_memS.v|Vellvm.Theory.I2F.I2F_memS|I2F_memS_mono"
  I2F_memS_mono : ∀ {S1 : Type u} {S2 : Type v} {A1 : Type w} {A2 : Type x} {P : Type} {X1 : Type y} {X2 : Type z}
    (RS : S1 → S2 → Prop) (RR RR' : X1 → X2 → Prop) (m : (memS S1 A1 P X1)) (n : (memS S2 A2 P X2)),
    (∀ a b, RR a b → RR' a b) → (@I2F_memS S1 S2 A1 A2 P X1 X2 RS RR) m n → I2F_memS RS RR' m n

#source_check "src/rocq/Theory/I2F/I2F_memS.v|Vellvm.Theory.I2F.I2F_memS|I2F_memS_lift"
  I2F_memS_lift : ∀ {S1 : Type u} {S2 : Type v} {A1 : Type w} {A2 : Type x} {P : Type} {X1 : Type y} {X2 : Type z}
    (RS : S1 → S2 → Prop) (RR : X1 → X2 → Prop) (m : EOU X1) (n : EOU X2), I2F_EOU RR m n → (@I2F_memS S1 S2 A1 A2 P X1 X2 RS RR) (lift m) (lift n)

#source_check "src/rocq/Theory/I2F/I2F_memS.v|Vellvm.Theory.I2F.I2F_memS|I2F_memS_bind"
  I2F_memS_bind : ∀ {S1 : Type u} {S2 : Type v} {A1 : Type w} {A2 : Type x} {P : Type} {X1 : Type y} {X2 : Type z} {Y1 : Type p} {Y2 : Type q}
    (RS : S1 → S2 → Prop) (RX : X1 → X2 → Prop) (RY : Y1 → Y2 → Prop) (m : (memS S1 A1 P X1)) (n : (memS S2 A2 P X2))
    (f : X1 → memS S1 A1 P Y1) (g : X2 → memS S2 A2 P Y2),
    I2F_memS RS RX m n → (∀ a b, RX a b → I2F_memS RS RY (f a) (g b)) →
    I2F_memS RS RY (memS_bind m f) (memS_bind n g)

#source_check "src/rocq/Theory/I2F/I2F_memS.v|Vellvm.Theory.I2F.I2F_memS|I2F_memS_get"
  I2F_memS_get : ∀ {S1 : Type u} {S2 : Type v} {A1 : Type w} {A2 : Type x} {P : Type}
    (RS : S1 → S2 → Prop), @I2F_memS S1 S2 A1 A2 P S1 S2 RS RS Vellvm.Semantics.Interfaces.Memory.get Vellvm.Semantics.Interfaces.Memory.get

#source_check "src/rocq/Theory/I2F/I2F_memS.v|Vellvm.Theory.I2F.I2F_memS|I2F_memS_put"
  I2F_memS_put : ∀ {S1 : Type u} {S2 : Type v} {A1 : Type w} {A2 : Type x} {P : Type}
    (RS : S1 → S2 → Prop) (a : S1) (b : S2), RS a b → @I2F_memS S1 S2 A1 A2 P Unit Unit RS (fun _ _ ↦ True) (put a) (put b)

#source_check "src/rocq/Theory/I2F/I2F_memS.v|Vellvm.Theory.I2F.I2F_memS|I2F_memS_next_key"
  I2F_memS_next_key : ∀ {S1 : Type u} {S2 : Type v} {A1 : Type w} {A2 : Type x} {P : Type}
    (RS : S1 → S2 → Prop) (size align : Nat), @I2F_memS S1 S2 A1 A2 P Int Int RS Eq (next_key size align) (next_key size align)

#source_check "src/rocq/Theory/I2F/I2F_memS.v|Vellvm.Theory.I2F.I2F_memS|I2F_memS_fresh_prov"
  I2F_memS_fresh_prov : ∀ {S1 : Type u} {S2 : Type v} {A1 : Type w} {A2 : Type x} {P : Type}
    (RS : S1 → S2 → Prop), @I2F_memS S1 S2 A1 A2 P P P RS Eq (fresh_prov ()) (fresh_prov ())

#source_check "src/rocq/Theory/I2F/I2F_memS.v|Vellvm.Theory.I2F.I2F_memS|I2F_memS_exposed_prov"
  I2F_memS_exposed_prov : ∀ {S1 : Type u} {S2 : Type v} {A1 : Type w} {A2 : Type x} {P : Type}
    (RS : S1 → S2 → Prop), @I2F_memS S1 S2 A1 A2 P (Option P) (Option P) RS Eq (exposed_prov ()) (exposed_prov ())

#source_check "src/rocq/Theory/I2F/I2F_memS.v|Vellvm.Theory.I2F.I2F_memS|I2F_memS_map_monad2"
  I2F_memS_map_monad2 : ∀ {S1 : Type u} {S2 : Type v} {A1 : Type w} {A2 : Type x} {P : Type} {X1 : Type y} {X2 : Type z} {Y1 : Type p} {Y2 : Type q}
    (RS : S1 → S2 → Prop) (RX : X1 → X2 → Prop) (RY : Y1 → Y2 → Prop)
    (f : X1 → memS S1 A1 P Y1) (g : X2 → memS S2 A2 P Y2),
    ∀ as bs, List.Forall₂ RX as bs →
    (∀ a b, RX a b → I2F_memS RS RY (f a) (g b)) →
    I2F_memS RS (List.Forall₂ RY) (map_monad f as) (map_monad g bs)

#source_check "src/rocq/Theory/I2F/I2F_memS.v|Vellvm.Theory.I2F.I2F_memS|I2F_memS_map_monad_acc2"
  I2F_memS_map_monad_acc2 : ∀ {S1 : Type u} {S2 : Type v} {A1 : Type w} {A2 : Type x} {P : Type} {X1 : Type y} {X2 : Type z} {Y1 : Type p} {Y2 : Type q}
    (RS : S1 → S2 → Prop) (RX : X1 → X2 → Prop) (RY : Y1 → Y2 → Prop)
    (f : X1 → memS S1 A1 P Y1) (g : X2 → memS S2 A2 P Y2),
    ∀ as bs, List.Forall₂ RX as bs →
    (∀ a b, RX a b → I2F_memS RS RY (f a) (g b)) →
    I2F_memS RS (List.Forall₂ RY) (map_monad_acc f as) (map_monad_acc g bs)

#source_check "src/rocq/Theory/I2F/I2F_memS.v|Vellvm.Theory.I2F.I2F_memS|I2F_memS_loop_monad2"
  I2F_memS_loop_monad2 : ∀ {S1 : Type u} {S2 : Type v} {A1 : Type w} {A2 : Type x} {P : Type} {X1 : Type y} {X2 : Type z}
    (RS : S1 → S2 → Prop) (RX : X1 → X2 → Prop)
    (f : X1 → memS S1 A1 P Unit) (g : X2 → memS S2 A2 P Unit),
    ∀ as bs, List.Forall₂ RX as bs →
    (∀ a b, RX a b → I2F_memS RS (fun (_ _ : Unit) ↦ True) (f a) (g b)) →
    I2F_memS RS (fun (_ _ : Unit) ↦ True) (loop_monad f as) (loop_monad g bs)
