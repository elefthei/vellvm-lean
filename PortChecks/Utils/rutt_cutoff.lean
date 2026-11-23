import PortChecks.SourceType
import Vellvm.Utils.rutt_cutoff

open CTree Coinduction Vellvm.Utils.CTreeUtil Vellvm.Utils.rutt_cutoff
open ITree (Effect)
open Vellvm.Tree (Head eqit eutt euttge)

universe u

#source_check "src/rocq/Utils/rutt_cutoff.v|Vellvm.Utils.rutt_cutoff|eq_REv_sum_prerel"
  eq_REv_sum_prerel : ∀ {E F G H : Effect.{u}} (v v' : prerel E F),
    eq_REv v v' → ∀ (w w' : prerel G H), eq_REv w w' →
    eq_REv (sum_prerel v w) (sum_prerel v' w')

#source_check "src/rocq/Utils/rutt_cutoff.v|Vellvm.Utils.rutt_cutoff|eq_REv_sum_rel_inl"
  eq_REv_sum_rel_inl : ∀ {E F G H : Effect.{u}} (v : prerel E F) (w : prerel G H),
    eq_REv (inl_prerel (sum_prerel v w)) v

#source_check "src/rocq/Utils/rutt_cutoff.v|Vellvm.Utils.rutt_cutoff|eq_REv_sum_rel_inr"
  eq_REv_sum_rel_inr : ∀ {E F G H : Effect.{u}} (v : prerel E F) (w : prerel G H),
    eq_REv (inr_prerel (sum_prerel v w)) w

#source_check "src/rocq/Utils/rutt_cutoff.v|Vellvm.Utils.rutt_cutoff|eq_RAns_sum_rel_inr"
  eq_RAns_sum_rel_inr : ∀ {E F G H : Effect.{u}} (a : postrel E F) (b : postrel G H),
    eq_RAns (inr_postrel (sum_postrel a b)) b

#source_check "src/rocq/Utils/rutt_cutoff.v|Vellvm.Utils.rutt_cutoff|ruttcF_ind"
  ruttcF_ind : ∀ {E F B : Effect.{u}} {X Y : Type u} (L : pred1 E) (K : pred1 F) (V : prerel E F) (A : postrel E F) (Q : X → Y → Prop) (C : Rel (CTree E B X) (CTree F B Y)) (P : Head E B X → Head F B Y → Prop),
    (∀ x y, Q x y → P (.ret x) (.ret y)) →
    (∀ t s, C t s → P (.guard t) (.guard s)) →
    (∀ e f k l, V e f → (∀ a b, A e a f b → C (k a) (l b)) → P (.vis e k) (.vis f l)) →
    (∀ (t : CTree E B X) s, ruttcF L K V A Q C t.unfold s → P t.unfold s → P (.guard t) s) →
    (∀ t (s : CTree F B Y), ruttcF L K V A Q C t s.unfold → P t s.unfold → P t (.guard s)) →
    (∀ e k s, L e → P (.vis e k) s) → (∀ f k t, K f → P t (.vis f k)) →
    P .stuck .stuck → (∀ t s, C t s → P (.step t) (.step s)) →
    (∀ c k l, (∀ a, C (k a) (l a)) → P (.br c k) (.br c l)) →
    ∀ l r, ruttcF L K V A Q C l r → P l r

#source_check "src/rocq/Utils/rutt_cutoff.v|Vellvm.Utils.rutt_cutoff|ruttcF_sind"
  ruttcF_sind : ∀ {E F B : Effect.{u}} {X Y : Type u} (L : pred1 E) (K : pred1 F) (V : prerel E F) (A : postrel E F) (Q : X → Y → Prop) (C : Rel (CTree E B X) (CTree F B Y)) (P : Head E B X → Head F B Y → Prop),
    (∀ x y, Q x y → P (.ret x) (.ret y)) →
    (∀ t s, C t s → P (.guard t) (.guard s)) →
    (∀ e f k l, V e f → (∀ a b, A e a f b → C (k a) (l b)) → P (.vis e k) (.vis f l)) →
    (∀ (t : CTree E B X) s, ruttcF L K V A Q C t.unfold s → P t.unfold s → P (.guard t) s) →
    (∀ t (s : CTree F B Y), ruttcF L K V A Q C t s.unfold → P t s.unfold → P t (.guard s)) →
    (∀ e k s, L e → P (.vis e k) s) → (∀ f k t, K f → P t (.vis f k)) →
    P .stuck .stuck → (∀ t s, C t s → P (.step t) (.step s)) →
    (∀ c k l, (∀ a, C (k a) (l a)) → P (.br c k) (.br c l)) →
    ∀ l r, ruttcF L K V A Q C l r → P l r

#source_check "src/rocq/Utils/rutt_cutoff.v|Vellvm.Utils.rutt_cutoff|ruttc_mono"
  ruttc_mono : ∀ {E F B : Effect.{u}} {X Y : Type u} (L : pred1 E) (K : pred1 F) (V : prerel E F) (A : postrel E F) (Q : X → Y → Prop) (C D : Rel (CTree E B X) (CTree F B Y)),
    C ≤ D → (ruttc_mon (B := B) L K V A Q) C ≤ (ruttc_mon (B := B) L K V A Q) D

#source_check "src/rocq/Utils/rutt_cutoff.v|Vellvm.Utils.rutt_cutoff|ruttc_to_mon_obs"
  ruttc_to_mon_obs : ∀ {E F B : Effect.{u}} {X Y : Type u} (L : pred1 E) (K : pred1 F) (V : prerel E F) (A : postrel E F) (Q : X → Y → Prop) (C : Rel (CTree E B X) (CTree F B Y)) (t : CTree E B X) (s : CTree F B Y),
    ruttcF L K V A Q C t.unfold s.unfold = (ruttc_mon (B := B) L K V A Q) C t s

#source_check "src/rocq/Utils/rutt_cutoff.v|Vellvm.Utils.rutt_cutoff|ruttc_to_mon_go"
  ruttc_to_mon_go : ∀ {E F B : Effect.{u}} {X Y : Type u} (L : pred1 E) (K : pred1 F) (V : prerel E F) (A : postrel E F) (Q : X → Y → Prop) (C : Rel (CTree E B X) (CTree F B Y)) (l : Head E B X) (r : Head F B Y),
    ruttcF L K V A Q C l r = (ruttc_mon (B := B) L K V A Q) C (.fold l) (.fold r)

#source_check "src/rocq/Utils/rutt_cutoff.v|Vellvm.Utils.rutt_cutoff|euttge_proper_ruttcChain"
  euttge_proper_ruttcChain : ∀ {E F B : Effect.{u}} {X Y : Type u} {L : pred1 E} {K : pred1 F} {V : prerel E F} {A : postrel E F} {Q : X → Y → Prop} (C : Rel (CTree E B X) (CTree F B Y)) (hc : Chain (ruttc_mon (B := B) L K V A Q) C) (t t' : CTree E B X),
    euttge Eq t t' → ∀ (s s' : CTree F B Y), euttge Eq s s' →
    C t' s' → C t s

#source_check "src/rocq/Utils/rutt_cutoff.v|Vellvm.Utils.rutt_cutoff|euttge_proper_ruttcChain_mon"
  euttge_proper_ruttcChain_mon : ∀ {E F B : Effect.{u}} {X Y : Type u} {L : pred1 E} {K : pred1 F} {V : prerel E F} {A : postrel E F} {Q : X → Y → Prop} (C : Rel (CTree E B X) (CTree F B Y)) (hc : Chain (ruttc_mon (B := B) L K V A Q) C) (t t' : CTree E B X),
    euttge Eq t t' → ∀ (s s' : CTree F B Y), euttge Eq s s' →
    (ruttc_mon (B := B) L K V A Q) C t' s' → (ruttc_mon (B := B) L K V A Q) C t s

#source_check "src/rocq/Utils/rutt_cutoff.v|Vellvm.Utils.rutt_cutoff|euttge_proper_ruttc"
  euttge_proper_ruttc : ∀ {E F B : Effect.{u}} {X Y : Type u} {L : pred1 E} {K : pred1 F} {V : prerel E F} {A : postrel E F} {Q : X → Y → Prop}  (t t' : CTree E B X),
    euttge Eq t t' → ∀ (s s' : CTree F B Y), euttge Eq s s' →
    ruttc L K V A Q t' s' → ruttc L K V A Q t s

#source_check "src/rocq/Utils/rutt_cutoff.v|Vellvm.Utils.rutt_cutoff|ruttc_bind_chain"
  ruttc_bind_chain : ∀ {E F B : Effect.{u}} {X Y : Type u} (L : pred1 E) (K : pred1 F) (V : prerel E F) (A : postrel E F) (Q : X → Y → Prop) (C : Rel (CTree E B X) (CTree F B Y)) (hc : Chain (ruttc_mon (B := B) L K V A Q) C) (U W : Type u) (P : U → W → Prop)
    (t : CTree E B U) (s : CTree F B W) (k : U → CTree E B X) (l : W → CTree F B Y),
    ruttc L K V A P t s → (∀ x y, P x y → C (k x) (l y)) →
    C (t >>= k) (s >>= l)

#source_check "src/rocq/Utils/rutt_cutoff.v|Vellvm.Utils.rutt_cutoff|ruttc_bind_bchain"
  ruttc_bind_bchain : ∀ {E F B : Effect.{u}} {X Y : Type u} (L : pred1 E) (K : pred1 F) (V : prerel E F) (A : postrel E F) (Q : X → Y → Prop) (C : Rel (CTree E B X) (CTree F B Y)) (hc : Chain (ruttc_mon (B := B) L K V A Q) C) (U W : Type u) (P : U → W → Prop)
    (t : CTree E B U) (s : CTree F B W) (k : U → CTree E B X) (l : W → CTree F B Y),
    ruttc L K V A P t s → (∀ x y, P x y → (ruttc_mon (B := B) L K V A Q) C (k x) (l y)) →
    (ruttc_mon (B := B) L K V A Q) C (t >>= k) (s >>= l)

#source_check "src/rocq/Utils/rutt_cutoff.v|Vellvm.Utils.rutt_cutoff|ruttc_Proper_R"
  ruttc_Proper_R : ∀ {E F B : Effect.{u}} {X Y : Type u} (L L' : pred1 E),
    eqp1 L L' → ∀ K K', eqp1 K K' → ∀ V V', eq_REv V V' → ∀ A A', eq_RAns A A' →
    ∀ (Q Q' : X → Y → Prop), (∀ x y, Q x y ↔ Q' x y) →
    ∀ (t t' : CTree E B X), t = t' → ∀ (s s' : CTree F B Y), s = s' →
    (ruttc L K V A Q t s ↔ ruttc L' K' V' A' Q' t' s')

#source_check "src/rocq/Utils/rutt_cutoff.v|Vellvm.Utils.rutt_cutoff|ruttc_weaken"
  ruttc_weaken : ∀ {E F B : Effect.{u}} {X Y : Type u} (L L' : pred1 E) (K K' : pred1 F) (V V' : prerel E F)
    (A A' : postrel E F) (Q Q' : X → Y → Prop),
    (∀ e, L e → L' e) → (∀ f, K f → K' f) → (∀ e f, V e f → V' e f) →
    (∀ e a f b, A' e a f b → A e a f b) → (∀ x y, Q x y → Q' x y) →
    ∀ (t : CTree E B X) (s : CTree F B Y), ruttc L K V A Q t s → ruttc L' K' V' A' Q' t s

#source_check "src/rocq/Utils/rutt_cutoff.v|Vellvm.Utils.rutt_cutoff|ruttc_bind"
  ruttc_bind : ∀ {E F B : Effect.{u}} {X Y U W : Type u} (L : pred1 E) (K : pred1 F) (V : prerel E F) (A : postrel E F) (Q : X → Y → Prop) (P : U → W → Prop) (t : CTree E B X) (s : CTree F B Y)
    (k : X → CTree E B U) (l : Y → CTree F B W),
    ruttc L K V A Q t s → (∀ x y, Q x y → ruttc L K V A P (k x) (l y)) →
    ruttc L K V A P (t >>= k) (s >>= l)

#source_check "src/rocq/Utils/rutt_cutoff.v|Vellvm.Utils.rutt_cutoff|ruttc_ret"
  ruttc_ret : ∀ {E F B : Effect.{u}} {X Y : Type u} {L : pred1 E} {K : pred1 F} {V : prerel E F} {A : postrel E F} {Q : X → Y → Prop} (x : X) (y : Y),
    Q x y → ruttc L K V A (B := B) Q (.ret x) (.ret y)

#source_check "src/rocq/Utils/rutt_cutoff.v|Vellvm.Utils.rutt_cutoff|ruttc_trigger"
  ruttc_trigger : ∀ {E F B : Effect.{u}} {L : pred1 E} {K : pred1 F} {V : prerel E F} {A : postrel E F} (e : E.I) (f : F.I) {Q : E.O e → F.O f → Prop},
    V e f → (∀ a b, A e a f b → Q a b) →
    ruttc L K V A (B := B) Q (CTree.trigger e) (CTree.trigger f)

#source_check "src/rocq/Utils/rutt_cutoff.v|Vellvm.Utils.rutt_cutoff|ruttc_trigger_cast"
  ruttc_trigger_cast : ∀ {E F B : Effect.{u}} {X Y : Type u} {L : pred1 E} {K : pred1 F} {V : prerel E F} {A : postrel E F} {Q : X → Y → Prop} (e : E.I) (f : F.I) (he : E.O e = PEmpty) (hf : F.O f = PEmpty),
    V e f → ruttc L K V A (B := B) Q (trigger_cast' e he) (trigger_cast' f hf)

#source_check "src/rocq/Utils/rutt_cutoff.v|Vellvm.Utils.rutt_cutoff|ruttc_map_monad_gen"
  ruttc_map_monad_gen : ∀ {E F B : Effect.{u}} {X Y U W : Type u} (L : pred1 E) (K : pred1 F) (V : prerel E F) (A : postrel E F) (Q : X → Y → Prop)
    (f : U → CTree E B X) (g : W → CTree F B Y) (xs : List U) (ys : List W),
    List.Forall₂ (fun a b ↦ ruttc L K V A Q (f a) (g b)) xs ys →
    ruttc L K V A (List.Forall₂ Q) (Vellvm.Utils.ListUtil.map_monad f xs) (Vellvm.Utils.ListUtil.map_monad g ys)

#source_check "src/rocq/Utils/rutt_cutoff.v|Vellvm.Utils.rutt_cutoff|ruttc_map_monad"
  ruttc_map_monad : ∀ {E F B : Effect.{u}} {X Y U : Type u} (L : pred1 E) (K : pred1 F) (V : prerel E F) (A : postrel E F) (Q : X → Y → Prop)
    (f : U → CTree E B X) (g : U → CTree F B Y) (xs : List U),
    (∀ a, a ∈ xs → ruttc L K V A Q (f a) (g a)) →
    ruttc L K V A (List.Forall₂ Q) (Vellvm.Utils.ListUtil.map_monad f xs) (Vellvm.Utils.ListUtil.map_monad g xs)

#source_check "src/rocq/Utils/rutt_cutoff.v|Vellvm.Utils.rutt_cutoff|ruttc_iter"
  ruttc_iter : ∀ {E F B : Effect.{u}} {U W X Y : Type u} (L : pred1 E) (K : pred1 F) (V : prerel E F) (A : postrel E F) (Q : X → Y → Prop) (P : U → W → Prop)
    (f : U → CTree E B (U ⊕ X)) (g : W → CTree F B (W ⊕ Y)),
    (∀ i j, P i j → ruttc L K V A (sum_rel P Q) (f i) (g j)) → ∀ i j, P i j →
    ruttc L K V A Q (CTree.iter f i) (CTree.iter g j)

#source_check "src/rocq/Utils/rutt_cutoff.v|Vellvm.Utils.rutt_cutoff|ruttc_interp_mrec"
  ruttc_interp_mrec : ∀ {D G E F B : Effect.{u}} {X Y : Type u} (L : pred1 E) (K : pred1 F) (V : prerel E F) (J : prerel D G) (N : postrel D G) (A : postrel E F) (Q : X → Y → Prop)
    (f : (d : D.I) → CTree (D ⊕ₑ E) B (D.O d))
    (g : (d : G.I) → CTree (G ⊕ₑ F) B (G.O d)),
    (∀ d e, J d e → ruttc (sum_pred1 FF1 L) (sum_pred1 FF1 K) (sum_prerel J V) (sum_postrel N A)
      (fun x y ↦ N d x e y) (f d) (g e)) → ∀ t s,
    ruttc (sum_pred1 FF1 L) (sum_pred1 FF1 K) (sum_prerel J V) (sum_postrel N A) Q t s → ruttc L K V A Q (interp_mrec f t) (interp_mrec g s)

#source_check "src/rocq/Utils/rutt_cutoff.v|Vellvm.Utils.rutt_cutoff|ruttc_mrec"
  ruttc_mrec : ∀ {D G E F B : Effect.{u}} (L : pred1 E) (K : pred1 F) (V : prerel E F) (A : postrel E F) (J : prerel D G) (N : postrel D G)
    (f : (d : D.I) → CTree (D ⊕ₑ E) B (D.O d))
    (g : (d : G.I) → CTree (G ⊕ₑ F) B (G.O d)),
    (∀ d e, J d e → ruttc (sum_pred1 FF1 L) (sum_pred1 FF1 K) (sum_prerel J V) (sum_postrel N A)
      (fun x y ↦ N d x e y) (f d) (g e)) → ∀ d e, J d e →
    ruttc L K V A (fun x y ↦ N d x e y) (mrec f d) (mrec g e)

#source_check "src/rocq/Utils/rutt_cutoff.v|Vellvm.Utils.rutt_cutoff|ruttc_translate_inr"
  ruttc_translate_inr : ∀ {E F G H B : Effect.{u}} {X Y : Type u} (L : pred1 E) (K : pred1 F) (V : prerel E F) (A : postrel E F) (V' : prerel G H) (A' : postrel G H) (Q : X → Y → Prop) (t : CTree E B X) (s : CTree F B Y),
    ruttc L K V A Q t s → ruttc (sum_pred1 TT1 L) (sum_pred1 TT1 K) (sum_prerel V' V)
      (sum_postrel A' A) Q (translate (inrMap G) t) (translate (inrMap H) s)

#source_check "src/rocq/Utils/rutt_cutoff.v|Vellvm.Utils.rutt_cutoff|ruttc_translate_inr'"
  ruttc_translate_inr' : ∀ {E F G H B : Effect.{u}} {X Y : Type u} (L : pred1 E) (K : pred1 F) (V : prerel E F) (A : postrel E F) (L' : pred1 (G ⊕ₑ E)) (K' : pred1 (H ⊕ₑ F))
    (V' : prerel (G ⊕ₑ E) (H ⊕ₑ F)) (A' : postrel (G ⊕ₑ E) (H ⊕ₑ F)) (Q : X → Y → Prop),
    eqp1 L' (sum_pred1 FF1 L) → eqp1 K' (sum_pred1 FF1 K) →
    eq_REv (inr_prerel V') V → eq_RAns (inr_postrel A') A →
    ∀ (t : CTree E B X) (s : CTree F B Y), ruttc L K V A Q t s →
    ruttc L' K' V' A' Q (translate (inrMap G) t) (translate (inrMap H) s)

#source_check "src/rocq/Utils/rutt_cutoff.v|Vellvm.Utils.rutt_cutoff|ruttc_inv_Tau_l"
  ruttc_inv_Tau_l : ∀ {E F B : Effect.{u}} {X Y : Type u} (K : pred1 F) (L : pred1 E) (V : prerel E F) (A : postrel E F) {Q : X → Y → Prop} (t : CTree E B X) (s : CTree F B Y),
    ruttc L K V A Q t.guard s → ruttc L K V A Q t s

#source_check "src/rocq/Utils/rutt_cutoff.v|Vellvm.Utils.rutt_cutoff|ruttc_inv_Tau_r"
  ruttc_inv_Tau_r : ∀ {E F B : Effect.{u}} {X Y : Type u} (K : pred1 F) (L : pred1 E) (V : prerel E F) (A : postrel E F) {Q : X → Y → Prop} (t : CTree E B X) (s : CTree F B Y),
    ruttc L K V A Q t s.guard → ruttc L K V A Q t s

#source_check "src/rocq/Utils/rutt_cutoff.v|Vellvm.Utils.rutt_cutoff|ruttc_inv_Tau"
  ruttc_inv_Tau : ∀ {E F B : Effect.{u}} {X Y : Type u} (K : pred1 F) (L : pred1 E) (V : prerel E F) (A : postrel E F) {Q : X → Y → Prop} (t : CTree E B X) (s : CTree F B Y),
    ruttc L K V A Q t.guard s.guard → ruttc L K V A Q t s

#source_check "src/rocq/Utils/rutt_cutoff.v|Vellvm.Utils.rutt_cutoff|ruttc_flip"
  ruttc_flip : ∀ {E F B : Effect.{u}} {X Y : Type u} {L : pred1 E} {K : pred1 F} {V : prerel E F} {A : postrel E F} {Q : X → Y → Prop} (t : CTree E B X) (s : CTree F B Y),
    ruttc L K V A Q t s ↔ ruttc K L (fun f e ↦ V e f) (fun f b e a ↦ A e a f b) (fun y x ↦ Q x y) s t

#source_check "src/rocq/Utils/rutt_cutoff.v|Vellvm.Utils.rutt_cutoff|ruttc_cong_eutt_l"
  ruttc_cong_eutt_l : ∀ {E F B : Effect.{u}} {X Y : Type u} {L : pred1 E} {K : pred1 F} {V : prerel E F} {A : postrel E F} {Q : X → Y → Prop} (t t' : CTree E B X) (s : CTree F B Y),
    ruttc L K V A Q t s → eutt Eq t t' → ruttc L K V A Q t' s

#source_check "src/rocq/Utils/rutt_cutoff.v|Vellvm.Utils.rutt_cutoff|ruttc_eutt_l"
  ruttc_eutt_l : ∀ {E F B : Effect.{u}} {X Y : Type u} {K : pred1 F} {L : pred1 E} {V : prerel E F} {A : postrel E F} {Q : X → Y → Prop} (t t' : CTree E B X) (s : CTree F B Y),
    eutt Eq t t' → ruttc L K V A Q t' s → ruttc L K V A Q t s

#source_check "src/rocq/Utils/rutt_cutoff.v|Vellvm.Utils.rutt_cutoff|ruttc_eutt_r"
  ruttc_eutt_r : ∀ {E F B : Effect.{u}} {X Y : Type u} {K : pred1 F} {L : pred1 E} {V : prerel E F} {A : postrel E F} {Q : X → Y → Prop} (t : CTree E B X) (s s' : CTree F B Y),
    eutt Eq s s' → ruttc L K V A Q t s → ruttc L K V A Q t s'

#source_check "src/rocq/Utils/rutt_cutoff.v|Vellvm.Utils.rutt_cutoff|ruttc_eutt"
  ruttc_eutt : ∀ {E F B : Effect.{u}} {X Y : Type u} {L : pred1 E} {K : pred1 F} {V : prerel E F} {A : postrel E F} {Q : X → Y → Prop} (t t' : CTree E B X),
    eutt Eq t t' → ∀ (s s' : CTree F B Y), eutt Eq s s' → (ruttc L K V A Q t s ↔ ruttc L K V A Q t' s')

#source_check "src/rocq/Utils/rutt_cutoff.v|Vellvm.Utils.rutt_cutoff|ruttc_eq_itree"
  ruttc_eq_itree : ∀ {E F B : Effect.{u}} {X Y : Type u} {L : pred1 E} {K : pred1 F} {V : prerel E F} {A : postrel E F} {Q : X → Y → Prop} (t t' : CTree E B X),
    eqit Eq false false t t' → ∀ (s s' : CTree F B Y), eqit Eq false false s s' → ruttc L K V A Q t' s' → ruttc L K V A Q t s

#source_check "src/rocq/Utils/rutt_cutoff.v|Vellvm.Utils.rutt_cutoff|ruttc_trigger_cutl"
  ruttc_trigger_cutl : ∀ {E F B : Effect.{u}} {X Y : Type u} {L : pred1 E} {K : pred1 F} {V : prerel E F} {A : postrel E F} {Q : X → Y → Prop} (e : E.I) (k : E.O e → CTree E B X) (s : CTree F B Y),
    L e → ruttc L K V A Q (CTree.trigger e >>= k) s

#source_check "src/rocq/Utils/rutt_cutoff.v|Vellvm.Utils.rutt_cutoff|ruttc_trigger_cutr"
  ruttc_trigger_cutr : ∀ {E F B : Effect.{u}} {X Y : Type u} {L : pred1 E} {K : pred1 F} {V : prerel E F} {A : postrel E F} {Q : X → Y → Prop} (t : CTree E B X) (f : F.I) (k : F.O f → CTree F B Y),
    K f → ruttc L K V A Q t (CTree.trigger f >>= k)

#source_check "src/rocq/Utils/rutt_cutoff.v|Vellvm.Utils.rutt_cutoff|ruttc_interp_itree"
  ruttc_interp_itree : ∀ {E F B : Effect.{u}} {X Y : Type u} {L : pred1 E} {K : pred1 F} {V : prerel E F} {A : postrel E F} {Q : X → Y → Prop} (f : (e : E.I) → CTree E B (E.O e))
    (g : (e : F.I) → CTree F B (F.O e)),
    (∀ e, L e → eqit Eq false false (f e) (CTree.trigger e)) →
    (∀ e, K e → eqit Eq false false (g e) (CTree.trigger e)) →
    (∀ e d, V e d → ruttc L K V A (fun x y ↦ A e x d y) (f e) (g d)) →
    ∀ (t : CTree E B X) (s : CTree F B Y), ruttc L K V A Q t s → ruttc L K V A Q (interp f t) (interp g s)

#source_check "src/rocq/Utils/rutt_cutoff.v|Vellvm.Utils.rutt_cutoff|ruttc_trigger'"
  ruttc_trigger' : ∀ {E F B : Effect.{u}} {X Y : Type u} {L : pred1 E} {K : pred1 F} {V : prerel E F} {A : postrel E F} {Q : X → Y → Prop} (e : E.I) (f : F.I)
    (k : E.O e → CTree E B X) (l : F.O f → CTree F B Y),
    V e f → (∀ a b, A e a f b → ruttc L K V A Q (k a) (l b)) →
    ruttc L K V A Q (CTree.trigger e >>= k) (CTree.trigger f >>= l)
