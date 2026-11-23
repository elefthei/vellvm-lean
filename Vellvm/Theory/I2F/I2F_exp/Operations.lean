import Vellvm.Theory.I2F.I2F_exp.Unsigned
import Vellvm.Theory.I2F.I2F_exp.Values
import Vellvm.Theory.I2F.I2F_exp.Bytes
import Vellvm.Theory.I2F.I2F_exp.Freeze
import Vellvm.Theory.I2F.I2F_exp.Arithmetic
import Vellvm.Theory.I2F.Refinement.TreeLaws
import Vellvm.Semantics.Denotation.Expressions

namespace Vellvm.Theory.I2F.I2F_exp
open Vellvm Vellvm.Syntax.DynamicTypes Vellvm.Syntax.LLVMAst
open Vellvm.Semantics.DynamicValues Vellvm.Semantics.EOU Vellvm.Semantics.Denotation
open Vellvm.Semantics.Operations.Conversion Vellvm.Semantics.Operations.Gep
open Vellvm.Semantics.Operations.Select
open Vellvm.Semantics.Attributes (denote_int_syntax)
open Vellvm.Theory.I2F.Refinement
open Vellvm.Utils.ListUtil

private theorem floatIntResult (w : Positive) (z : Option Int) :
    I2F_EOU I2F_dvalue_base
      (pure (match z with | none => @DVALUE_Poison PInf | some n => @DVALUE_I PInf w (Numeric.Integers.repr n)))
      (pure (match z with | none => @DVALUE_Poison PFin | some n => @DVALUE_I PFin w (Numeric.Integers.repr n))) := by
  cases z <;> constructor <;> constructor

set_option maxHeartbeats 4000000 in
theorem I2F_convert_pure_base (cv : pure_conversion) (t u : dtyp_base)
    {v : @dvalue_base PInf} {v' : @dvalue_base PFin} :
    I2F_dvalue_base v v' → I2F_EOU I2F_dvalue_base
      (@convert_pure_base PInf cv t v u) (@convert_pure_base PFin cv t v' u) := by
  intro h
  cases cv <;> cases t <;> try exact I2F_EOU_error _ _
  all_goals cases h <;> try exact I2F_EOU_error _ _
  all_goals cases u <;> try exact I2F_EOU_error _ _
  all_goals repeat first
    | exact I2F_EOU_error _ _ | exact I2F_EOU_ret _ _ (by constructor)
    | exact floatIntResult _ _ | cases ‹floating_point_variant›
  all_goals simp only [convert_pure_base]
  all_goals repeat first
    | exact I2F_EOU_error _ _ | exact I2F_EOU_ret _ _ (by constructor)
    | exact floatIntResult _ _ | split

private theorem baseConvert (cv : pure_conversion) (t u : dtyp_base) {v w}
    (h : I2F_dvalue_base v w) :
    I2F_EOU I2F_dvalue ((@DVALUE_Base PInf) <$> @convert_pure_base PInf cv t v u)
      ((@DVALUE_Base PFin) <$> @convert_pure_base PFin cv t w u) :=
  I2F_EOU_bind _ _ (I2F_convert_pure_base cv t u h)
    fun _ _ hv ↦ .I2F_EOU_ret _ _ (.I2F_dvalue_Base hv)

theorem I2F_convert_pure (cv : pure_conversion) (t u : dtyp) {v w} (h : I2F_dvalue v w) :
    I2F_EOU I2F_dvalue (@convert_pure PInf cv t v u) (@convert_pure PFin cv t w u) := by
  cases t with
  | DTYPE_Array vec n t =>
    cases vec
    · cases h <;> exact .I2F_EOU_error _ _
    · have lanes := I2F_vector_elts n h
      cases ht : get_vector_conversion_type (.DTYPE_Array true n t) u with
      | none => simp only [convert_pure, ht]; exact .I2F_EOU_error _ _
      | some ab =>
        obtain ⟨a, b⟩ := ab
        cases hx : @vector_elts PInf n v <;> cases hy : @vector_elts PFin n w <;>
          simp only [convert_pure, ht, hx, hy] at lanes ⊢ <;>
          first | contradiction | exact I2F_EOU_error _ _ | skip
        refine I2F_EOU_bind _ _ (I2F_EOU_map_monad2 _ _ lanes (fun _ _ ↦ I2F_dvalue_to_dvalue_base)) ?_
        intro xs ys hs
        refine I2F_EOU_bind _ _ (I2F_EOU_map_monad2 _ _ hs (fun _ _ ↦ I2F_convert_pure_base cv a b)) ?_
        exact fun _ _ hz ↦ .I2F_EOU_ret _ _ (I2F_canonicalize_agg u (Forall2_map_Base hz))
  | DTYPE_Struct p ts => cases h <;> exact .I2F_EOU_error _ _
  | DTYPE_Base t =>
    cases h <;> try exact I2F_EOU_error _ _
    cases u <;> first | exact baseConvert _ _ _ ‹_› | exact I2F_EOU_error _ _

theorem I2F_gep_indexable (t : dtyp) :
    @gep_indexable PInf t = @gep_indexable PFin t := by
  rfl

theorem I2F_sequential_stride (v : Bool) (t : dtyp) :
    @sequential_stride PInf v t = @sequential_stride PFin v t := by
  rfl

theorem I2F_gep_struct_field (p : Bool) (ts : List dtyp) (n : Nat) :
    @gep_struct_field PInf p ts n = @gep_struct_field PFin p ts n := by
  rfl

theorem I2F_gep_index {v : @dvalue PInf} {v' : @dvalue PFin} :
    I2F_dvalue v v' → @gep_index PInf v = @gep_index PFin v' := by
  intro h
  cases h <;> try rfl
  case I2F_dvalue_Base h => cases h <;> first | rfl | exact congrArg some ‹I2F_Iptr _ _›

theorem I2F_gep_index_trunc_ok (u : Bool) {v : @dvalue PInf} {v' : @dvalue PFin} :
    I2F_dvalue v v' → @gep_index_trunc_ok PInf u v = @gep_index_trunc_ok PFin u v' := by
  intro h
  cases h <;> try rfl
  case I2F_dvalue_Base h => cases h <;> rfl

theorem I2F_gep_trunc_violated (flags : gep_flags) {vs : List (@dvalue PInf)} {ws : List (@dvalue PFin)} :
    List.Forall₂ I2F_dvalue vs ws → @gep_trunc_violated PInf flags vs = @gep_trunc_violated PFin flags ws := by
  intro h
  have lanes (u : Bool) : vs.all (@gep_index_trunc_ok PInf u) = ws.all (@gep_index_trunc_ok PFin u) := by
    induction h with
    | nil => rfl
    | cons hx _ ih => simp only [List.all_cons, I2F_gep_index_trunc_ok u hx, ih]
  simp only [gep_trunc_violated, lanes]

theorem I2F_gep_steps_h {vs : List (@dvalue PInf)} {ws : List (@dvalue PFin)} :
    List.Forall₂ I2F_dvalue vs ws → ∀ t : dtyp, @gep_steps_h PInf t vs = @gep_steps_h PFin t ws := by
  intro h
  induction h with
  | nil => intro t; rfl
  | cons hx _ ih =>
    intro t
    unfold gep_steps_h
    have ix := I2F_gep_index hx
    cases hx <;> (first | cases ‹I2F_dvalue_base _ _› | skip) <;> cases t <;>
      simp only [ix, ih] <;> rfl

theorem I2F_gep_steps (t : dtyp) {vs : List (@dvalue PInf)} {ws : List (@dvalue PFin)} :
    List.Forall₂ I2F_dvalue vs ws → @gep_steps PInf t vs = @gep_steps PFin t ws := by
  intro h
  cases h with
  | nil => rfl
  | cons hx ht =>
    have ix := I2F_gep_index hx
    have tailEq := I2F_gep_steps_h ht t
    cases hx <;> (first | cases ‹I2F_dvalue_base _ _› | skip) <;>
      simp only [gep_steps, ix, tailEq] <;> rfl

theorem I2F_handle_gep_ptr (flags : gep_flags) (t : dtyp) (a : PInf.PTR.ptr)
    (b : PFin.PTR.ptr) {vs ws} (ha : I2F_Addr a b) (hs : List.Forall₂ I2F_dvalue vs ws) :
    I2F_EOUP I2F_Addr (@handle_gep_ptr PInf flags t a vs) (@handle_gep_ptr PFin flags t b ws) := by
  have addr : PInf.P2I.ptr_to_int a = PFin.P2I.ptr_to_int b := ha.1
  have prov : PInf.PTR.ptr_provenance a = PFin.PTR.ptr_provenance b := ha.2
  simp only [handle_gep_ptr, I2F_gep_steps t hs, I2F_gep_trunc_violated flags hs, addr, prov]
  cases hh : @gep_steps PFin t ws with
  | raise_error _ => exact .I2F_EOUP_error _ _
  | raise_ub _ => exact .I2F_EOUP_ub _ _
  | raise_oom _ => exact .I2F_EOUP_oom _ _
  | raise_ret steps =>
    cases steps with
    | none => exact .I2F_EOUP_poison
    | some steps =>
      change I2F_EOUP _ (if _ then _ else _) (if _ then _ else _)
      have eqFlags : @gep_flags_violated PInf = @gep_flags_violated PFin := by
        have ns (xs) (addr off : Int) : @gep_nusw_ok PInf addr off xs = @gep_nusw_ok PFin addr off xs := by
          induction xs generalizing off with
          | nil => rfl
          | cons x xs ih => cases x; simp only [gep_nusw_ok, ih] <;> rfl
        have nu (xs) (addr off : Int) : @gep_nuw_ok PInf addr off xs = @gep_nuw_ok PFin addr off xs := by
          induction xs generalizing off with
          | nil => rfl
          | cons x xs ih => cases x; simp only [gep_nuw_ok, ih] <;> rfl
        funext flags addr steps
        simp only [gep_flags_violated, ns, nu] <;> rfl
      rw [eqFlags]
      cases hflag : (@gep_flags_violated PFin flags (PFin.P2I.ptr_to_int b) steps ||
          @gep_trunc_violated PFin flags ws) <;> simp only [Bool.false_eq_true, ↓reduceIte]
      · exact I2F_EOUP_fmap_NoPois _ _ _ (I2F_int_to_ptr _ _)
      · exact .I2F_EOUP_poison

theorem I2F_eval_gep (flags : gep_flags) (t : dtyp) {v vs w ws} (hv : I2F_dvalue v w)
    (hs : List.Forall₂ I2F_dvalue vs ws) :
    I2F_EOU I2F_dvalue (@eval_gep PInf flags t v vs) (@eval_gep PFin flags t w ws) := by
  cases hv <;> try exact .I2F_EOU_error _ _
  cases ‹I2F_dvalue_base _ _› <;>
    first | exact .I2F_EOU_error _ _ | exact .I2F_EOU_ret _ _ (.I2F_dvalue_Base .I2F_dvalue_Poison)
          | skip
  rename_i a b hab
  simp only [eval_gep]
  generalize hm : @handle_gep_ptr PInf flags t a vs = m
  generalize hn : @handle_gep_ptr PFin flags t b ws = n
  have h := I2F_handle_gep_ptr flags t a b hab hs
  rw [hm, hn] at h
  cases h <;>
    first | exact .I2F_EOU_ret _ _ (.I2F_dvalue_Base (.I2F_dvalue_Pointer _ _ ‹_›))
          | exact .I2F_EOU_ret _ _ (.I2F_dvalue_Base .I2F_dvalue_Poison)
          | exact .I2F_EOU_ub _ _ | exact .I2F_EOU_oom _ _ | exact .I2F_EOU_error _ _

theorem I2F_vector_index {v : @dvalue PInf} {v' : @dvalue PFin} :
    I2F_dvalue v v' → @vector_index PInf v = @vector_index PFin v' := by
  intro h
  cases h <;> try rfl
  case I2F_dvalue_Base h => cases h <;> rfl

private theorem splitView {xs ys} (i : Int) (h : List.Forall₂ I2F_dvalue xs ys) :
    (Semantics.DynamicValues.split [] i xs = none ∧ Semantics.DynamicValues.split [] i ys = none) ∨
    ∃ p x q p' y q', Semantics.DynamicValues.split [] i xs = some ((p, x), q) ∧
      Semantics.DynamicValues.split [] i ys = some ((p', y), q') ∧
      List.Forall₂ I2F_dvalue p p' ∧ I2F_dvalue x y ∧ List.Forall₂ I2F_dvalue q q' := by
  have hs := Forall2_split _ i xs ys h
  rcases hx : Semantics.DynamicValues.split [] i xs with _ | ⟨⟨p, x⟩, q⟩ <;>
    rcases hy : Semantics.DynamicValues.split [] i ys with _ | ⟨⟨p', y⟩, q'⟩ <;>
    simp only [hx, hy] at hs <;>
    first | contradiction | exact Or.inl ⟨rfl, rfl⟩ | exact Or.inr ⟨_, _, _, _, _, _, rfl, rfl, hs⟩

private theorem poison : I2F_dvalue (@DVALUE_Base PInf (@DVALUE_Poison PInf))
    (@DVALUE_Base PFin (@DVALUE_Poison PFin)) := .I2F_dvalue_Base .I2F_dvalue_Poison

local macro "elementLeaf" : tactic => `(tactic|
  first | exact I2F_EOU_error _ _ | exact I2F_EOU_ret _ _ poison)

theorem I2F_extract_element {a b a' b'} (ha : I2F_dvalue a a') (hb : I2F_dvalue b b') :
    I2F_EOU I2F_dvalue (@extract_element PInf a b) (@extract_element PFin a' b') := by
  cases ha with
  | I2F_dvalue_Base hv => cases hv <;> elementLeaf
  | I2F_dvalue_Struct => elementLeaf
  | I2F_dvalue_Array vec hv =>
    cases vec <;> try elementLeaf
    cases hv with
    | nil => elementLeaf
    | cons hx ht =>
      simp only [extract_element, I2F_vector_index hb]
      cases hidx : @vector_index PFin b' with
      | none => cases hb <;> first | elementLeaf | cases ‹I2F_dvalue_base _ _› <;> elementLeaf
      | some i =>
        rcases splitView i (.cons hx ht) with ⟨l, r⟩ | ⟨_, _, _, _, _, _, l, r, _, he, _⟩ <;>
          simp only [split_acc_eq, l, r] <;> first | elementLeaf | exact I2F_EOU_ret _ _ he

private theorem lanesView (n : Nat) {v w} (h : I2F_dvalue v w) :
    (@vector_elts PInf n v = none ∧ @vector_elts PFin n w = none) ∨
    ∃ xs ys, @vector_elts PInf n v = some xs ∧ @vector_elts PFin n w = some ys ∧ List.Forall₂ I2F_dvalue xs ys := by
  have hs := I2F_vector_elts n h
  cases hx : @vector_elts PInf n v <;> cases hy : @vector_elts PFin n w <;> simp only [hx, hy] at hs <;>
    first | contradiction | exact Or.inl ⟨rfl, rfl⟩ | exact Or.inr ⟨_, _, rfl, rfl, hs⟩

theorem I2F_insert_element (dt : dtyp) {a b c a' b' c'} (ha : I2F_dvalue a a')
    (hb : I2F_dvalue b b') (hc : I2F_dvalue c c') :
    I2F_EOU I2F_dvalue (@insert_element PInf dt a b c) (@insert_element PFin dt a' b' c') := by
  cases dt <;> try elementLeaf
  rename_i vec n t
  cases vec <;> try elementLeaf
  rcases lanesView n ha with ⟨l, r⟩ | ⟨xs, ys, l, r, hs⟩ <;>
    simp only [insert_element, l, r, I2F_vector_index hc] <;> try elementLeaf
  cases hidx : @vector_index PFin c' with
  | none => cases hc <;> first | elementLeaf | cases ‹I2F_dvalue_base _ _› <;> elementLeaf
  | some i =>
    rcases splitView i hs with ⟨l, r⟩ | ⟨_, _, _, _, _, _, l, r, hp, _, hq⟩ <;>
      simp only [split_acc_eq, l, r] <;> try elementLeaf
    exact .I2F_EOU_ret _ _ (I2F_canonicalize_agg _ (List.rel_append hp (.cons hb hq)))

private theorem getLane {xs ys} (h : List.Forall₂ I2F_dvalue xs ys) (i : Nat) :
    I2F_dvalue (xs.getD i (@DVALUE_Base PInf (@DVALUE_Poison PInf))) (ys.getD i (@DVALUE_Base PFin (@DVALUE_Poison PFin))) := by
  induction h generalizing i with
  | nil => cases i <;> exact poison
  | cons hx _ ih => cases i with | zero => exact hx | succ n => exact ih n

theorem I2F_shuffle_vector (dt : dtyp) {a b c a' b' c'} (ha : I2F_dvalue a a')
    (hb : I2F_dvalue b b') (hc : I2F_dvalue c c') :
    I2F_EOU I2F_dvalue (@shuffle_vector PInf dt a b c) (@shuffle_vector PFin dt a' b' c') := by
  cases dt <;> try elementLeaf
  rename_i vec n t
  cases vec <;> try elementLeaf
  rcases lanesView n ha with ⟨l, r⟩ | ⟨xs, ys, l, r, hs⟩ <;>
    rcases lanesView n hb with ⟨l', r'⟩ | ⟨xs', ys', l', r', hs'⟩ <;>
    cases hc <;> (first | cases ‹I2F_dvalue_base _ _› | cases ‹Bool› | skip) <;>
    simp only [shuffle_vector, l, r, l', r'] <;> try elementLeaf
  rename_i ms ns hm
  rw [hm.length_eq]
  apply I2F_EOU_ret _ _
  apply I2F_canonicalize_agg
  refine Forall2_map_rel I2F_dvalue _ _ _ ?_ _ _ hm
  intro x y h
  simp only [I2F_vector_index h]
  cases @vector_index PFin y <;> first | exact poison | exact getLane (List.rel_append hs hs') _

private theorem splitUB {xs ys} (msg : IRString) (i : Int) (h : List.Forall₂ I2F_dvalue xs ys) :
    I2F_EOU (fun l r ↦ List.Forall₂ I2F_dvalue l.1.1 r.1.1 ∧
      I2F_dvalue l.1.2 r.1.2 ∧ List.Forall₂ I2F_dvalue l.2 r.2)
      (option_ub msg (Semantics.DynamicValues.split [] i xs))
      (option_ub msg (Semantics.DynamicValues.split [] i ys)) := by
  rcases splitView i h with ⟨l, r⟩ | ⟨_, _, _, _, _, _, l, r, h⟩ <;>
    simp only [l, r, option_ub] <;> first | exact .I2F_EOU_ub _ _ | exact .I2F_EOU_ret _ _ h

theorem I2F_extract_value (dt : dtyp) {a a'} (idxs : List int_syntax) (ha : I2F_dvalue a a') :
    I2F_EOU I2F_dvalue (@extract_value PInf dt a (idxs.map denote_int_syntax))
      (@extract_value PFin dt a' (idxs.map denote_int_syntax)) := by
  generalize idxs.map denote_int_syntax = is
  induction is generalizing dt a a' with
  | nil => exact .I2F_EOU_ret _ _ ha
  | cons i is ih =>
    cases dt with
    | DTYPE_Base => exact .I2F_EOU_error _ _
    | DTYPE_Struct p ts =>
      simp only [extract_value]
      refine I2F_EOU_bind _ _ (I2F_EOU_refl _) ?_
      rintro ⟨⟨_, t⟩, _⟩ _ rfl
      cases ha <;> (first | cases ‹I2F_dvalue_base _ _› | skip) <;>
        first | exact .I2F_EOU_error _ _ | exact ih _ (I2F_poison_of_dtyp _) | skip
      refine I2F_EOU_bind _ _ (splitUB _ i ‹_›) ?_
      exact fun ⟨⟨_, _⟩, _⟩ ⟨⟨_, _⟩, _⟩ h ↦ ih _ h.2.1
    | DTYPE_Array vec n t =>
      cases vec <;> try exact I2F_EOU_error _ _
      cases ha <;> (first | cases ‹I2F_dvalue_base _ _› | cases ‹Bool› | skip) <;>
        first | exact .I2F_EOU_error _ _ | exact ih _ (I2F_poison_of_dtyp _) | skip
      refine I2F_EOU_bind _ _ (splitUB _ i ‹_›) ?_
      exact fun ⟨⟨_, _⟩, _⟩ ⟨⟨_, _⟩, _⟩ h ↦ ih _ h.2.1

private theorem insertField (dt : dtyp) {p p' q q' m m'} (hp : List.Forall₂ I2F_dvalue p p')
    (hq : List.Forall₂ I2F_dvalue q q') (h : I2F_EOU I2F_dvalue m m') :
    I2F_EOU I2F_dvalue (EOU.bind m (fun x ↦ pure (@canonicalize_agg PInf dt (p ++ x :: q))))
      (EOU.bind m' (fun y ↦ pure (@canonicalize_agg PFin dt (p' ++ y :: q')))) :=
  I2F_EOU_bind _ _ h fun _ _ hx ↦
    .I2F_EOU_ret _ _ (I2F_canonicalize_agg dt (List.rel_append hp (.cons hx hq)))

theorem I2F_insert_value (idxs : List int_syntax) (dt : dtyp) {a b a' b'}
    (ha : I2F_dvalue a a') (hb : I2F_dvalue b b') :
    I2F_EOU I2F_dvalue (@insert_value PInf dt a b (idxs.map denote_int_syntax))
      (@insert_value PFin dt a' b' (idxs.map denote_int_syntax)) := by
  generalize idxs.map denote_int_syntax = is
  induction is generalizing dt a a' with
  | nil => exact .I2F_EOU_ret _ _ hb
  | cons i is ih =>
    cases dt with
    | DTYPE_Base => exact .I2F_EOU_error _ _
    | DTYPE_Struct p ts =>
      simp only [insert_value]
      refine I2F_EOU_bind _ _ (I2F_EOU_refl _) ?_
      rintro ⟨⟨pre, t⟩, post⟩ _ rfl
      cases ha <;> (first | cases ‹I2F_dvalue_base _ _› | skip) <;> try exact .I2F_EOU_error _ _
      · exact insertField _ (Forall2_map2 _ _ _ pre fun t _ ↦ I2F_poison_of_dtyp t)
          (Forall2_map2 _ _ _ post fun t _ ↦ I2F_poison_of_dtyp t) (ih _ (I2F_poison_of_dtyp t))
      · refine I2F_EOU_bind _ _ (splitUB _ i ‹_›) ?_
        exact fun ⟨⟨_, _⟩, _⟩ ⟨⟨_, _⟩, _⟩ h ↦ insertField _ h.1 h.2.2 (ih _ h.2.1)
    | DTYPE_Array vec n t =>
      cases vec <;> try exact I2F_EOU_error _ _
      cases ha <;> (first | cases ‹I2F_dvalue_base _ _› | cases ‹Bool› | skip) <;>
        try exact .I2F_EOU_error _ _
      · refine I2F_EOU_bind _ _ (I2F_EOU_refl _) ?_
        rintro ⟨pre, post⟩ _ rfl
        have hp := I2F_poison_of_dtyp t
        exact insertField _ (Forall2_repeatN _ _ _ hp pre) (Forall2_repeatN _ _ _ hp post) (ih _ hp)
      · refine I2F_EOU_bind _ _ (splitUB _ i ‹_›) ?_
        exact fun ⟨⟨_, _⟩, _⟩ ⟨⟨_, _⟩, _⟩ h ↦ insertField _ h.1 h.2.2 (ih _ h.2.1)

theorem I2F_eval_select_base_dvalue {cond : @dvalue_base PInf} {cond' : @dvalue_base PFin}
    {a b : @dvalue PInf} {a' b' : @dvalue PFin} :
    I2F_dvalue_base cond cond' → I2F_dvalue a a' → I2F_dvalue b b' →
    I2F_EOU I2F_dvalue
      (@eval_select_base_dvalue PInf cond a b) (@eval_select_base_dvalue PFin cond' a' b') := by
  intro hc hx hy
  cases hc <;> try exact .I2F_EOU_error _ _
  case I2F_dvalue_Poison => exact .I2F_EOU_ret _ _ (.I2F_dvalue_Base .I2F_dvalue_Poison)
  case I2F_dvalue_Int sz i =>
    obtain ⟨n, hn⟩ := sz
    cases n with
    | zero => contradiction
    | succ n =>
      cases n with
      | zero =>
        simp only [eval_select_base_dvalue]
        split <;> exact .I2F_EOU_ret _ _ (by assumption)
      | succ n => exact .I2F_EOU_error _ _

private theorem selectLanes (dt : dtyp) {cs ds xs xs' ys ys'}
    (hc : List.Forall₂ I2F_dvalue_base cs ds) (hx : List.Forall₂ I2F_dvalue xs xs')
    (hy : List.Forall₂ I2F_dvalue ys ys') :
    I2F_EOU I2F_dvalue
      ((@canonicalize_agg PInf dt) <$> vec_loop (fun c p ↦ @eval_select_base_dvalue PInf c p.1 p.2)
        (cs.zip (xs.zip ys)))
      ((@canonicalize_agg PFin dt) <$> vec_loop (fun c p ↦ @eval_select_base_dvalue PFin c p.1 p.2)
        (ds.zip (xs'.zip ys'))) := by
  have hs := Forall2_combine _ _ _ _ _ _ hc (Forall2_combine _ _ _ _ _ _ hx hy)
  refine I2F_EOU_bind _ _ (I2F_EOU_vec_loop (R := I2F_dvalue) _ _ hs ?_) ?_
  · exact fun _ _ _ _ h h' ↦ I2F_eval_select_base_dvalue h h'.1 h'.2
  · exact fun _ _ h ↦ .I2F_EOU_ret _ _ (I2F_canonicalize_agg dt h)

theorem I2F_eval_select (dt : dtyp) {a b c a' b' c'} (ha : I2F_dvalue a a')
    (hb : I2F_dvalue b b') (hc : I2F_dvalue c c') :
    I2F_EOU I2F_dvalue (@eval_select PInf a dt b c) (@eval_select PFin a' dt b' c') := by
  cases ha with
  | I2F_dvalue_Struct => exact .I2F_EOU_error _ _
  | I2F_dvalue_Base h =>
    have hh := I2F_eval_select_base_dvalue h hb hc
    cases h <;> first | exact hh | exact .I2F_EOU_ret _ _ (I2F_poison_of_dtyp dt)
  | I2F_dvalue_Array vector hs =>
    cases vector <;> try elementLeaf
    cases dt <;> try elementLeaf
    rename_i vec n t
    cases vec <;> try elementLeaf
    refine I2F_EOU_bind _ _ (I2F_EOU_map_monad2 _ _ hs (fun _ _ ↦ I2F_dvalue_to_dvalue_base)) ?_
    intro cs ds hcs
    have rep := Forall2_repeat _ _ _ n poison
    cases hb <;> (first | cases ‹I2F_dvalue_base _ _› | cases ‹Bool› | skip) <;> try elementLeaf
    all_goals cases hc <;> (first | cases ‹I2F_dvalue_base _ _› | cases ‹Bool› | skip) <;>
      first | elementLeaf | exact selectLanes _ hcs (by assumption) (by assumption)

open Semantics.LLVMEvents
open Vellvm.Utils.rutt_cutoff
open CTree (CTree)

private theorem mcfgBind {X Y U W} {R : X → Y → Prop} {S : U → W → Prop} {l r}
    {f : X → @MCFGtop PInf U} {g : Y → @MCFGtop PFin W}
    (h : I2F_refine_MCFG R l r) (hk : ∀ x y, R x y → I2F_refine_MCFG S (f x) (g y)) :
    I2F_refine_MCFG S (l >>= f) (r >>= g) :=
  ruttc_bind cutUB cutOOM I2FE_MCFG I2FA_MCFG R S l r f g h hk

private theorem globalRead (i : raw_id) : I2F_refine (gread (Pa := PInf) i) (gread (Pa := PFin) i) := by
  let e := requestIn (D := @GlobalE PInf) (E := @MCFGEtop PInf) (@GlobalRead PInf i)
  let f := requestIn (D := @GlobalE PFin) (E := @MCFGEtop PFin) (@GlobalRead PFin i)
  change I2F_refine (id <$> CTree.trigger e) (id <$> CTree.trigger f)
  simp only [id_map]
  exact ruttc_trigger e f rfl fun _ _ h ↦ h

private theorem localRead (i : raw_id) : I2F_refine (lread (Pa := PInf) i) (lread (Pa := PFin) i) := by
  let e := requestIn (D := @LocalE PInf) (E := @MCFGEtop PInf) (@LocalRead PInf i)
  let f := requestIn (D := @LocalE PFin) (E := @MCFGEtop PFin) (@LocalRead PFin i)
  change I2F_refine (id <$> CTree.trigger e) (id <$> CTree.trigger f)
  simp only [id_map]
  exact ruttc_trigger e f rfl fun _ _ h ↦ h

theorem I2F_convert (cv : conversion_type) (t u : dtyp) {v w} (h : I2F_dvalue v w) :
    I2F_refine (@convert PInf cv t v u) (@convert PFin cv t w u) := by
  cases cv with
  | CONV_Pure c => exact I2F_refine_lift _ _ _ (I2F_convert_pure c t u h)
  | CONV_Bitcast =>
    simp only [convert, Semantics.Operations.Conversion.Worker.convert]
    split
    · exact ruttc_ret _ _ h
    · split
      · exact I2F_refine_lift _ _ _ (I2F_bitcast_bytes t u h)
      · exact I2F_refine_lift _ (raise_error _) (raise_error _) (.I2F_EOU_error _ _)
  | CONV_Impure c =>
    let e := requestIn (D := @MemoryE PInf) (E := @MCFGEtop PInf) (@Conv PInf c t v u)
    let f := requestIn (D := @MemoryE PFin) (E := @MCFGEtop PFin) (@Conv PFin c t w u)
    change I2F_refine (id <$> CTree.trigger e) (id <$> CTree.trigger f)
    simp only [id_map]
    exact ruttc_trigger e f ⟨rfl, rfl, h, rfl⟩ fun _ _ hv ↦ hv

private theorem raiseRelated (msg : IRString) :
    I2F_refine (Semantics.LLVMEvents.Worker.«raise» msg) (Semantics.LLVMEvents.Worker.«raise» msg) :=
  I2F_refine_lift _ (raise_error msg) (raise_error msg) (.I2F_EOU_error _ _)

local macro "bindOperand " pr:term " as " h:ident : tactic =>
  `(tactic| (refine mcfgBind $pr ?_; intro _ _ $h))

mutual
  theorem I2F_denote_exp (e : exp dtyp) (τ : Option dtyp) :
      I2F_refine (@denote_exp PInf τ e) (@denote_exp PFin τ e) := by
    cases e
    case EXP_Ident i => cases i <;> first | exact globalRead _ | exact localRead _
    case EXP_BlockAddress => exact globalRead _
    case EXP_Integer =>
      cases τ <;> first | exact raiseRelated _ | exact I2F_refine_lift _ _ _ (I2F_denote_int_syntax_as_int _ _)
    case EXP_Float =>
      cases τ <;> first | exact raiseRelated _ | exact I2F_refine_lift _ _ _ (I2F_denote_float_syntax_as_float _ _)
    case EXP_Zero_initializer =>
      cases τ <;> first | exact raiseRelated _ | exact I2F_refine_lift _ _ _ (I2F_default_dvalue_of_dtyp _)
    case EXP_Asm => exact raiseRelated _
    case EXP_Bool b => exact ruttc_ret _ _ (.I2F_dvalue_Base (.I2F_dvalue_Int _))
    case EXP_Null => exact ruttc_ret _ _ (.I2F_dvalue_Base (.I2F_dvalue_Pointer _ _ ⟨rfl, rfl⟩))
    case EXP_Undef | EXP_Poison => cases τ <;> first | exact ruttc_ret _ _ poison | exact ruttc_ret _ _ (I2F_poison_of_dtyp _)
    case EXP_Metadata md =>
      cases md <;> first
        | exact ruttc_ret _ _ (.I2F_dvalue_Base .I2F_dvalue_None)
        | exact ruttc_ret _ _ (.I2F_dvalue_Base (.I2F_dvalue_Pointer _ _ ⟨rfl, rfl⟩))
        | exact typedRelated _
    all_goals simp only [denote_exp, Semantics.Denotation.Worker.denote_exp]
    case EXP_Splat x =>
      refine mcfgBind (I2F_refine_lift _ _ _ (I2F_EOU_refl (assert_vector_typ τ))) ?_
      rintro ⟨sz, t⟩ _ rfl
      exact mcfgBind (typedRelated x) fun v w h ↦
        ruttc_ret _ _ (I2F_canonicalize_agg _ (Forall2_repeat _ v w sz h))
    case EXP_Cstring xs =>
      exact mcfgBind (typedListRelated xs) fun _ _ h ↦ ruttc_ret _ _ (.I2F_dvalue_Array false h)
    case EXP_Packed_struct xs =>
      refine mcfgBind (I2F_refine_lift _ _ _ (I2F_EOU_refl (assert_packed_struct_typ τ))) ?_
      exact fun _ _ _ ↦ mcfgBind (typedListRelated xs) fun _ _ h ↦ ruttc_ret _ _ (I2F_canonicalize_agg _ h)
    case EXP_Struct xs | EXP_Array xs | EXP_Vector xs =>
      exact mcfgBind (typedListRelated xs) fun _ _ h ↦ ruttc_ret _ _ (I2F_canonicalize_agg _ h)
    case OP_IBinop op t x y =>
      bindOperand (I2F_denote_exp x (some t)) as h1
      bindOperand (I2F_denote_exp y (some t)) as h2
      exact I2F_refine_lift _ _ _ (I2F_eval_iop op t h1 h2)
    case OP_ICmp ss op t x y =>
      bindOperand (I2F_denote_exp x (some t)) as h1
      bindOperand (I2F_denote_exp y (some t)) as h2
      exact I2F_refine_lift _ _ _ (I2F_eval_icmp ss op t h1 h2)
    case OP_FBinop op _ t x y =>
      bindOperand (I2F_denote_exp x (some t)) as h1
      bindOperand (I2F_denote_exp y (some t)) as h2
      exact I2F_refine_lift _ _ _ (I2F_eval_fop op t h1 h2)
    case OP_FCmp op _ t x y =>
      bindOperand (I2F_denote_exp x (some t)) as h1
      bindOperand (I2F_denote_exp y (some t)) as h2
      exact I2F_refine_lift _ _ _ (I2F_eval_fcmp op t h1 h2)
    case OP_Fneg _ x =>
      bindOperand (typedRelated x) as h1
      exact I2F_refine_lift _ _ _ (I2F_eval_fneg x.1 h1)
    case OP_GetElementPtr flags t p is =>
      bindOperand (typedRelated p) as h1
      bindOperand (typedListRelated is) as h2
      exact I2F_refine_lift _ _ _ (I2F_eval_gep flags t h1 h2)
    case OP_ExtractElement v i =>
      bindOperand (typedRelated v) as h1
      bindOperand (typedRelated i) as h2
      exact I2F_refine_lift _ _ _ (I2F_extract_element h1 h2)
    case OP_ShuffleVector v w m =>
      bindOperand (typedRelated v) as h1
      bindOperand (typedRelated w) as h2
      bindOperand (typedRelated m) as h3
      exact I2F_refine_lift _ _ _ (I2F_shuffle_vector v.1 h1 h2 h3)
    case OP_ExtractValue v is =>
      bindOperand (typedRelated v) as h1
      exact I2F_refine_lift _ _ _ (I2F_extract_value v.1 is h1)
    case OP_InsertValue v w is =>
      bindOperand (typedRelated v) as h1
      bindOperand (typedRelated w) as h2
      exact I2F_refine_lift _ _ _ (I2F_insert_value is v.1 h1 h2)
    case OP_Select _ c x y =>
      bindOperand (typedRelated c) as h1
      bindOperand (typedRelated x) as h2
      bindOperand (typedRelated y) as h3
      exact I2F_refine_lift _ _ _ (I2F_eval_select x.1 h1 h2 h3)
    case OP_Conversion op s x t =>
      exact mcfgBind (I2F_denote_exp x (some s)) fun _ _ h ↦ I2F_convert op s t h
    case OP_Freeze x => exact mcfgBind (typedRelated x) fun _ _ h ↦ I2F_freeze x.1 h
    case OP_InsertElement v e i =>
      refine mcfgBind (typedRelated v) fun _ _ hv ↦ ?_
      refine mcfgBind (typedRelated e) fun _ _ he ↦ ?_
      refine mcfgBind (I2F_refine_lift _ _ _ (I2F_dvalue_to_dvalue_base he)) fun _ _ he' ↦ ?_
      exact mcfgBind (typedRelated i) fun _ _ hi ↦
        I2F_refine_lift _ _ _ (I2F_insert_element v.1 hv (.I2F_dvalue_Base he') hi)
  termination_by structural e

  private theorem typedRelated (x : texp dtyp) :
      I2F_refine (Semantics.Denotation.Worker.denote_texp (M := CTree.CTree) (Pa := PInf) x)
        (Semantics.Denotation.Worker.denote_texp (M := CTree.CTree) (Pa := PFin) x) := by
    cases x with | mk t e => exact I2F_denote_exp e (some t)
  termination_by structural x

  private theorem typedListRelated (xs : List (texp dtyp)) :
      I2F_refine_MCFG (List.Forall₂ I2F_dvalue) (Semantics.Denotation.Worker.denote_texps (M := CTree.CTree) (Pa := PInf) xs)
        (Semantics.Denotation.Worker.denote_texps (M := CTree.CTree) (Pa := PFin) xs) := by
    cases xs with
    | nil => exact ruttc_ret _ _ .nil
    | cons x xs =>
      exact mcfgBind (typedRelated x) fun _ _ hx ↦ mcfgBind (typedListRelated xs) fun _ _ hxs ↦
        ruttc_ret _ _ (.cons hx hxs)
  termination_by structural xs
end

theorem I2F_denote_exp' (e : exp dtyp) (τ : Option dtyp) :
    I2F_refine_CFG I2F_dvalue (@denote_exp' PInf τ e) (@denote_exp' PFin τ e) := by
  refine ruttc_translate_inr' _ _ _ _ _ _ _ _ _ I2F_cutUB_CFG I2F_cutOOM_CFG ?_ ?_ _ _ (I2F_denote_exp e τ)
  · intro i j; constructor <;> rintro h
    · cases h; assumption
    · exact .intro _ _ h
  · intro i x j y; constructor <;> rintro h
    · cases h; assumption
    · exact .intro _ _ _ _ h

end Vellvm.Theory.I2F.I2F_exp
