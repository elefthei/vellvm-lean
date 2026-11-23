import PortChecks.SourceType
import Vellvm.Utils.IntMaps

open Vellvm.Utils.IntMaps
universe u

#source_check "src/rocq/Utils/IntMaps.v|Vellvm.Utils.IntMaps|IM_greatest_key_none'"
  IM_greatest_key_none' : ∀ {A : Type u} (m : IM.t A), IM.Empty m → IM_greatest_key m = none

#source_check "src/rocq/Utils/IntMaps.v|Vellvm.Utils.IntMaps|IM_greatest_key_none''"
  IM_greatest_key_none'' : ∀ {A : Type u} (m : IM.t A), IM_greatest_key m = none → IM.Empty m

#source_check "src/rocq/Utils/IntMaps.v|Vellvm.Utils.IntMaps|IM_greatest_key_none"
  IM_greatest_key_none : ∀ {A : Type u} (m : IM.t A), IM_greatest_key m = none ↔ IM.Empty m

#source_check "src/rocq/Utils/IntMaps.v|Vellvm.Utils.IntMaps|IM_greatest_key_In"
  IM_greatest_key_In : ∀ {A : Type u} (m : IM.t A) (gk : Int),
    IM_greatest_key m = some gk → IM.In gk m

#source_check "src/rocq/Utils/IntMaps.v|Vellvm.Utils.IntMaps|IM_greatest_key_In'"
  IM_greatest_key_In' : ∀ {A : Type u} (m : IM.t A) (k : IM.key), IM.In k m →
    ∃ gk, IM_greatest_key m = some gk

#source_check "src/rocq/Utils/IntMaps.v|Vellvm.Utils.IntMaps|IM_greatest_key_lt"
  IM_greatest_key_lt : ∀ {A : Type u} (m : IM.t A) (gk : Int),
    IM_greatest_key m = some gk → IM.Raw.lt_tree (1 + gk) (IM.this m)

#source_check "src/rocq/Utils/IntMaps.v|Vellvm.Utils.IntMaps|IM_raw_greatest_key_lr"
  IM_raw_greatest_key_lr : ∀ {elt : Type u} (m : IM.bst elt) (k : IM.Raw.key) (e : elt)
    (l : IM.Raw.tree elt) (t : Int) (r : IM.Raw.tree elt) (kl kr : Int),
    IM.this m = IM.Raw.Node l k e r t → IM_raw_greatest_key l = some kl →
    IM_raw_greatest_key r = some kr → kl < kr

#source_check "src/rocq/Utils/IntMaps.v|Vellvm.Utils.IntMaps|next_key_correct"
  next_key_correct : ∀ {A : Type u} (m : IM.t A) (a : Int), IM.In a m → a < next_key m
