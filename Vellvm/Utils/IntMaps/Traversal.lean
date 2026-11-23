module

public import Vellvm.Utils.IntMaps.Operations
public import Mathlib.Control.Traversable.Basic

@[expose] public section
namespace Vellvm.Utils.IntMaps

/-- ExtLib keeps the binary operation and neutral element separate from their laws. -/
structure FoldMonoid (M : Type u) where
  monoid_plus : M → M → M
  monoid_unit : M

class Foldable.{u,v,w} (T : Type u) (A : Type v) where
  fold_mon : ∀ (M : Type w) {_ : FoldMonoid M}, (A → M) → T → M

def traverseWithKeyRaw {F : Type v → Type w} [Applicative F] {A : Type u} {B : Type v}
    (f : Int → A → F B) : IM.Raw.tree A → F (IM.Raw.tree B)
  | .Leaf => pure .Leaf
  | .Node l k v r h =>
    if h = 1 then (fun v' ↦ IM.Raw.Node .Leaf k v' .Leaf 1) <$> f k v
    else (fun l' v' r' ↦ IM.Raw.Node l' k v' r' h) <$> traverseWithKeyRaw f l <*> f k v <*>
      traverseWithKeyRaw f r

instance Traversable_RawIntMap : Traversable IM.Raw.tree.{u} where
  map f := traverseWithKeyRaw (F := Id) (fun _ x ↦ f x)
  traverse f := traverseWithKeyRaw (fun _ ↦ f)

def traverseWithKey {F : Type v → Type w} [Applicative F] {A : Type u} {B : Type v}
    (f : Int → A → F B) (m : IM.t A) : F (IM.t B) :=
  IM.fold (fun k v acc ↦ add k <$> f k v <*> acc) m (pure empty)

instance Traversable_IntMap : Traversable (fun A : Type u ↦ IntMap A) where
  map f := traverseWithKey (F := Id) (fun _ x ↦ f x)
  traverse f := traverseWithKey (fun _ ↦ f)

instance Foldable_IS : Foldable.{0,0,u} IS.t Int where
  fold_mon _ m f s := IS.fold (fun k acc ↦ m.monoid_plus (f k) acc) s m.monoid_unit

instance Foldable_IM_Raw.{u,v} {A : Type u} : Foldable.{u,0,v} (IM.Raw.tree A) Int where
  fold_mon _ m f s := IM.Raw.fold (fun k _ acc ↦ m.monoid_plus (f k) acc) s m.monoid_unit

end Vellvm.Utils.IntMaps
