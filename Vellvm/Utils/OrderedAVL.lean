/-
Translated from Rocq stdlib 9.2.0, FSets/FMapAVL.v.
Copyright INRIA, CNRS and contributors. GNU Lesser General Public License Version 2.1.
-/
module

@[expose] public section
namespace Vellvm.OrderedAVL

namespace Raw

inductive tree (K : Type u) (A : Type v) where
  | Leaf
  | Node (l : tree K A) (key : K) (value : A) (r : tree K A) (height : Int)

open tree
variable {K : Type u} {A : Type v}

def height : tree K A → Int
  | Leaf => 0
  | Node _ _ _ _ h => h

def create (l : tree K A) (k : K) (v : A) (r : tree K A) :=
  Node l k v r (max (height l) (height r) + 1)

/-- The source balances at height difference 3, not 2. Raw trees may carry arbitrary heights. -/
def bal (l : tree K A) (k : K) (v : A) (r : tree K A) :=
  let hl := height l
  let hr := height r
  if hl > hr + 2 then
    match l with
    | Leaf => create l k v r
    | Node ll lk lv lr _ =>
      if height ll ≥ height lr then create ll lk lv (create lr k v r)
      else match lr with
        | Leaf => create l k v r
        | Node lrl lrk lrv lrr _ => create (create ll lk lv lrl) lrk lrv (create lrr k v r)
  else if hr > hl + 2 then
    match r with
    | Leaf => create l k v r
    | Node rl rk rv rr _ =>
      if height rr ≥ height rl then create (create l k v rl) rk rv rr
      else match rl with
        | Leaf => create l k v r
        | Node rll rlk rlv rlr _ => create (create l k v rll) rlk rlv (create rlr rk rv rr)
  else Node l k v r (max hl hr + 1)

def find [Ord K] (x : K) : tree K A → Option A
  | Leaf => none
  | Node l k v r _ => match compare x k with
    | .lt => find x l
    | .eq => some v
    | .gt => find x r

def mem [Ord K] (x : K) : tree K A → Bool
  | Leaf => false
  | Node l k _ r _ => match compare x k with
    | .lt => mem x l
    | .eq => true
    | .gt => mem x r

def add [Ord K] (x : K) (v : A) : tree K A → tree K A
  | Leaf => Node Leaf x v Leaf 1
  | Node l k old r h => match compare x k with
    | .lt => bal (add x v l) k old r
    | .eq => Node l k v r h
    | .gt => bal l k old (add x v r)

def remove_min : tree K A → K → A → tree K A → tree K A × (K × A)
  | Leaf, k, v, r => (r, k, v)
  | Node ll lk lv lr _, k, v, r =>
    let (l', m) := remove_min ll lk lv lr
    (bal l' k v r, m)

def merge : tree K A → tree K A → tree K A
  | Leaf, r => r
  | l, Leaf => l
  | l, Node rl k v rr _ =>
    let (r', k', v') := remove_min rl k v rr
    bal l k' v' r'

def remove [Ord K] (x : K) : tree K A → tree K A
  | Leaf => Leaf
  | Node l k v r _ => match compare x k with
    | .lt => bal (remove x l) k v r
    | .eq => merge l r
    | .gt => bal l k v (remove x r)

def elements_aux (acc : List (K × A)) : tree K A → List (K × A)
  | Leaf => acc
  | Node l k v r _ => elements_aux ((k, v) :: elements_aux acc r) l

def elements := @elements_aux K A []

def fold (f : K → A → X → X) : tree K A → X → X
  | Leaf, a => a
  | Node l k v r _, a => fold f r (f k v (fold f l a))

inductive MapsTo (x : K) (a : A) : tree K A → Prop where
  | MapsRoot : x = k → MapsTo x a (Node l k a r h)
  | MapsLeft : MapsTo x a l → MapsTo x a (Node l k v r h)
  | MapsRight : MapsTo x a r → MapsTo x a (Node l k v r h)

inductive In (x : K) : tree K A → Prop where
  | InRoot : x = k → In x (Node l k v r h)
  | InLeft : In x l → In x (Node l k v r h)
  | InRight : In x r → In x (Node l k v r h)

def lt_tree [LT K] (x : K) (m : tree K A) := ∀ y, In y m → y < x
def gt_tree [LT K] (x : K) (m : tree K A) := ∀ y, In y m → x < y

inductive bst [LT K] : tree K A → Prop where
  | BSLeaf : bst Leaf
  | BSNode : bst l → bst r → lt_tree k l → gt_tree k r → bst (Node l k v r h)

theorem mapsTo_iff_in {x : K} {t : tree K A} : (∃ a, MapsTo x a t) ↔ In x t := by
  constructor
  · rintro ⟨a, h⟩
    induction h with
    | MapsRoot eq => exact .InRoot eq
    | MapsLeft _ ih => exact .InLeft ih
    | MapsRight _ ih => exact .InRight ih
  · intro h
    induction h with
    | InRoot eq => exact ⟨_, .MapsRoot eq⟩
    | InLeft _ ih => obtain ⟨a, ha⟩ := ih; exact ⟨a, .MapsLeft ha⟩
    | InRight _ ih => obtain ⟨a, ha⟩ := ih; exact ⟨a, .MapsRight ha⟩

end Raw

structure bst (K : Type u) (A : Type v) [LT K] where
  this : Raw.tree K A
  is_bst : Raw.bst this

end Vellvm.OrderedAVL
