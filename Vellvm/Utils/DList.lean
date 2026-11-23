module

public import Vellvm.Types

@[expose] public section
namespace Vellvm.Utils.DList

def DList (A : Type u) := List A → List A

def DList_to_list (dl : DList A) := dl []
def DList_append (dl₁ dl₂ : DList A) : DList A := fun xs ↦ dl₁ (dl₂ xs)
def DList_singleton (a : A) : DList A := List.cons a
def DList_cons (a : A) (dl : DList A) := DList_append (DList_singleton a) dl
def DList_empty : DList A := id
def DList_from_list (l : List A) : DList A := (l ++ ·)
def DList_map (f : A → B) (dl : DList A) : DList B := DList_from_list ((dl []).map f)

instance DList_Functor : Functor DList where map := DList_map

def DString := DList UInt8

def string_fold_left (f : A → UInt8 → A) (s : IRString) (acc : A) := s.foldl f acc
def rev_string (s : IRString) : IRString := ⟨s.data.reverse⟩
def rev_tail_rec (xs : List A) := xs.reverse
def string_of_list_ascii_tail_rec (s : List UInt8) : IRString := ⟨s.toArray⟩
def list_ascii_of_string_tail_rec (s : IRString) := s.data.toList
def DString_to_string (ds : DString) := string_of_list_ascii_tail_rec (ds [])
def string_to_DString (s : IRString) : DString := DList_from_list (list_ascii_of_string_tail_rec s)
def list_to_DString (ls : List IRString) : DString :=
  ls.foldl (fun x s ↦ DList_append x (string_to_DString s)) DList_empty
def EmptyDString : DString := DList_empty
def concat_DString (sep : DString) : List DString → DString
  | [] => EmptyDString
  | [x] => x
  | x :: y :: xs => DList_append (DList_append x sep) (concat_DString sep (y :: xs))
def DList_join (ls : List (DList A)) := ls.foldl DList_append DList_empty

def example1 : DList Nat := DList_cons 1 DList_empty

end Vellvm.Utils.DList
