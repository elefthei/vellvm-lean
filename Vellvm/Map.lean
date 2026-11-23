/-
Translated from ExtLib 0.13.2, Structures/Maps.v (BSD 2-Clause).
Copyright (c) 2013, Gregory M. Malecha. All rights reserved.

Redistribution and use in source and binary forms, with or without modification, are
permitted provided that the following conditions are met:
1. Redistributions of source code must retain the above copyright notice, this list of
   conditions and the following disclaimer.
2. Redistributions in binary form must reproduce the above copyright notice, this list of
   conditions and the following disclaimer in the documentation and/or other materials
   provided with the distribution.

THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS "AS IS" AND ANY EXPRESS
OR IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE IMPLIED WARRANTIES OF MERCHANTABILITY
AND FITNESS FOR A PARTICULAR PURPOSE ARE DISCLAIMED. IN NO EVENT SHALL THE COPYRIGHT HOLDER OR
CONTRIBUTORS BE LIABLE FOR ANY DIRECT, INDIRECT, INCIDENTAL, SPECIAL, EXEMPLARY, OR CONSEQUENTIAL
DAMAGES (INCLUDING, BUT NOT LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES; LOSS OF USE,
DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND ON ANY THEORY OF LIABILITY,
WHETHER IN CONTRACT, STRICT LIABILITY, OR TORT (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN
ANY WAY OUT OF THE USE OF THIS SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.
-/
module

@[expose] public section
namespace Vellvm

class Map (K : outParam (Type u)) (V : outParam (Type v)) (M : Type w) where
  empty : M
  add : K → V → M → M
  remove : K → M → M
  lookup : K → M → Option V
  union : M → M → M

class MapOk {K : Type u} {V : Type v} {M : Type w} (R : K → K → Prop) (ops : Map K V M) where
  mapsto : K → V → M → Prop
  mapsto_empty : ∀ k v, ¬mapsto k v ops.empty
  mapsto_lookup : ∀ k v m, ops.lookup k m = some v ↔ mapsto k v m
  mapsto_add_eq : ∀ m k v, mapsto k v (ops.add k v m)
  mapsto_add_neq : ∀ m k v k', ¬R k k' → ∀ v', mapsto k' v' m ↔ mapsto k' v' (ops.add k v m)
  mapsto_remove_eq : ∀ m k v, ¬mapsto k v (ops.remove k m)
  mapsto_remove_neq : ∀ m k k', ¬R k k' → ∀ v', mapsto k' v' m ↔ mapsto k' v' (ops.remove k m)

end Vellvm
