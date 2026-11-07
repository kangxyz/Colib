/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

import Colib.RingTheory.KTheory.MilnorK.Symbols.Transport

universe u v w

variable {k : Type u} {K : Type v} {L : Type w} [Field k] [Field K] [Field L] {n : ℕ}

-- All three field universes are independent, including in composition.
example (φ : k →+* K) (ψ : K →+* L) :
    milnorKTheoryMap (ψ.comp φ) n =
      (milnorKTheoryMap ψ n).comp (milnorKTheoryMap φ n) := milnorKTheoryMap_comp φ ψ

-- The additive API is the existing forgetful operation on the one linear map.
example (φ : k →+* K) (a : Fin n → kˣ) :
    (milnorKTheoryMap φ n).toAddMonoidHom (milnorKTupleSymbol a) =
      milnorKTupleSymbol (Units.map φ.toMonoidHom ∘ a) := milnorKTheoryMap_tupleSymbol φ a

example (φ : k →+* K) :
    milnorKTheoryMap φ 0 (milnorKTupleSymbol (Fin.elim0 : Fin 0 → kˣ)) =
      milnorKTupleSymbol (Fin.elim0 : Fin 0 → Kˣ) := by
  rw [milnorKTheoryMap_tupleSymbol]
  congr 1
  exact funext fun i => Fin.elim0 i

-- Compatibility is equality of the actual maps, not a second-model comparison.
example {k' : Type u} [Field k'] (φ : k →+* k') :
    milnorKTheoryMap φ n = (milnorKTransport φ n).toIntLinearMap :=
  milnorKTheoryMap_eq_transport φ

example : milnorKTheoryMap (RingHom.id k) n = LinearMap.id := milnorKTheoryMap_id
