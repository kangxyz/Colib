/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

import Colib.KTheory.MilnorK.Norm.PresentationBaseChange

/-! Consumer of the actual mapped-mixed-span comparison.-/

noncomputable section

open Polynomial Stacks.Chow Stacks.Chow.MonicIrreducibleOfDegree

universe u

attribute [local instance] Ideal.Quotient.field

variable {k K : Type u} [Field k] [Field K]

example (φ : k →+* K) {d e : ℕ}
    (p : MonicIrreducibleOfDegree k d) (q : MonicIrreducibleOfDegree k e)
    (f : (k[X] ⧸ Ideal.span {poly p}) ≃ₐ[k] (k[X] ⧸ Ideal.span {poly q}))
    (hpφ : Irreducible ((poly p).map φ)) (hqφ : Irreducible ((poly q).map φ))
    (m : ℕ) (x : MilnorKTheory (k[X] ⧸ Ideal.span {poly p}) (m + 1)) :
    let pφ : MonicIrreducibleOfDegree K ((poly p).map φ).natDegree :=
      ⟨(poly p).map φ, (monic p).map φ, hpφ, rfl⟩
    let j : (k[X] ⧸ Ideal.span {poly p}) →+* (K[X] ⧸ Ideal.span {poly pφ}) :=
      AdjoinRoot.map φ (poly p) (poly pφ) dvd_rfl
    milnorKTransport j (m + 1) x ∈
        milnorKMixedSpan (algebraMap K (K[X] ⧸ Ideal.span {poly pφ})) m →
      milnorKRingMap φ (simpleMilnorNorm p (x : MilnorKRing (k[X] ⧸ Ideal.span {poly p}))) =
        milnorKRingMap φ (simpleMilnorNorm q
          (milnorKRingMap f.toRingHom (x : MilnorKRing (k[X] ⧸ Ideal.span {poly p})))) :=
  simpleMilnorNorm_map_eq_of_mapped_mem_mixedSpan φ p q f hpφ hqφ m x

end
