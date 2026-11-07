/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

import Colib.RingTheory.KTheory.MilnorK.Symbols.MixedMap

/-!
# Consumers of native mixed-span transport

The generic square retains four independent universes. The additional consumers
cover degree one, actual generators, an actual scalar tower, and successive
commuting squares. No norm or completed-branch compatibility is assumed or claimed.

-/

noncomputable section

universe u v w z r s

variable {F : Type u} {E : Type v} {K : Type w} {L : Type z}
  [Field F] [Field E] [Field K] [Field L]

example (f : F →+* E) (a : F →+* K) (b : E →+* L) (g : K →+* L)
    (hsquare : b.comp f = g.comp a) (n : ℕ)
    (x : MilnorKTheory E (n + 1)) (hx : x ∈ milnorKMixedSpan f n) :
    milnorKTheoryMap b (n + 1) x ∈ milnorKMixedSpan g n :=
  milnorKTheoryMap_mem_mixedSpan_of_comm f a b g hsquare n x hx

example (f : F →+* E) (a : F →+* K) (b : E →+* L) (g : K →+* L)
    (hsquare : b.comp f = g.comp a)
    (x : MilnorKTheory E 1) (hx : x ∈ milnorKMixedSpan f 0) :
    milnorKTheoryMap b 1 x ∈ milnorKMixedSpan g 0 :=
  milnorKTheoryMap_mem_mixedSpan_of_comm f a b g hsquare 0 x hx

example (f : F →+* E) (a : F →+* K) (b : E →+* L) (g : K →+* L)
    (hsquare : b.comp f = g.comp a) (n : ℕ) (c : Fin n → Fˣ) (d : Eˣ) :
    milnorKTheoryMap b (n + 1)
        (milnorKTupleSymbol (Fin.snoc (Units.map f.toMonoidHom ∘ c) d)) ∈
      milnorKMixedSpan g n :=
  milnorKTheoryMap_mem_mixedSpan_of_comm f a b g hsquare n _
    (milnorKTupleSymbol_snoc_mem_mixedSpan f n c d)

example [Algebra F E] [Algebra F L] [Algebra E L] [IsScalarTower F E L]
    (n : ℕ) (x : MilnorKTheory E (n + 1))
    (hx : x ∈ milnorKMixedSpan (algebraMap F E) n) :
    milnorKTheoryMap (algebraMap E L) (n + 1) x ∈
      milnorKMixedSpan (algebraMap F L) n := by
  apply milnorKTheoryMap_mem_mixedSpan_of_comm (algebraMap F E) (RingHom.id F)
    (algebraMap E L) (algebraMap F L) _ n x hx
  simpa only [RingHom.comp_id] using (IsScalarTower.algebraMap_eq F E L).symm

example {P : Type r} {Q : Type s} [Field P] [Field Q]
    (f : F →+* E) (a : F →+* K) (b : E →+* L) (g : K →+* L)
    (c : K →+* P) (d : L →+* Q) (h : P →+* Q)
    (hfirst : b.comp f = g.comp a) (hsecond : d.comp g = h.comp c)
    (n : ℕ) (x : MilnorKTheory E (n + 1)) (hx : x ∈ milnorKMixedSpan f n) :
    milnorKTheoryMap (d.comp b) (n + 1) x ∈ milnorKMixedSpan h n := by
  rw [milnorKTheoryMap_comp, LinearMap.comp_apply]
  exact milnorKTheoryMap_mem_mixedSpan_of_comm g c d h hsecond n _
    (milnorKTheoryMap_mem_mixedSpan_of_comm f a b g hfirst n x hx)

end
