/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.RingTheory.KTheory.MilnorK.Symbols.SplitMixed
public import Colib.RingTheory.KTheory.MilnorK.Symbols.Transport

/-!
# Transport of the existing mixed span through an actual field square

An actual commuting square of field homomorphisms carries each mixed tuple to
a mixed tuple, and hence carries the existing integer span into the existing
target span. All four fields may have independent universes. No algebra
structures, comparison maps, field models, or norm statements are introduced.

This does not construct the maps or commuting squares for completed branches.
Those remain separate arithmetic obligations.

-/

@[expose] public noncomputable section

universe u v w z

variable {F : Type u} {E : Type v} {K : Type w} {L : Type z}
  [Field F] [Field E] [Field K] [Field L]

/-- A literal commuting square sends mixed classes to mixed classes, with no
finiteness, normality, separability, characteristic, or degree assumption. -/
theorem milnorKTheoryMap_mem_mixedSpan_of_comm
    (f : F →+* E) (a : F →+* K) (b : E →+* L) (g : K →+* L)
    (hsquare : b.comp f = g.comp a) (n : ℕ)
    (x : MilnorKTheory E (n + 1)) (hx : x ∈ milnorKMixedSpan f n) :
    milnorKTheoryMap b (n + 1) x ∈ milnorKMixedSpan g n := by
  change x ∈ Submodule.span ℤ _ at hx
  induction hx using Submodule.span_induction with
  | mem y hy =>
      obtain ⟨⟨c, d⟩, rfl⟩ := hy
      rw [milnorKTheoryMap_tupleSymbol]
      have htuple :
          Units.map b.toMonoidHom ∘ Fin.snoc (Units.map f.toMonoidHom ∘ c) d =
            Fin.snoc (Units.map g.toMonoidHom ∘ (Units.map a.toMonoidHom ∘ c))
              (Units.map b.toMonoidHom d) := by
        funext i
        refine Fin.lastCases ?_ (fun j => ?_) i
        · simp only [Function.comp_apply, Fin.snoc_last]
        · simp only [Function.comp_apply, Fin.snoc_castSucc]
          apply Units.ext
          exact DFunLike.congr_fun hsquare (c j : F)
      rw [htuple]
      exact milnorKTupleSymbol_snoc_mem_mixedSpan g n _ _
  | zero =>
      rw [map_zero]
      exact Submodule.zero_mem _
  | add x y hx hy ihx ihy =>
      rw [map_add]
      exact Submodule.add_mem _ ihx ihy
  | smul r x hx ih =>
      rw [map_smul]
      exact Submodule.smul_mem _ r ih

