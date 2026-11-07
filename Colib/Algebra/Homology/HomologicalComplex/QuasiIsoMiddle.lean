/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.Algebra.Homology.HomologySequenceLemmas

/-!
Adapted from `Quillen/Aglib/Algebra/Homology/HomologicalComplex/QuasiIsoMiddle.lean` at commit
`c561118b7795eb9780be9ed391c3251d6a4d0afd`, retaining the original maps.

# The middle quasi-isomorphism in a short exact sequence of complexes

The result applies to arbitrary complex shapes. At an endpoint with no adjacent
degree, the corresponding three lemma replaces the four lemma. In particular,
the proof includes degree zero of nonnegative chain complexes.
-/

@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

open CategoryTheory CategoryTheory.Limits CategoryTheory.ComposableArrows
open HomologicalComplex HomologicalComplex.HomologySequence

universe u v w

namespace HomologicalComplex

variable {A : Type u} [Category.{v} A] [Abelian A] {ι : Type w}
    {c : ComplexShape ι} {S T : ShortComplex (HomologicalComplex A c)}
    (φ : S ⟶ T) (hS : S.ShortExact) (hT : T.ShortExact)

include hS hT in
/-- In a short exact diagram of actual complexes, quasi-isomorphisms of the
outer maps imply a quasi-isomorphism of the original middle map. -/
theorem quasiIso_middle_of_shortExact
    (h₁ : QuasiIso φ.τ₁) (h₃ : QuasiIso φ.τ₃) : QuasiIso φ.τ₂ := by
  rw [quasiIso_iff]
  intro i
  rw [quasiIsoAt_iff_isIso_homologyMap]
  have hm : Mono (homologyMap φ.τ₂ i) := by
    by_cases hi : ∃ j, c.Rel j i
    · obtain ⟨j, hji⟩ := hi
      apply Abelian.mono_of_epi_of_mono_of_mono
        ((δ₀Functor ⋙ δ₀Functor).map (mapComposableArrows₅ φ hS hT j i hji))
      · exact (composableArrows₅_exact hS j i hji).δ₀.δ₀
      · exact (composableArrows₅_exact hT j i hji).δ₀.δ₀
      all_goals
        dsimp [homMk₅, homMk₄, homMk₃, homMk₂, homMk₁, homMkSucc, homMk, Precomp.map]
        infer_instance
    · have := hT.mono_f
      have hf : Mono (homologyMap T.f i) :=
        mono_homologyMap_of_mono_of_not_rel T.f i (by simpa using hi)
      apply Abelian.mono_of_mono_of_mono_of_mono (mapComposableArrows₂ φ i)
        (composableArrows₂_exact hS i)
      all_goals
        dsimp [homMk₅, homMk₄, homMk₃, homMk₂, homMk₁, homMkSucc, homMk, Precomp.map]
        infer_instance
  have he : Epi (homologyMap φ.τ₂ i) := by
    by_cases hi : ∃ j, c.Rel i j
    · obtain ⟨j, hij⟩ := hi
      apply Abelian.epi_of_epi_of_epi_of_mono
        ((δlastFunctor ⋙ δlastFunctor).map (mapComposableArrows₅ φ hS hT i j hij))
      · exact (composableArrows₅_exact hS i j hij).δlast.δlast
      · exact (composableArrows₅_exact hT i j hij).δlast.δlast
      all_goals
        dsimp [homMk₅, homMk₄, homMk₃, homMk₂, homMk₁, homMkSucc, homMk, Precomp.map]
        infer_instance
    · have := hS.epi_g
      have hg : Epi (homologyMap S.g i) :=
        epi_homologyMap_of_epi_of_not_rel S.g i (by simpa using hi)
      apply Abelian.epi_of_epi_of_epi_of_epi (mapComposableArrows₂ φ i)
        (composableArrows₂_exact hT i)
      all_goals
        dsimp [homMk₅, homMk₄, homMk₃, homMk₂, homMk₁, homMkSucc, homMk, Precomp.map]
        infer_instance
  exact isIso_of_mono_of_epi _

end HomologicalComplex
