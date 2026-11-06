/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Mathlib.Algebra.Homology.HomologySequenceLemmas

/-! # Genuine extension of quasi-isomorphisms in cochain short exact sequences

The actual middle map is a quasi-isomorphism if the two outer maps are.
The proof uses the neighboring homology exact sequences and both four lemmas;
no extension or weak-equivalence axiom is an input.


Implementation provenance:
`Quillen/Aglib/Algebra/Homology/CochainComplex/QuasiIsoExtension.lean` at Quillen commit
`c561118b7795eb9780be9ed391c3251d6a4d0afd`. Original maps, bounds, hypotheses
and independent object/hom universe parameters are retained.
-/
@[expose] public section


noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits CategoryTheory.ComposableArrows
open HomologicalComplex HomologicalComplex.HomologySequence
universe u v

namespace CochainComplex
variable {A : Type u} [Category.{v} A] [Abelian A]
  {S T : ShortComplex (CochainComplex A ℤ)} (φ : S ⟶ T)
  (hS : S.ShortExact) (hT : T.ShortExact)

include hS hT in
/-- The actual middle vertical map of short exact cochain sequences is a
quasi-isomorphism whenever the two actual outer maps are quasi-isomorphisms. -/
theorem quasiIso_middle_of_shortExact (h₁ : QuasiIso φ.τ₁) (h₃ : QuasiIso φ.τ₃) :
    QuasiIso φ.τ₂ := by
  let : QuasiIso φ.τ₁ := h₁
  let : QuasiIso φ.τ₃ := h₃
  rw [quasiIso_iff]
  intro n
  rw [quasiIsoAt_iff_isIso_homologyMap]
  have hm : Mono (homologyMap φ.τ₂ n) := by
    apply Abelian.mono_of_epi_of_mono_of_mono
      ((δ₀Functor ⋙ δ₀Functor).map (mapComposableArrows₅ φ hS hT (n - 1) n (by simp)))
    · exact (composableArrows₅_exact hS (n - 1) n (by simp)).δ₀.δ₀
    · exact (composableArrows₅_exact hT (n - 1) n (by simp)).δ₀.δ₀
    · change Epi (homologyMap φ.τ₃ (n - 1))
      infer_instance
    · change Mono (homologyMap φ.τ₁ n)
      infer_instance
    · change Mono (homologyMap φ.τ₃ n)
      infer_instance
  have he : Epi (homologyMap φ.τ₂ n) := by
    apply Abelian.epi_of_epi_of_epi_of_mono
      ((δlastFunctor ⋙ δlastFunctor).map (mapComposableArrows₅ φ hS hT n (n + 1) (by simp)))
    · exact (composableArrows₅_exact hS n (n + 1) (by simp)).δlast.δlast
    · exact (composableArrows₅_exact hT n (n + 1) (by simp)).δlast.δlast
    · change Epi (homologyMap φ.τ₁ n)
      infer_instance
    · change Epi (homologyMap φ.τ₃ n)
      infer_instance
    · change Mono (homologyMap φ.τ₁ (n + 1))
      infer_instance
  exact isIso_of_mono_of_epi _

end CochainComplex
