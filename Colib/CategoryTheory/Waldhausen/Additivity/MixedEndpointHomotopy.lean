/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Colib.KTheory.Waldhausen.Additivity.RealizationHomotopy

/-! # The actual simplicial homotopy between mixed-deformation endpoints

Implementation provenance: `Quillen/Waldhausen/Additivity/MixedEndpointHomotopy.lean`
at commit c561118b7795eb9780be9ed391c3251d6a4d0afd. Actual maps, hypotheses and
universes are retained; no subdivision realization equivalence is assumed.
-/
@[expose] public section


noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory Opposite MonoidalCategory
open SSet.MixedOrdinalCylinder
open scoped Simplicial
universe u

namespace CategoryTheory.Waldhausen.Additivity

/-- The minimum-cut cylinder, restricted to the one endpoint and followed
by the actual deformation. This retains an explicit cylinder for tracking
chosen vertices, before any cancellation of subdivision. -/
def mixedEndpointHomotopy (X Y : SimplexCategoryᵒᵖ ⥤ SSet.{u})
    (θ : outerCylinder X ⟶ Y) :
    SSet.Homotopy
      (SSet.diagonalMap (SSet.OrdinalSubdivision.horizontalEndpoint X) ≫
        SSet.diagonalMap (outerZeroSection X ≫ θ))
      (SSet.diagonalMap (outerOneSection X ≫ θ)) where
  h := SSet.diagonalMap (outerOneSection X) ▷ Δ[1] ≫
    (outerContraction X).h ≫ SSet.diagonalMap θ
  h₀ := by
    simp only [SSet.ι₀_comp_assoc, SSet.Homotopy.h₀_assoc]
    change SSet.diagonalFunctor.map
      (outerOneSection X ≫ outerProjection X ≫ outerZeroSection X ≫ θ) =
        SSet.diagonalFunctor.map
          (SSet.OrdinalSubdivision.horizontalEndpoint X ≫ outerZeroSection X ≫ θ)
    exact congrArg SSet.diagonalFunctor.map (by
      rw [← Category.assoc (outerOneSection X), outerOneSection_projection])
  h₁ := by simp only [SSet.ι₁_comp_assoc, SSet.Homotopy.h₁_assoc, Category.id_comp]; rfl
  rel := by ext n z; exact z.1.property.elim

end CategoryTheory.Waldhausen.Additivity
