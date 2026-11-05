/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Colib.CategoryTheory.Waldhausen.Additivity.MixedEndpointHomotopy
public import Colib.CategoryTheory.Waldhausen.Additivity.NormalizedZeroMaps

/-! # The mixed additivity deformation has a genuinely fixed chosen zero

Implementation provenance: `Quillen/Waldhausen/Additivity/NormalizedMixedHomotopy.lean`
at commit c561118b7795eb9780be9ed391c3251d6a4d0afd. Actual maps, hypotheses and
universes are retained; no subdivision realization equivalence is assumed.
-/
@[expose] public section


noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits Opposite MonoidalCategory
open SSet.MixedOrdinalCylinder
open scoped Simplicial
universe u v

namespace CategoryTheory.Waldhausen.Additivity
variable {C D : Type u} [Category.{v} C] [Category.{v} D]
variable (V : Structure C) (W : Structure D) {F G : C ⥤ D} (a : F ⟶ G)
variable (hF : IsExact V.cof V.weq W.cof W.weq F)
variable (hG : IsExact V.cof V.weq W.cof W.weq G)
variable (hc : IsCofibrationTransformation W a V)

/-- The normalized mixed deformation with its exact identity and separated
endpoint maps. Its underlying cylinder is the actual minimum-cut cylinder. -/
def normalizedMixedEndpointHomotopy :
    SSet.Homotopy
      (SSet.diagonalMap (SSet.OrdinalSubdivision.horizontalEndpoint (bisimplicialSSet V)) ≫
        SSet.diagonalMap (normalizedIdentityMap V W a hF hG hc))
      (SSet.diagonalMap (normalizedSeparatedMap V W a hF hG hc)) where
  h := (mixedEndpointHomotopy (bisimplicialSSet V) (bisimplicialSSet W)
    (normalizedMixedMap V W a hF hG hc)).h
  h₀ := by
    rw [SSet.Homotopy.h₀, normalizedMixedMap_zero]; rfl
  h₁ := by
    rw [SSet.Homotopy.h₁, normalizedMixedMap_one]; rfl
  rel := by ext n z; exact z.1.property.elim

/-- At the actual subdivided zero vertex the entire simplicial cylinder is
literally constant. All intermediate cuts retain the same chosen zero. -/
theorem normalizedMixedEndpointHomotopy_fixed_zero :
    SSet.yonedaEquiv.symm
      (show (SSet.diagonalSSet (SSet.OrdinalSubdivision.δ.op ⋙ bisimplicialSSet V)) _⦋0⦌ from
        zeroSimplex₂ V.cof V.weq V.zero V.isZero (op (SSet.OrdinalSubdivision.δ.obj ⦋0⦌))
          (op ⦋0⦌)) ▷
          Δ[1] ≫
      (normalizedMixedEndpointHomotopy V W a hF hG hc).h =
        CartesianMonoidalCategory.fst Δ[0] Δ[1] ≫
          SSet.yonedaEquiv.symm (diagonalZeroVertex W) := by
  ext n z
  apply Subtype.ext
  exact diagram_eq_const_of_zero W _
    (fun _ ↦ normalizedPushoutFunctor_obj_zero V W a hF hG hc)

/-- The realized deformation genuinely stays at the chosen target zero. -/
theorem normalizedMixedRealizationHomotopy_fixed_zero (t : unitInterval) :
    SSet.realizationSimplicialHomotopy (normalizedMixedEndpointHomotopy V W a hF hG hc)
      (t, SSet.realizationPoint
        (show (SSet.diagonalSSet (SSet.OrdinalSubdivision.δ.op ⋙ bisimplicialSSet V)) _⦋0⦌ from
          zeroSimplex₂ V.cof V.weq V.zero V.isZero (op (SSet.OrdinalSubdivision.δ.obj
            ⦋0⦌)) (op ⦋0⦌))) =
        SSet.realizationPoint (diagonalZeroVertex W) :=
  SSet.realizationSimplicialHomotopy_fixed_vertex _ _ _
    (normalizedMixedEndpointHomotopy_fixed_zero V W a hF hG hc) t

end CategoryTheory.Waldhausen.Additivity
