/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Colib.Topology.Realization.HomotopyBridge
public import Mathlib.Topology.Homotopy.Equiv

public import Colib.AlgebraicTopology.SimplicialSet.MixedOrdinalBisimplicial

/-! # Realized homotopies supplied by the actual mixed cylinder

Implementation provenance: `Quillen/Waldhausen/Additivity/RealizationHomotopy.lean`
at commit c561118b7795eb9780be9ed391c3251d6a4d0afd. Actual maps, hypotheses and
universes are retained; no subdivision realization equivalence is assumed.
-/
@[expose] public section


noncomputable section
open CategoryTheory Opposite
open scoped Simplicial Topology
universe u

namespace CategoryTheory.Waldhausen.Additivity

/-- The realized map on the genuine diagonal of a bisimplicial set. -/
def realizedDiagonalMap {X Y : SimplexCategoryᵒᵖ ⥤ SSet.{u}} (η : X ⟶ Y) :
    C(|SSet.diagonalSSet X|, |SSet.diagonalSSet Y|) :=
  (SSet.toTop.map (SSet.diagonalMap η)).hom

@[simp] theorem realizedDiagonalMap_comp {X Y Z : SimplexCategoryᵒᵖ ⥤ SSet.{u}}
    (η : X ⟶ Y) (κ : Y ⟶ Z) :
    realizedDiagonalMap (η ≫ κ) = (realizedDiagonalMap κ).comp (realizedDiagonalMap η) := by
  change ((SSet.diagonalFunctor ⋙ SSet.toTop).map (η ≫ κ)).hom = _
  rw [Functor.map_comp]
  rfl

/-- The minimum-cut homotopy relates the two genuine endpoint maps of any
actual mixed deformation. No homotopy between the endpoints is an input. -/
theorem mixed_deformation_endpoints
    (X Y : SimplexCategoryᵒᵖ ⥤ SSet.{u}) (θ : SSet.MixedOrdinalCylinder.outerCylinder X ⟶ Y) :
    ((realizedDiagonalMap (SSet.MixedOrdinalCylinder.outerZeroSection X ≫ θ)).comp
      (realizedDiagonalMap (SSet.OrdinalSubdivision.horizontalEndpoint X))).Homotopic
      (realizedDiagonalMap (SSet.MixedOrdinalCylinder.outerOneSection X ≫ θ)) := by
  have H : ((realizedDiagonalMap (SSet.MixedOrdinalCylinder.outerZeroSection X)).comp
      (realizedDiagonalMap (SSet.MixedOrdinalCylinder.outerProjection X))).Homotopic
      (ContinuousMap.id _) := by
    have h := SSet.realizationSimplicialHomotopy (SSet.MixedOrdinalCylinder.outerContraction X)
    rw [Functor.map_comp, CategoryTheory.Functor.map_id] at h
    exact ⟨h⟩
  have H' := ((ContinuousMap.Homotopic.refl (realizedDiagonalMap θ)).comp H).comp
    (ContinuousMap.Homotopic.refl (realizedDiagonalMap
      (SSet.MixedOrdinalCylinder.outerOneSection X)))
  change (((realizedDiagonalMap θ).comp (realizedDiagonalMap
    (SSet.MixedOrdinalCylinder.outerZeroSection X))).comp
      ((realizedDiagonalMap (SSet.MixedOrdinalCylinder.outerProjection X)).comp
        (realizedDiagonalMap (SSet.MixedOrdinalCylinder.outerOneSection X)))).Homotopic
      ((realizedDiagonalMap θ).comp (realizedDiagonalMap (SSet.MixedOrdinalCylinder.outerOneSection
        X))) at H'
  have hp : (realizedDiagonalMap (SSet.MixedOrdinalCylinder.outerProjection X)).comp
      (realizedDiagonalMap (SSet.MixedOrdinalCylinder.outerOneSection X)) =
      realizedDiagonalMap (SSet.OrdinalSubdivision.horizontalEndpoint X) := by
    rw [← realizedDiagonalMap_comp, SSet.MixedOrdinalCylinder.outerOneSection_projection]
    rfl
  rw [hp] at H'
  exact (congrArg₂ ContinuousMap.Homotopic
    (congrArg (fun f ↦ f.comp (realizedDiagonalMap (SSet.OrdinalSubdivision.horizontalEndpoint X)))
      (realizedDiagonalMap_comp (SSet.MixedOrdinalCylinder.outerZeroSection X) θ))
    (realizedDiagonalMap_comp (SSet.MixedOrdinalCylinder.outerOneSection X) θ)).mpr H'


/-- Precomposition by a genuine homotopy equivalence detects homotopy of maps. -/
theorem homotopic_of_precomp_equivalence {X Y Z : Type u}
    [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z]
    (e : ContinuousMap.HomotopyEquiv X Y) (f g : C(Y, Z))
    (h : (f.comp e.toFun).Homotopic (g.comp e.toFun)) : f.Homotopic g := by
  have hf := (ContinuousMap.Homotopic.refl f).comp e.right_inv
  have hg := (ContinuousMap.Homotopic.refl g).comp e.right_inv
  exact hf.symm.trans ((h.comp (ContinuousMap.Homotopic.refl e.invFun)).trans hg)

end CategoryTheory.Waldhausen.Additivity
