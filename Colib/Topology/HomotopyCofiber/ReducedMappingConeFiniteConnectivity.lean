/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.Topology.HomotopyCofiber.ReducedMappingConeFiberReduction
public import Colib.Topology.DoubleMappingCylinder.GapConnectivity

/-!
# Finite excision for the literal reduced cone-to-fiber comparison

The original double-cylinder theorem applies to the ordinary cone with its singleton endpoint.
Removing that singleton preserves the complete cylinder path. The genuine chosen-point collapse
then yields the same finite range for the actual reduced cone comparison under original point HEP.
-/
/-! Implementation provenance: adapted from
`Quillen/Topology/HomotopyCofiber/ReducedMappingConeFiniteConnectivity.lean` at commit
`c561118b7795eb9780be9ed391c3251d6a4d0afd`. The original objects, maps,
point hypotheses, whole stored cylinder paths and universe parameters are
retained. Native namespace and lower-import ownership are used. -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory
open scoped Topology
universe u
namespace Topology.ReducedMappingCone
variable {X Y : Type u} [TopologicalSpace X] [TopologicalSpace Y]
  (f : C(X, Y))

/-- Removing the singleton endpoint identifies the original cylinder target with its fiber. -/
def unreducedGapFiberHomeomorph :
    HomotopyPullback
      (TopCat.DoubleCylinder.gapLeftEndpoint (B := TopCat.of Y) (C := TopCat.of PUnit)
        (unreducedEnd f))
      (TopCat.DoubleCylinder.gapRightEndpoint (B := TopCat.of Y) (C := TopCat.of PUnit)
      (unreducedEnd f)) ≃ₜ
        HomotopyFiber (unreducedInclusion f) (unreducedVertex f) :=
  HomotopyFiber.singletonParameterHomeomorph (unreducedInclusion f) PUnit
    (TopCat.DoubleCylinder.gapRightEndpoint (B := TopCat.of Y) (C := TopCat.of PUnit)
      (unreducedEnd f)) PUnit.unit

/-- The entire original unreduced cylinder is retained by the singleton comparison. -/
theorem unreducedGapFiberHomeomorph_comp_gap :
    (unreducedGapFiberHomeomorph f).toHomotopyEquiv.toFun.comp
      (TopCat.DoubleCylinder.gap (TopCat.ofHom f)
        (TopCat.ofHom (ContinuousMap.const X PUnit.unit)) (unreducedSquare f)) =
          unreducedFiberComparison f := rfl

/-- Finite excision for the actual ordinary cone-to-inclusion-fiber comparison. -/
theorem unreducedFiberComparison_isHomotopyConnectedMap (p q r : ℕ)
    (hr : r + 1 ≤ p + q) (hf : IsHomotopyConnectedMap f p)
    (hX : IsHomotopyConnectedMap (ContinuousMap.const X (PUnit.unit : PUnit.{u + 1})) q) :
    IsHomotopyConnectedMap (unreducedFiberComparison f) r :=
  IsHomotopyConnectedMap.of_equivalence_square (ContinuousMap.HomotopyEquiv.refl X)
    (unreducedGapFiberHomeomorph f).toHomotopyEquiv
    (unreducedGapFiberHomeomorph_comp_gap f) r
    (TopCat.DoubleCylinder.gap_isHomotopyConnectedMap (TopCat.ofHom f)
      (TopCat.ofHom (ContinuousMap.const X PUnit.unit)) (unreducedSquare f) p q r hr hf hX)

/-- Finite excision for the unchanged reduced cone gap, with explicit original point HEP. -/
theorem fiberComparison_isHomotopyConnectedMap (x₀ : X) (y₀ : Y) (hf : f x₀ = y₀)
    (hX : TopCat.HomotopyExtensionProperty
      (TopCat.ofHom (ContinuousMap.const PUnit.{u + 1} x₀)))
    (hY : TopCat.HomotopyExtensionProperty
      (TopCat.ofHom (ContinuousMap.const PUnit.{u + 1} y₀)))
    (p q r : ℕ) (hr : r + 1 ≤ p + q) (hfp : IsHomotopyConnectedMap f p)
    (hXq : IsHomotopyConnectedMap (ContinuousMap.const X (PUnit.unit : PUnit.{u + 1})) q) :
    IsHomotopyConnectedMap (fiberComparison x₀ y₀ f) r :=
  fiberComparison_isHomotopyConnectedMap_of_unreduced x₀ y₀ f hf hX hY r
    (unreducedFiberComparison_isHomotopyConnectedMap f p q r hr hfp hXq)

end Topology.ReducedMappingCone

attribute [colib_tag "COL-0287"]
  Topology.ReducedMappingCone.fiberComparison_isHomotopyConnectedMap
