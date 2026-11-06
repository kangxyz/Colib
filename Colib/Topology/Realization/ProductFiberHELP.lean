/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Colib.Topology.Realization.ProductCompactHELP
public import Colib.Topology.Realization.SplitFiber
public import Colib.Topology.HomotopyFiber.CompactHELP
public import Colib.Topology.HELP.Composition
public import Colib.Topology.HELP.HomotopyEquiv
public import Colib.Topology.Homotopy.HomotopyGroup.ZeroDetection

/-! # Compact HELP and connectedness of actual product-type row fibers

Implementation provenance:
`Quillen/Topology/Realization/ProductFiberHELP.lean`
at Quillen commit `c561118b7795eb9780be9ed391c3251d6a4d0afd`. The original maps,
hypotheses, path coordinates and universe parameters are retained.
-/
@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open Topology CategoryTheory MonoidalCategory CartesianMonoidalCategory
open scoped Simplicial Topology
universe u

namespace SSet.ProductRealization
variable (A B : SSet.{u})

/-- The prescribed source comparison on actual product fibers satisfies
compact HELP while retaining its path coordinate literally. -/
theorem sourceFiberComparison_compactHELP (b : |B|) :
    CompactHomotopyExtensionLiftingProperty (sourceFiberComparison A B b) :=
  HomotopyFiber.sourceMap_compactHELP ContinuousMap.snd (comparison A B)
    (comparison_injective A B) (comparison_compact_lifts_universe A B) b

/-- The original realized first projection satisfies compact HELP on the
actual second-projection fiber. -/
theorem fiberProjection_compactHELP (b : |B|) :
    CompactHomotopyExtensionLiftingProperty (fiberProjection A B b) :=
  (TopCat.compactHELP_of_homotopyEquiv (HomotopyFiber.sndEquiv |A| b)).comp
    (sourceFiberComparison_compactHELP A B b)

/-- Any nonempty product-projection fiber is genuinely path connected when
the first realization is, as detected by its original π₀ map. -/
theorem fiber_pathConnected [PathConnectedSpace |A|] (b : |B|)
    (p : HomotopyFiber (SSet.toTop.map (snd A B)).hom b) :
    PathConnectedSpace (HomotopyFiber (SSet.toTop.map (snd A B)).hom b) :=
  pathConnectedSpace_of_injective_zeroMap (fiberProjection A B b) p
    (fiberProjection_bijective A B b p 0).injective

end SSet.ProductRealization

namespace SSet.SplitRealizationFiber
variable {A B E : SSet.{u}} (χ : E ⟶ A ⊗ B)
  (e : ContinuousMap.HomotopyEquiv |E| |A ⊗ B|)
  (he : e.toFun = (SSet.toTop.map χ).hom)

include e he

/-- The actual first projection of a product-type row fiber satisfies
compact HELP, derived from the genuine row comparison equivalence. -/
theorem firstProjection_compactHELP (b : |B|) :
    CompactHomotopyExtensionLiftingProperty (firstProjection χ b) :=
  (ProductRealization.fiberProjection_compactHELP A B b).comp
    (TopCat.compactHELP_of_homotopyEquiv (comparisonHomotopyEquiv χ e he b))

/-- The actual row fiber is path connected at every supplied fiber point
when its genuine first product factor is connected. -/
theorem fiber_pathConnected [PathConnectedSpace |A|] (b : |B|)
    (p : HomotopyFiber (projection χ) b) :
    PathConnectedSpace (HomotopyFiber (projection χ) b) :=
  pathConnectedSpace_of_injective_zeroMap (firstProjection χ b) p
    (firstProjection_bijective χ e he b p 0).injective

end SSet.SplitRealizationFiber
