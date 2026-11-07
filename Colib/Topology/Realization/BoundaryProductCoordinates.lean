/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Colib.Topology.Realization.Boundary
public import Colib.Topology.Realization.LocallyCompactProduct
public import Colib.Topology.Realization.SimplexAttachmentCollar

/-!
Adapted from `Quillen/CategoryTheory/TheoremA/EnrichedBoundaryHEP.lean` at commit
`c561118b7795eb9780be9ed391c3251d6a4d0afd`, retaining the original maps.
 # Actual geometric coordinates on realized boundary products -/
@[expose] public noncomputable section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory TopCat SSet
open Convexity.StdSimplex
open scoped Simplicial Topology
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace SSet
instance realizationProductComparison_boundary_isIso (X : SSet.{u}) (n : ℕ) :
    IsIso (CartesianMonoidalCategory.prodComparison SSet.toTop X (∂Δ[n] : SSet.{u})) :=
  realizationProductComparison_isIso_of_locallyCompact X _

/-- The realized product with a boundary, in ordinary geometric coordinates. -/
def realizationProductBoundaryHomeomorph (X : SSet.{u}) (n : ℕ) :
    |X ⊗ (∂Δ[n] : SSet.{u})| ≃ₜ |X| × Convexity.StdSimplex.boundary n :=
  (TopCat.homeoOfIso (asIso (CartesianMonoidalCategory.prodComparison SSet.toTop X
      (∂Δ[n] : SSet.{u})))).trans
    ((Homeomorph.refl _).prodCongr (realizationBoundaryHomeomorph n))

/-- The realized product with a simplex, allowing an arbitrary simplicial parameter. -/
def realizationProductSimplexParameterHomeomorph (X : SSet.{u}) (n : ℕ) :
    |X ⊗ Δ[n]| ≃ₜ |X| × Convexity.StdSimplex ℝ (Fin (n + 1)) :=
  (TopCat.homeoOfIso (realizationProductSimplexIso X n)).trans
    ((Homeomorph.refl _).prodCongr (SimplexCategory.toTopHomeo ⦋n⦌))

end SSet

namespace CategoryTheory.TheoremA

set_option maxHeartbeats 800000 in
-- Comparing the original forward maps unfolds the nested realization coordinate homeomorphisms.
/-- The product comparisons identify the actual simplicial boundary map with
its ordinary parameterized topological boundary inclusion. -/
theorem realizationProductBoundary_square (X : SSet.{u}) (n : ℕ) :
    SSet.toTop.map (X ◁ ∂Δ[n].ι) ≫
        (TopCat.isoOfHomeo (realizationProductSimplexParameterHomeomorph X n)).hom =
      (TopCat.isoOfHomeo (realizationProductBoundaryHomeomorph X n)).hom ≫
        TopCat.parameterizedSimplexBoundaryInclusion |X| n := by
  apply TopCat.hom_ext
  apply ContinuousMap.ext
  intro x
  have h := ConcreteCategory.congr_hom
    (prodComparison_natural_whiskerLeft (A := X) SSet.toTop ∂Δ[n].ι) x
  apply Prod.ext
  · exact congrArg (fun z : |X| × |(Δ[n] : SSet.{u})| ↦ z.1) h
  · exact congrArg (fun z : |X| × |(Δ[n] : SSet.{u})| ↦
      SimplexCategory.toTopHomeo ⦋n⦌ z.2) h

end CategoryTheory.TheoremA
