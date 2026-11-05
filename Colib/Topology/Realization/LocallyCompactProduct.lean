/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Colib.Topology.Realization.ProductSimplex
public import Mathlib.AlgebraicTopology.SimplicialSet.TopAdj

/-! # Actual realization products with a locally compact factor

The canonical product comparison is compatible with swapping factors. Density
of representables and the locally compact topological product adjunction extend
the standard-simplex comparison to any locally compact right realization.

Source: the product comparison section of
`Quillen/CategoryTheory/TheoremA/EnrichedBoundaryHEP.lean` at
c561118b7795eb9780be9ed391c3251d6a4d0afd. The actual comparison maps are retained.
-/
@[expose] public noncomputable section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory TopCat
open scoped Simplicial Topology
universe u
namespace SSet
/-- Product comparison is compatible with interchanging the two factors. -/
lemma realizationProductComparison_swap (X Y : SSet.{u}) :
    SSet.toTop.map (β_ X Y).hom ≫ CartesianMonoidalCategory.prodComparison SSet.toTop Y X =
      CartesianMonoidalCategory.prodComparison SSet.toTop X Y ≫ (β_ |X| |Y|).hom := by
  apply CartesianMonoidalCategory.hom_ext <;> simp [← Functor.map_comp]

lemma realizationProductComparison_isIso_swap (X Y : SSet.{u})
    [IsIso (CartesianMonoidalCategory.prodComparison SSet.toTop Y X)] :
    IsIso (CartesianMonoidalCategory.prodComparison SSet.toTop X Y) := by
  have h : CartesianMonoidalCategory.prodComparison SSet.toTop X Y =
      SSet.toTop.map (β_ X Y).hom ≫ CartesianMonoidalCategory.prodComparison SSet.toTop Y X ≫ (β_
        |X| |Y|).inv := by
    rw [← Category.assoc, realizationProductComparison_swap]
    simp
  rw [h]
  infer_instance

/-- The product comparison with a fixed second simplicial factor. -/
def realizationProductComparisonRightNatTrans (Y : SSet.{u}) :
    tensorRight Y ⋙ SSet.toTop ⟶ SSet.toTop ⋙ tensorRight |Y| where
  app X := CartesianMonoidalCategory.prodComparison SSet.toTop X Y
  naturality _ _ f := prodComparison_natural_whiskerRight SSet.toTop f

/-- Realization preserves product with any factor whose realization is locally compact. -/
theorem realizationProductComparison_isIso_of_locallyCompact
    (X Y : SSet.{u}) [LocallyCompactSpace |Y|] :
    IsIso (CartesianMonoidalCategory.prodComparison SSet.toTop X Y) := by
  let K := Presheaf.functorToRepresentables X
  let η := realizationProductComparisonRightNatTrans Y
  have : ∀ j, IsIso ((Functor.whiskerLeft K η).app j) := by
    intro j
    change IsIso (CartesianMonoidalCategory.prodComparison SSet.toTop (SSet.stdSimplex.obj
      j.unop.1.unop) Y)
    exact realizationProductComparison_isIso_swap _ _
  have := NatIso.isIso_of_isIso_app (Functor.whiskerLeft K η)
  have : PreservesColimitsOfShape X.Elementsᵒᵖ (tensorRight Y) :=
    preservesColimitsOfShape_of_natIso (BraidedCategory.tensorLeftIsoTensorRight Y)
  let := (topologicalProductMappingSpaceAdjunction |Y|).isLeftAdjoint
  have : PreservesColimit K (tensorRight Y) := by infer_instance
  have : PreservesColimit (K ⋙ tensorRight Y) SSet.toTop := by infer_instance
  have : PreservesColimit K SSet.toTop := by infer_instance
  have : PreservesColimit (K ⋙ SSet.toTop) (tensorRight |Y|) := by infer_instance
  exact isIso_app_coconePt_of_preservesColimit K η
    (Presheaf.coconeOfRepresentable X) (Presheaf.colimitOfRepresentable X)

end SSet
