/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.Topology.HomotopyPullback.WeakCalculus
public import Colib.CategoryTheory.TheoremB.SkeletalCartesianInduction
public import Colib.CategoryTheory.TheoremB.SkeletalCartesianCoordinates

/-! # Weak naturality squares in actual enriched product coordinates

Implementation provenance:
`Quillen/Topology/Realization/Cartesian/WeakProducts.lean`
at Quillen commit `c561118b7795eb9780be9ed391c3251d6a4d0afd`. Original maps,
hypotheses, path coordinates and universe parameters are retained.
-/
@[expose] public section

open CategoryTheory.TheoremA


noncomputable section
open Topology TopCat SSet Topology.HomotopyPullback
open CategoryTheory Limits Opposite MonoidalCategory CartesianMonoidalCategory
open scoped Simplicial Topology unitInterval
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace CategoryTheory.TheoremB.Skeletal
open TheoremA

/-- The exact square for two coefficient maps over one simplicial parameter map. -/
theorem enrichedCoefficient_square {K L X X' Y Y' : SSet.{u}}
    (k : K ⟶ L) (p : X ⟶ Y) (q : X' ⟶ Y') (f : X ⟶ X') (g : Y ⟶ Y')
    (w : f ≫ q = p ≫ g) :
    SSet.toTop.map (enrichedMap k f) ≫
        SSet.toTop.map (diagonalMap (outerProductCoefficientMap (K := L) q)) =
      SSet.toTop.map (diagonalMap (outerProductCoefficientMap (K := K) p)) ≫
        SSet.toTop.map (enrichedMap k g) := by
  rw [← SSet.toTop.map_comp, ← SSet.toTop.map_comp]
  congr 1
  ext n x : 4
  apply congrArg (Sigma.mk _)
  exact ConcreteCategory.congr_hom (NatTrans.congr_app w n) x.2

/-- A weak canonical coefficient square remains weak after enriching by a
geometric parameter map. All four realization coordinates are the actual ones. -/
theorem enrichedCoefficient_weakCartesian {K L X X' Y Y' : SSet.{u}}
    [LocallyCompactSpace |K|] [LocallyCompactSpace |L|]
    (k : K ⟶ L) (p : X ⟶ Y) (q : X' ⟶ Y') (f : X ⟶ X') (g : Y ⟶ Y')
    (w : f ≫ q = p ≫ g)
    (h : WeakCartesian (SSet.toTop.map p).hom (SSet.toTop.map q).hom
      (SSet.toTop.map f).hom (SSet.toTop.map g).hom
      (congrArg TopCat.Hom.hom (show SSet.toTop.map f ≫ SSet.toTop.map q =
        SSet.toTop.map p ≫ SSet.toTop.map g from by
        rw [← SSet.toTop.map_comp, ← SSet.toTop.map_comp, w]))) :
    WeakCartesian
      (SSet.toTop.map (diagonalMap (outerProductCoefficientMap (K := K) p))).hom
      (SSet.toTop.map (diagonalMap (outerProductCoefficientMap (K := L) q))).hom
      (SSet.toTop.map (enrichedMap k f)).hom (SSet.toTop.map (enrichedMap k g)).hom
      (congrArg TopCat.Hom.hom (enrichedCoefficient_square k p q f g w)) := by
  have hk : WeakCartesian (ContinuousMap.id |K|) (ContinuousMap.id |L|)
      (SSet.toTop.map k).hom (SSet.toTop.map k).hom rfl :=
    isWeakHomotopyEquivalence_of_homotopyEquiv
      (HomotopyPullback.identityHomotopyEquiv (SSet.toTop.map k).hom)
  have hh := h.prod hk
  apply weakCartesianOfCoordinates _ _ _ _ _ _ _ _ _ _
    (TopCat.homeoOfIso (realizedOuterProductIso K X))
    (TopCat.homeoOfIso (realizedOuterProductIso L X'))
    (TopCat.homeoOfIso (realizedOuterProductIso K Y))
    (TopCat.homeoOfIso (realizedOuterProductIso L Y'))
  · exact congrArg TopCat.Hom.hom (realizedOuterProductIso_coefficient (B := K) p).symm
  · exact congrArg TopCat.Hom.hom (realizedOuterProductIso_coefficient (B := L) q).symm
  · exact congrArg TopCat.Hom.hom (realizedOuterProductIso_map k f).symm
  · exact congrArg TopCat.Hom.hom (realizedOuterProductIso_map k g).symm
  · exact hh

end CategoryTheory.TheoremB.Skeletal
