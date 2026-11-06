/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Colib.CategoryTheory.TheoremA.SkeletalEquivalences
public import Colib.Topology.HomotopyPullback.Cartesian

/-! # Actual enriched product charts and their canonical cartesian squares -/
/-! Implementation source: `Quillen/CategoryTheory/TheoremB/SkeletalCartesianProducts.lean` at
c561118b7795eb9780be9ed391c3251d6a4d0afd. Existing enriched domains, product realization
coordinates and actual canonical maps are retained. No stage-chart input is required. -/
@[expose] public section

open SSet Topology.HomotopyPullback


noncomputable section
open CategoryTheory Limits Opposite MonoidalCategory CartesianMonoidalCategory
open scoped Simplicial Topology unitInterval
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

namespace CategoryTheory.TheoremA

/-- The actual indexing-simplex projection of an enriched domain. -/
def outerProjection (K X : SSet.{u}) : diagonalSSet (outerProduct K X) ⟶ K where
  app _ := ↾fun x ↦ x.1
  naturality _ _ _ := rfl

/-- The actual base projection of a restricted replacement. -/
def restrictionProjection {D : Type u} [SmallCategory D]
    (H : D ⥤ SSet.{u}) (A : (nerve D).Subcomplex) :
    diagonalSSet (replacementRestriction H A) ⟶ A where
  app _ := ↾fun x ↦ x.1
  naturality _ _ _ := rfl

@[reassoc] theorem outerProjection_map {K L X : SSet.{u}} (k : K ⟶ L) :
    diagonalMap (outerProductMap (X := X) k) ≫ outerProjection L X =
      outerProjection K X ≫ k := rfl

@[reassoc] theorem outerProjection_coefficient {K X Y : SSet.{u}} (f : X ⟶ Y) :
    diagonalMap (outerProductCoefficientMap (K := K) f) ≫ outerProjection K Y =
      outerProjection K X := rfl

/-- Product coordinates carry the enriched index projection to the genuine
second projection exactly. -/
theorem realizedOuterProductIso_projection (K X : SSet.{u}) [LocallyCompactSpace |K|] :
    (realizedOuterProductIso K X).hom ≫ snd |X| |K| =
      SSet.toTop.map (outerProjection K X) := by
  dsimp [realizedOuterProductIso]
  rw [Category.assoc, CartesianMonoidalCategory.prodComparison_snd, ← Functor.map_comp]
  rfl

/-- Outer-product realization coordinates are natural in the geometric domain. -/
theorem realizedOuterProductIso_domain {K L X : SSet.{u}}
    [LocallyCompactSpace |K|] [LocallyCompactSpace |L|] (k : K ⟶ L) :
    SSet.toTop.map (diagonalMap (outerProductMap (X := X) k)) ≫
      (realizedOuterProductIso L X).hom =
    (realizedOuterProductIso K X).hom ≫ (|X| ◁ SSet.toTop.map k) := by
  dsimp [realizedOuterProductIso]
  rw [← Functor.map_comp_assoc, diagonalOuterProductIso_naturality, Functor.map_comp_assoc,
    prodComparison_natural_whiskerLeft]
  simp only [Category.assoc]

/-- The simultaneous parameter/coefficient map in actual enriched coordinates. -/
def enrichedMap {K L X Y : SSet.{u}} (k : K ⟶ L) (f : X ⟶ Y) :
    diagonalSSet (outerProduct K X) ⟶ diagonalSSet (outerProduct L Y) :=
  diagonalMap (outerProductMap k ≫ outerProductCoefficientMap f)

@[reassoc] theorem enrichedMap_projection {K L X Y : SSet.{u}} (k : K ⟶ L) (f : X ⟶ Y) :
    enrichedMap k f ≫ outerProjection L Y = outerProjection K X ≫ k := rfl

/-- Both geometric and coefficient coordinates are exact under realization. -/
theorem realizedOuterProductIso_map {K L X Y : SSet.{u}}
    [LocallyCompactSpace |K|] [LocallyCompactSpace |L|] (k : K ⟶ L) (f : X ⟶ Y) :
    SSet.toTop.map (enrichedMap k f) ≫ (realizedOuterProductIso L Y).hom =
      (realizedOuterProductIso K X).hom ≫ (SSet.toTop.map f ⊗ₘ SSet.toTop.map k) := by
  change SSet.toTop.map (diagonalMap (outerProductMap k) ≫
    diagonalMap (outerProductCoefficientMap f)) ≫ _ = _
  rw [Functor.map_comp, Category.assoc, realizedOuterProductIso_coefficient,
    ← Category.assoc, realizedOuterProductIso_domain, Category.assoc]
  rw [← tensorHom_def']

theorem realizedEnrichedMap_square {K L X Y : SSet.{u}} (k : K ⟶ L) (f : X ⟶ Y) :
    SSet.toTop.map (enrichedMap k f) ≫ SSet.toTop.map (outerProjection L Y) =
      SSet.toTop.map (outerProjection K X) ≫ SSet.toTop.map k := by
  rw [← Functor.map_comp, ← Functor.map_comp]
  exact congrArg SSet.toTop.map (enrichedMap_projection k f)

/-- Every actual enriched product square is cartesian when its prescribed
coefficient map is a homotopy equivalence. -/
theorem enrichedMap_cartesian {K L X Y : SSet.{u}}
    [LocallyCompactSpace |K|] [LocallyCompactSpace |L|]
    (k : K ⟶ L) (f : X ⟶ Y) (e : ContinuousMap.HomotopyEquiv |X| |Y|)
    (he : e.toFun = (SSet.toTop.map f).hom) :
    Cartesian (SSet.toTop.map (outerProjection K X)).hom
      (SSet.toTop.map (outerProjection L Y)).hom (SSet.toTop.map (enrichedMap k f)).hom
      (SSet.toTop.map k).hom
      (congrArg TopCat.Hom.hom (realizedEnrichedMap_square k f)) := by
  apply cartesianOfCoordinates _ _ _ _ _
    (ContinuousMap.snd : C(|X| × |K|, |K|))
    (ContinuousMap.snd : C(|Y| × |L|, |L|))
    (e.toFun.prodMap (SSet.toTop.map k).hom) (SSet.toTop.map k).hom rfl
    (TopCat.homeoOfIso (realizedOuterProductIso K X))
    (TopCat.homeoOfIso (realizedOuterProductIso L Y))
    (Homeomorph.refl _) (Homeomorph.refl _)
  · exact congrArg TopCat.Hom.hom (realizedOuterProductIso_projection K X)
  · exact congrArg TopCat.Hom.hom (realizedOuterProductIso_projection L Y)
  · rw [he]
    exact congrArg TopCat.Hom.hom (realizedOuterProductIso_map k f).symm
  · rfl
  · exact cartesianProduct _ e

end CategoryTheory.TheoremA
