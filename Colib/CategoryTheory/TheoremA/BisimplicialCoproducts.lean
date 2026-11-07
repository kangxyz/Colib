/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Colib.CategoryTheory.TheoremA.SkeletalAttachments
public import Colib.CategoryTheory.TheoremA.RealizationCoproduct

/-! Source: Quillen/CategoryTheory/TheoremA/BisimplicialCoproducts.lean at
c561118b7795eb9780be9ed391c3251d6a4d0afd. Native topology lower owners are reused. -/

/-! # Homotopy extension for realized bisimplicial coproducts -/
@[expose] public section

noncomputable section

open SSet TopCat CategoryTheory Limits Opposite MonoidalCategory
open scoped Simplicial Topology

universe u

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

namespace CategoryTheory.TheoremA

variable {ι : Type u}

/-- The map of explicit bisimplicial coproducts induced by a family of maps. -/
def bisimplicialSigmaMap {X Y : ι → SimplexCategoryᵒᵖ ⥤ SSet.{u}}
    (f : ∀ i, X i ⟶ Y i) : bisimplicialSigma X ⟶ bisimplicialSigma Y :=
  bisimplicialSigmaDesc fun i ↦ f i ≫ bisimplicialSigmaι Y i

@[reassoc (attr := simp)]
theorem bisimplicialSigmaι_map {X Y : ι → SimplexCategoryᵒᵖ ⥤ SSet.{u}}
    (f : ∀ i, X i ⟶ Y i) (i : ι) :
    bisimplicialSigmaι X i ≫ bisimplicialSigmaMap f = f i ≫ bisimplicialSigmaι Y i := rfl

/-- The realization of the explicit bisimplicial coproduct is a topological coproduct. -/
def realizedBisimplicialSigmaIsColimit (X : ι → SimplexCategoryᵒᵖ ⥤ SSet.{u}) :
    IsColimit (Cofan.mk |diagonalSSet (bisimplicialSigma X)|
      (fun i ↦ SSet.toTop.map (diagonalMap (bisimplicialSigmaι X i)))) :=
  isColimitCofanMkObjOfIsColimit (diagonalFunctor ⋙ SSet.toTop) X (bisimplicialSigmaι X)
    (bisimplicialSigmaIsColimit X)

/-- The canonical homeomorphism identifying the realized coproduct with a disjoint union. -/
def realizedBisimplicialSigmaIso (X : ι → SimplexCategoryᵒᵖ ⥤ SSet.{u}) :
    |diagonalSSet (bisimplicialSigma X)| ≅ TopCat.of (Σ i, |diagonalSSet (X i)|) :=
  (realizedBisimplicialSigmaIsColimit X).coconePointUniqueUpToIso
    (TopCat.sigmaCofanIsColimit fun i ↦ |diagonalSSet (X i)|)

@[reassoc (attr := simp)]
theorem realizedBisimplicialSigmaIso_ι (X : ι → SimplexCategoryᵒᵖ ⥤ SSet.{u}) (i : ι) :
    SSet.toTop.map (diagonalMap (bisimplicialSigmaι X i)) ≫
      (realizedBisimplicialSigmaIso X).hom =
        TopCat.sigmaι (fun i ↦ |diagonalSSet (X i)|) i :=
  (realizedBisimplicialSigmaIsColimit X).comp_coconePointUniqueUpToIso_hom _ ⟨i⟩

/-- The homeomorphism preserves the prescribed map on each summand exactly. -/
theorem realizedBisimplicialSigmaIso_naturality
    {X Y : ι → SimplexCategoryᵒᵖ ⥤ SSet.{u}} (f : ∀ i, X i ⟶ Y i) :
    SSet.toTop.map (diagonalMap (bisimplicialSigmaMap f)) ≫
      (realizedBisimplicialSigmaIso Y).hom =
    (realizedBisimplicialSigmaIso X).hom ≫
      topologicalSigmaMap (fun i ↦ SSet.toTop.map (diagonalMap (f i))) := by
  apply (realizedBisimplicialSigmaIsColimit X).hom_ext
  intro ⟨i⟩
  change (diagonalFunctor ⋙ SSet.toTop).map (bisimplicialSigmaι X i) ≫
      (diagonalFunctor ⋙ SSet.toTop).map (bisimplicialSigmaMap f) ≫ _ = _
  rw [← Functor.map_comp_assoc, bisimplicialSigmaι_map, Functor.map_comp_assoc]
  change SSet.toTop.map (diagonalMap (f i)) ≫
      SSet.toTop.map (diagonalMap (bisimplicialSigmaι Y i)) ≫ _ = _
  rw [realizedBisimplicialSigmaIso_ι]
  change _ = SSet.toTop.map (diagonalMap (bisimplicialSigmaι X i)) ≫
    (realizedBisimplicialSigmaIso X).hom ≫ _
  rw [← Category.assoc, realizedBisimplicialSigmaIso_ι, topologicalSigmaMap_ι]

/-- HEP is invariant under actual isomorphisms of the source and target. -/
theorem homotopyExtensionProperty_via_iso_square {A B A' B' : TopCat.{u}}
    {i : A ⟶ B} {j : A' ⟶ B'} (eA : A ≅ A') (eB : B ≅ B')
    (w : i ≫ eB.hom = eA.hom ≫ j) (hj : TopCat.HomotopyExtensionProperty j) :
    TopCat.HomotopyExtensionProperty i :=
  TopCat.homotopyExtensionProperty_of_iso_square i j eA eB w hj

/-- A family of genuinely realized bisimplicial HEP maps remains HEP after
forming the actual coproduct and realizing. -/
theorem homotopyExtensionProperty_realizedBisimplicialSigma
    {X Y : ι → SimplexCategoryᵒᵖ ⥤ SSet.{u}} (f : ∀ i, X i ⟶ Y i)
    (hf : ∀ i, TopCat.HomotopyExtensionProperty (SSet.toTop.map (diagonalMap (f i)))) :
    TopCat.HomotopyExtensionProperty (SSet.toTop.map (diagonalMap (bisimplicialSigmaMap f))) :=
  homotopyExtensionProperty_via_iso_square
    (realizedBisimplicialSigmaIso X) (realizedBisimplicialSigmaIso Y)
    (realizedBisimplicialSigmaIso_naturality f)
    (homotopyExtensionProperty_sigma _ hf)

end CategoryTheory.TheoremA
