/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Colib.CategoryTheory.Waldhausen.Fibration.MixedNerves.Postcompose
public import Colib.CategoryTheory.Waldhausen.Fibration.MixedNerves.TransposeNerves

/-! # Strict functoriality of the original mixed nerves and their transpose

The forward maps are literal postcomposition in both original indices.
Their identity, composition, inclusion, and transpose squares are proved
from the actual component formulas. No inverse choices are used.


Implementation provenance:
`Quillen/Waldhausen/Fibration/MixedNerves/PostcomposeNerves.lean`
at Quillen commit `c561118b7795eb9780be9ed391c3251d6a4d0afd`. The original maps,
hypotheses, chosen zero objects and universe parameters are retained.
-/
@[expose] public section

noncomputable section
open CategoryTheory Opposite
universe u v
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace CategoryTheory.Waldhausen.Fibration.MixedNerves
variable {C D E : Type u} [Category.{v} C] [Category.{v} D] [Category.{v} E]
  {V : Structure C} {W : Structure D} {U : Structure E}
  {N : NestedWeakEquivalences V} {M : NestedWeakEquivalences W} {L : NestedWeakEquivalences U}
  (F : CompatibleFunctor N M)

/-- Actual base postcomposition in the original coarse/fine nerve presentation. -/
def coarseNerveMap : coarseChainNerve N ⟶ coarseChainNerve M where
  app n := nerveMap (fineWeakCoarsePostcompose F n.unop)
  naturality _ _ _ := by ext k X; rfl
/-- The same original postcomposition retains the cofibration-chain condition. -/
def cofNerveMap : cofChainNerve N ⟶ cofChainNerve M where
  app n := nerveMap (fineWeakCofPostcompose F n.unop)
  naturality _ _ _ := by ext k X; rfl
/-- Actual base postcomposition in the transposed nerve presentation. -/
def horizontalNerveMap : horizontalNerve N ⟶ horizontalNerve M where
  app k := nerveMap (horizontalPostcompose F k.unop)
  naturality _ _ _ := by ext n X; rfl
/-- The same original transposed map retains genuine pointwise cofibrations. -/
def horizontalCofNerveMap : horizontalCofNerve N ⟶ horizontalCofNerve M where
  app k := nerveMap (horizontalCofPostcompose F k.unop)
  naturality _ _ _ := by ext n X; rfl

@[simp] theorem coarseNerveMap_id : coarseNerveMap (CompatibleFunctor.id N) = 𝟙
    (coarseChainNerve N) := by
  ext n k X : 5
  apply CategoryTheory.Functor.ext (fun _ ↦ rfl)
@[simp] theorem cofNerveMap_id : cofNerveMap (CompatibleFunctor.id N) = 𝟙 (cofChainNerve N) := by
  ext n k X : 5
  apply CategoryTheory.Functor.ext (fun _ ↦ rfl)
@[simp] theorem horizontalNerveMap_id : horizontalNerveMap (CompatibleFunctor.id N) = 𝟙
    (horizontalNerve N) := by
  ext n k X : 5
  apply CategoryTheory.Functor.ext (fun _ ↦ rfl)
@[simp] theorem horizontalCofNerveMap_id :
    horizontalCofNerveMap (CompatibleFunctor.id N) = 𝟙 (horizontalCofNerve N) := by
  ext n k X : 5
  apply CategoryTheory.Functor.ext (fun _ ↦ rfl)

@[simp] theorem coarseNerveMap_comp (G : CompatibleFunctor M L) :
    coarseNerveMap (F.comp G) = coarseNerveMap F ≫ coarseNerveMap G := by
  ext n k X : 5
  apply CategoryTheory.Functor.ext (fun _ ↦ rfl)
@[simp] theorem cofNerveMap_comp (G : CompatibleFunctor M L) :
    cofNerveMap (F.comp G) = cofNerveMap F ≫ cofNerveMap G := by
  ext n k X : 5
  apply CategoryTheory.Functor.ext (fun _ ↦ rfl)
@[simp] theorem horizontalNerveMap_comp (G : CompatibleFunctor M L) :
    horizontalNerveMap (F.comp G) = horizontalNerveMap F ≫ horizontalNerveMap G := by
  ext n k X : 5
  apply CategoryTheory.Functor.ext (fun _ ↦ rfl)
@[simp] theorem horizontalCofNerveMap_comp (G : CompatibleFunctor M L) :
    horizontalCofNerveMap (F.comp G) = horizontalCofNerveMap F ≫ horizontalCofNerveMap G := by
  ext n k X : 5
  apply CategoryTheory.Functor.ext (fun _ ↦ rfl)

/-- Naturality of the unchanged original inclusion under base postcomposition. -/
theorem chainInclusion_naturality :
    chainInclusion N ≫ coarseNerveMap F = cofNerveMap F ≫ chainInclusion M := by
  ext n k X : 5
  apply CategoryTheory.Functor.ext (fun _ ↦ rfl)
/-- Naturality of the literal horizontal inclusion under the same original functor. -/
theorem horizontalNerveInclusion_naturality :
    horizontalNerveInclusion N ≫ horizontalNerveMap F =
      horizontalCofNerveMap F ≫ horizontalNerveInclusion M := by
  ext n k X : 5
  apply CategoryTheory.Functor.ext (fun _ ↦ rfl)

/-- The exact two-index transpose commutes strictly with the original base functor. -/
theorem coarseTransposeIso_naturality :
    (flipFunctor _ _ _).map (coarseNerveMap F) ≫ (coarseTransposeIso M).hom =
      (coarseTransposeIso N).hom ≫ horizontalNerveMap F := by
  ext n k X : 5
  apply CategoryTheory.Functor.ext (fun _ ↦ rfl)
/-- The same transpose square retains the original cofibration predicates. -/
theorem cofTransposeIso_naturality :
    (flipFunctor _ _ _).map (cofNerveMap F) ≫ (cofTransposeIso M).hom =
      (cofTransposeIso N).hom ≫ horizontalCofNerveMap F := by
  ext n k X : 5
  apply CategoryTheory.Functor.ext (fun _ ↦ rfl)

/-- The original diagonal presentation isomorphism is natural in the actual base functor. -/
theorem coarseDiagonalIso_naturality :
    SSet.diagonalMap (coarseNerveMap F) ≫ (coarseDiagonalIso M).hom =
      (coarseDiagonalIso N).hom ≫ SSet.diagonalMap (horizontalNerveMap F) := by
  ext n X : 4
  apply CategoryTheory.Functor.ext (fun _ ↦ rfl)
/-- The original cofibration diagonal presentation isomorphism has the same strict naturality. -/
theorem cofDiagonalIso_naturality :
    SSet.diagonalMap (cofNerveMap F) ≫ (cofDiagonalIso M).hom =
      (cofDiagonalIso N).hom ≫ SSet.diagonalMap (horizontalCofNerveMap F) := by
  ext n X : 4
  apply CategoryTheory.Functor.ext (fun _ ↦ rfl)

end CategoryTheory.Waldhausen.Fibration.MixedNerves
