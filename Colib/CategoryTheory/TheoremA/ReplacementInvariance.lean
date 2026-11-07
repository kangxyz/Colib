/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Colib.CategoryTheory.TheoremA.SkeletalEquivalences
public import Colib.Topology.Category.TopCat.SequentialColimit.HomotopyInvariance
public import Colib.CategoryTheory.TheoremA.Augmentations

/-! Source: Quillen/CategoryTheory/TheoremA/ReplacementInvariance.lean at
c561118b7795eb9780be9ed391c3251d6a4d0afd. Native topology lower owners are reused. -/

/-! # Actual homotopy invariance of simplicial replacement realization -/
@[expose] public section

noncomputable section

open SSet TopCat CategoryTheory Limits Opposite
open scoped Simplicial Topology

universe u

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

namespace CategoryTheory.TheoremA

variable {D : Type u} [SmallCategory D]

/-- The canonical exhaustive cocone on the realized skeletal tower. -/
def realizedReplacementSkeletonCocone (H : D ⥤ SSet.{u}) :
    Cocone (realizedReplacementSkeleton H) :=
  (diagonalFunctor ⋙ SSet.toTop).mapCocone (replacementSkeletonCocone H)

/-- The colimit comparison is exactly the realization of the original
simplicial replacement map. -/
theorem realizedReplacementSkeleton_colimitMap {H K : D ⥤ SSet.{u}} (η : H ⟶ K) :
    (realizedReplacementSkeletonIsColimit H).map
      (realizedReplacementSkeletonCocone K) (realizedReplacementSkeletonMap η) =
        SSet.toTop.map (diagonalMap (simplicialReplacementMap η)) := by
  apply (realizedReplacementSkeletonIsColimit H).hom_ext
  intro n
  rw [(realizedReplacementSkeletonIsColimit H).ι_map]
  let R := diagonalFunctor.{u} ⋙ SSet.toTop
  change R.map ((replacementSkeletonMap η).app n) ≫
      R.map (replacementRestrictionι K ((nerve D).skeleton n)) =
    R.map (replacementRestrictionι H ((nerve D).skeleton n)) ≫
      R.map (simplicialReplacementMap η)
  simpa only [← Functor.map_comp] using congrArg R.map (replacementSkeletonMap_ι η n)

/-- Objectwise realized homotopy equivalences induce an actual homotopy
equivalence on geometric realization of the simplicial replacement.
No compatible choice of the fiberwise inverse or homotopies is required. -/
def replacementRealizationHomotopyEquiv {H K : D ⥤ SSet.{u}} (η : H ⟶ K)
    (e : ∀ d, ContinuousMap.HomotopyEquiv |H.obj d| |K.obj d|)
    (he : ∀ d, (e d).toFun = (SSet.toTop.map (η.app d)).hom) :
    ContinuousMap.HomotopyEquiv |replacementDiagonal H| |replacementDiagonal K| := by
  let E : ContinuousMap.HomotopyEquiv |replacementDiagonal H| |replacementDiagonal K| :=
    sequentialCoconeHomotopyEquiv (realizedReplacementSkeletonMap η)
    (homotopyExtensionProperty_realizedReplacementSkeleton_succ H)
    (homotopyExtensionProperty_realizedReplacementSkeleton_succ K)
    (realizedReplacementSkeletonHomotopyEquiv η e he)
    (realizedReplacementSkeletonHomotopyEquiv_toFun η e he)
    (realizedReplacementSkeletonCocone H) (realizedReplacementSkeletonIsColimit H)
    (realizedReplacementSkeletonCocone K) (realizedReplacementSkeletonIsColimit K)
  have hE : E.toFun = (SSet.toTop.map (diagonalMap (simplicialReplacementMap η))).hom := by
    rw [sequentialCoconeHomotopyEquiv_toFun]
    exact congrArg TopCat.Hom.hom (realizedReplacementSkeleton_colimitMap η)
  exact { E with
    toFun := (SSet.toTop.map (diagonalMap (simplicialReplacementMap η))).hom
    left_inv := by simpa only [hE] using E.left_inv
    right_inv := by simpa only [hE] using E.right_inv }

@[simp]
theorem replacementRealizationHomotopyEquiv_toFun {H K : D ⥤ SSet.{u}} (η : H ⟶ K)
    (e : ∀ d, ContinuousMap.HomotopyEquiv |H.obj d| |K.obj d|)
    (he : ∀ d, (e d).toFun = (SSet.toTop.map (η.app d)).hom) :
    (replacementRealizationHomotopyEquiv η e he).toFun =
      (SSet.toTop.map (diagonalMap (simplicialReplacementMap η))).hom := rfl

/-- The canonical realization of the replacement of the point diagram. -/
def replacementPointRealizationIso :
    |replacementDiagonal ((Functor.const D).obj (Δ[0] : SSet.{u}))| ≅ |nerve D| :=
  SSet.toTop.mapIso ((diagonalFunctor.mapIso replacementPointIso) ≪≫ diagonalBaseIso D)

/-- Contractible coefficients give an actual equivalence from the simplicial
replacement to the nerve of the indexing category. -/
def contractibleReplacementRealizationHomotopyEquiv (H : D ⥤ SSet.{u})
    (h : ∀ d, ContractibleSpace |H.obj d|) :
    ContinuousMap.HomotopyEquiv |replacementDiagonal H| |nerve D| :=
  (replacementRealizationHomotopyEquiv (replacementPointAugmentation H)
    (fun d ↦ by
      letI := h d
      exact (ContractibleSpace.hequiv |H.obj d| |(Δ[0] : SSet.{u})|).some)
    (fun _ ↦ by ext x; exact @Subsingleton.elim |(Δ[0] : SSet.{u})| inferInstance _ _)).trans
    (TopCat.homeoOfIso replacementPointRealizationIso).toHomotopyEquiv

/-- The contractible-coefficient equivalence has exactly the canonical base
projection as its forward map. -/
@[simp]
theorem contractibleReplacementRealizationHomotopyEquiv_toFun (H : D ⥤ SSet.{u})
    (h : ∀ d, ContractibleSpace |H.obj d|) :
    (contractibleReplacementRealizationHomotopyEquiv H h).toFun =
      (SSet.toTop.map (replacementBaseMap H)).hom := by
  change (replacementPointRealizationIso.hom).hom.comp
      (replacementRealizationHomotopyEquiv _ _ _).toFun = _
  rw [replacementRealizationHomotopyEquiv_toFun]
  change (SSet.toTop.map (diagonalMap (simplicialReplacementMap (replacementPointAugmentation H))) ≫
    replacementPointRealizationIso.hom).hom = _
  congr 1
  change SSet.toTop.map (diagonalMap (simplicialReplacementMap (replacementPointAugmentation H))) ≫
    SSet.toTop.map ((diagonalMap replacementPointIso.hom) ≫ (diagonalBaseIso D).hom) = _
  rw [← Functor.map_comp]
  apply congrArg SSet.toTop.map
  exact targetAugmentation_diagonal H

end CategoryTheory.TheoremA

attribute [colib_tag "COL-0233",
  colib_ref "WeibelKBook" "IV, 3.6.1, page 29" "adaptation"
    "Simplicial replacement realization invariance"]
  CategoryTheory.TheoremA.replacementRealizationHomotopyEquiv
