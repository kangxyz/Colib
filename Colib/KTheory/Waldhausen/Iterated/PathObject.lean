/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.CategoryTheory.Waldhausen.SConstruction.Iterated.PathDiagram
public import Colib.CategoryTheory.TheoremA.Augmentations
public import Colib.KTheory.Waldhausen.Connected
public import Colib.KTheory.Waldhausen.Iterated.Prespectrum
public import Colib.Topology.Realization.BisimplicialContractibility
public import Colib.KTheory.Waldhausen.WeakNaturalTransformationBased
public import Colib.KTheory.Waldhausen.ZeroFunctor

/-!
# Contractibility of actual paths at every finite S-stage

Implementation provenance: `Quillen/Waldhausen/SConstruction/Iterated/PathObject.lean`
at Quillen commit `c561118b7795eb9780be9ed391c3251d6a4d0afd`. The original
maps, ordinal parameters, chosen zero objects and universe parameters are retained.
-/
@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits Opposite MonoidalCategory CartesianMonoidalCategory
open scoped Simplicial Topology unitInterval
universe u
namespace CategoryTheory.Waldhausen.IteratedS

open SmallWaldhausenCategory SSet Topology
open Fibration.RelativeRows

/-- Every actual higher S-realization is connected, with no Omega-equivalence premise. -/
theorem stageSpace_pathConnected (r : ℕ) (W : WideSubcategory preservesZero.{u}) :
    PathConnectedSpace (stageSpace r W) := by
  induction r generalizing W with
  | zero => exact inferInstanceAs (PathConnectedSpace W.obj.waldhausen.Delooping)
  | succ r ih =>
    let : PathConnectedSpace |(rowDiagram W ⋙ stages r).obj (op ⦋0⦌)| :=
      ih ((rows ⦋0⦌).obj W)
    exact diagonal_pathConnected_of_zero_row (rowDiagram W ⋙ stages r)


/-- An all-weak original structure has a genuine S-contraction. -/
theorem initialS_contractible_of_all_weak (W : WideSubcategory preservesZero.{u})
    (h : ∀ ⦃A B : W.obj.Obj⦄ (f : A ⟶ B), W.obj.waldhausen.weq f) :
    ContractibleSpace (stageSpace 0 W) := by
  let η : zeroFunctor W.obj.waldhausen ⟶ 𝟭 W.obj.Obj := {
    app A := W.obj.waldhausen.isZero.to_ A
    naturality _ _ _ := W.obj.waldhausen.isZero.eq_of_src _ _ }
  let H := weakNaturalTransformationRealizationHomotopy W.obj.waldhausen W.obj.waldhausen
    (zeroFunctor_isExact _ _) (IsExact.id _ _) η (fun A ↦ h (η.app A))
  apply (contractible_iff_id_nullhomotopic _).2
  refine ⟨W.obj.waldhausen.kBasepoint, ?_⟩
  have hc : (deloopingMap (zeroFunctor_isExact W.obj.waldhausen W.obj.waldhausen)).hom =
      ContinuousMap.const W.obj.waldhausen.Delooping W.obj.waldhausen.kBasepoint :=
    deloopingMap_zeroFunctor _ _
  have hi : (deloopingMap (IsExact.id W.obj.waldhausen.cof W.obj.waldhausen.weq)).hom =
      ContinuousMap.id W.obj.waldhausen.Delooping := by
    rw [deloopingMap_id, TopCat.hom_id]
  rw [hc, hi] at H
  exact ⟨H.symm⟩

/-- All finite stages of an all-weak original category are actually contractible. -/
theorem stageSpace_contractible_of_all_weak (r : ℕ) (W : WideSubcategory preservesZero.{u})
    (h : ∀ ⦃A B : W.obj.Obj⦄ (f : A ⟶ B), W.obj.waldhausen.weq f) :
    ContractibleSpace (stageSpace r W) := by
  induction r generalizing W with
  | zero => exact initialS_contractible_of_all_weak W h
  | succ r ih =>
    apply diagonal_contractible_of_rows (rowDiagram W ⋙ stages r)
    intro n
    exact ih ((rows n).obj W) (fun {A B} f p ↦ h (f.hom.app p))

/-- The actual augmentation and degeneracy section give the whole path-object equivalence. -/
def pathRealizationEquiv (H : WideSubcategory preservesZero.{u} ⥤ SSet.{u})
    (W : WideSubcategory preservesZero.{u}) :
    ContinuousMap.HomotopyEquiv |SSet.diagonalSSet (pathDiagram W ⋙ H)|
      |SSet.diagonalSSet ((Functor.const _).obj ((rows ⦋0⦌).obj W) ⋙ H)| where
  toFun := (SSet.toTop.map (pathAugmentationMap H W)).hom
  invFun := (SSet.toTop.map (pathSectionMap H W)).hom
  left_inv := by
    have h := realizationSimplicialHomotopy (pathHomotopy H W)
    simp only [CategoryTheory.Functor.map_comp, CategoryTheory.Functor.map_id,
      TopCat.hom_comp, TopCat.hom_id] at h
    exact ⟨h⟩
  right_inv := by
    have h := congrArg (fun f ↦ (SSet.toTop.map f).hom) (pathSectionMap_augmentation H W)
    simp only [CategoryTheory.Functor.map_comp, CategoryTheory.Functor.map_id,
      TopCat.hom_comp, TopCat.hom_id] at h
    rw [h]

/-- At every finite S-level the genuine added-initial-row path object is contractible. -/
theorem pathStage_contractible (r : ℕ) (W : WideSubcategory preservesZero.{u}) :
    ContractibleSpace |SSet.diagonalSSet (pathDiagram W ⋙ stages r)| := by
  let e : SSet.diagonalSSet ((Functor.const _).obj ((rows ⦋0⦌).obj W) ⋙ stages r) ≅
      (stages r).obj ((rows ⦋0⦌).obj W) :=
    SSet.diagonalFunctor.mapIso (Functor.constComp SimplexCategoryᵒᵖ ((rows ⦋0⦌).obj W)
      (stages r)) ≪≫
      CategoryTheory.TheoremA.diagonalConstantIso _
  let : ContractibleSpace |(stages r).obj ((rows ⦋0⦌).obj W)| :=
    stageSpace_contractible_of_all_weak r ((rows ⦋0⦌).obj W) (fun {A B} f ↦ zeroRows_all_weak W f)
  let : ContractibleSpace |SSet.diagonalSSet ((Functor.const _).obj ((rows ⦋0⦌).obj W) ⋙
    stages r)| :=
    (TopCat.homeoOfIso (SSet.toTop.mapIso e)).contractibleSpace
  exact (pathRealizationEquiv (stages r) W).contractibleSpace


end CategoryTheory.Waldhausen.IteratedS
