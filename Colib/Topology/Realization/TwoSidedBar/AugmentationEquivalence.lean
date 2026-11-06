/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Colib.Topology.Realization.TwoSidedBar.Basic
public import Colib.Topology.Realization.BisimplicialEquivalence
public import Colib.Topology.Realization.ProductComparison
public import Colib.Topology.ClassifyingSpace.Contraction
public import Colib.Topology.Realization.TwoSidedBar.Resolution

/-!
# Augmentation equivalences of the two-sided bar

The drop and evaluation augmentations have the stated weak-equivalence properties, using row and
    column comparisons and the resolution contraction.


Implementation provenance:
`Quillen/Topology/Realization/TwoSidedBar/AugmentationEquivalence.lean`
at Quillen commit `c561118b7795eb9780be9ed391c3251d6a4d0afd`. Original maps,
hypotheses, path coordinates and universe parameters are retained.
-/
@[expose] public section

open CategoryTheory.TheoremA



noncomputable section
open Topology TopCat SSet
open CategoryTheory Limits Opposite MonoidalCategory CartesianMonoidalCategory
open scoped Simplicial Topology
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

namespace SSet.TwoSidedBar
open TheoremA

/-- Projection away from an actual finite standard simplex is an ordinary
homotopy equivalence, using only the permitted finite-factor product map. -/
def simplexProjectionHomotopyEquiv (X : SSet.{u}) (n : SimplexCategory) :
    ContinuousMap.HomotopyEquiv |X ⊗ SSet.stdSimplex.obj n| |X| := by
  letI : ContractibleSpace |SSet.stdSimplex.{u}.obj n| := by
    let : ContractibleSpace |nerve (ULift.{u} (Fin (n.len + 1)))| := by
      change ContractibleSpace (ClassifyingSpace (ULift.{u} (Fin (n.len + 1))))
      infer_instance
    exact (TopCat.homeoOfIso (SSet.toTop.mapIso (SSet.stdSimplex.isoNerve n.len))).contractibleSpace
  let E := (ProductRealization.finiteRightHomeomorph X (SSet.stdSimplex.obj
    n)).toHomotopyEquiv.trans
    (((ContinuousMap.HomotopyEquiv.refl |X|).prodCongr
      (ContractibleSpace.hequiv_unit |SSet.stdSimplex.obj n|).some).trans
        (Homeomorph.prodUnique |X| Unit).toHomotopyEquiv)
  exact {
    E with toFun := (SSet.toTop.map (fst X (SSet.stdSimplex.obj n))).hom
           left_inv := E.left_inv
           right_inv := E.right_inv }

@[simp] theorem simplexProjectionHomotopyEquiv_toFun (X : SSet.{u}) (n : SimplexCategory) :
    (simplexProjectionHomotopyEquiv X n).toFun =
      (SSet.toTop.map (fst X (SSet.stdSimplex.obj n))).hom := rfl

variable {D : Type u} [SmallCategory D]
  (L : D ⥤ SimplexCategoryᵒᵖ) (H : D ⥤ SSet.{u})

/-- The actual coordinate-dropping map is an equivalence on each row. -/
def dropRowHomotopyEquiv (p : SimplexCategoryᵒᵖ) :
    ContinuousMap.HomotopyEquiv |row L H p| |replacementRow H p| :=
  SSet.realizationSigmaHomotopyEquiv fun s : (nerve D).obj p ↦
    simplexProjectionHomotopyEquiv (H.obj (s.obj 0))
      (L.obj (s.obj (Fin.last p.unop.len))).unop

@[simp] theorem dropRowHomotopyEquiv_toFun (p : SimplexCategoryᵒᵖ) :
    (dropRowHomotopyEquiv L H p).toFun = (SSet.toTop.map (dropRow L H p)).hom :=
  SSet.realizationSigmaHomotopyEquiv_toFun
    (fun s : (nerve D).obj p ↦ fst (H.obj (s.obj 0))
      (SSet.stdSimplex.obj (L.obj (s.obj (Fin.last p.unop.len))).unop))
    (fun s ↦ simplexProjectionHomotopyEquiv (H.obj (s.obj 0))
      (L.obj (s.obj (Fin.last p.unop.len))).unop)
    (fun _ ↦ rfl)

/-- The prescribed bar-drop map realizes to a genuine homotopy equivalence. -/
def dropRealizationHomotopyEquiv :
    ContinuousMap.HomotopyEquiv |diagonalSSet (object L H)| |replacementDiagonal H| :=
  BisimplicialRealization.diagonalRealizationHomotopyEquiv (drop L H)
    (fun n ↦ dropRowHomotopyEquiv L H (op ⦋n⦌))
    (fun n ↦ dropRowHomotopyEquiv_toFun L H (op ⦋n⦌))

@[simp] theorem dropRealizationHomotopyEquiv_toFun :
    (dropRealizationHomotopyEquiv L H).toFun =
      (SSet.toTop.map (diagonalMap (drop L H))).hom := rfl

end SSet.TwoSidedBar

end

noncomputable section
open Topology TopCat SSet
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory Opposite
open scoped Simplicial Topology
universe u

namespace SSet.TwoSidedBar
open TheoremA

/-- The nerve of a discrete category is the actual constant simplicial set. -/
def discreteNerveIso (A : Type u) :
    nerve (Discrete A) ≅ (Functor.const SimplexCategoryᵒᵖ).obj A :=
  NatIso.ofComponents (fun p ↦ Equiv.toIso {
    toFun F := (F.obj 0).as
    invFun a := (Functor.const (Fin (p.unop.len + 1))).obj (Discrete.mk a)
    left_inv F := by
      refine CategoryTheory.Functor.ext (fun i ↦ Discrete.ext (Discrete.eq_of_hom (F.map
        (homOfLE (Fin.zero_le i))))) ?_
      intro i j f
      apply Subsingleton.elim
    right_inv _ := rfl }) (by
    intro p q α
    ext F : 3
    exact (Discrete.eq_of_hom (F.map (homOfLE (Fin.zero_le (α.unop.toOrderHom 0))))).symm)

variable (H : SimplexCategoryᵒᵖ ⥤ SSet.{u}) (q : SimplexCategoryᵒᵖ)

/-- The original evaluation functor is a classifying-space homotopy equivalence. -/
def resolutionEvaluationHomotopyEquiv :
    ContinuousMap.HomotopyEquiv (ClassifyingSpace (Resolution H q))
      (ClassifyingSpace (Discrete ((H.obj q).obj q))) where
  toFun := (classifyingSpaceMap (Resolution.evaluate H q)).hom
  invFun := (classifyingSpaceMap (Resolution.sectionFunctor H q)).hom
  left_inv := by
    have h := classifyingSpaceNaturalTransformationHomotopy (Resolution.contraction H q)
    exact ⟨by simpa only [classifyingSpaceMap_id, classifyingSpaceMap_comp, TopCat.hom_id,
      TopCat.hom_comp] using h.symm⟩
  right_inv := by
    have h := classifyingSpaceNaturalTransformationHomotopy (Resolution.sectionEvaluationIso H
      q).hom
    exact ⟨by simpa only [classifyingSpaceMap_id, classifyingSpaceMap_comp, TopCat.hom_id,
      TopCat.hom_comp] using h⟩

/-- In the actual column coordinates evaluation is precisely the discrete
augmentation functor, including every initial/final transport. -/
theorem columnIso_evaluation :
    (columnIso H q).hom ≫ ((flipFunctor _ _ _).map (evaluation H)).app q =
      nerveMap (Resolution.evaluate H q) ≫ (discreteNerveIso ((H.obj q).obj q)).hom := by
  apply NatTrans.ext
  funext p
  apply ConcreteCategory.hom_ext
  intro F
  change (H.map (indexProjection.map ((F ⋙ Resolution.forget H q).map
      (homOfLE (Fin.zero_le (Fin.last p.unop.len)))) ≫ (F.obj (Fin.last p.unop.len)).arrow)).app q
        (F.obj 0).value = (H.map (F.obj 0).arrow).app q (F.obj 0).value
  exact congrArg (fun α ↦ (H.map α).app q (F.obj 0).value)
    (F.map (homOfLE (Fin.zero_le (Fin.last p.unop.len)))).arrow

/-- Every actual transposed evaluation row is a realization equivalence. -/
theorem evaluationColumn_isRealizationEquivalence :
    IsRealizationEquivalence (((flipFunctor _ _ _).map (evaluation H)).app q) := by
  apply IsRealizationEquivalence.of_iso_square _ (nerveMap (Resolution.evaluate H q))
    (columnIso H q).symm (discreteNerveIso ((H.obj q).obj q)).symm
  · change ((flipFunctor _ _ _).map (evaluation H)).app q ≫
        (discreteNerveIso ((H.obj q).obj q)).inv =
      (columnIso H q).inv ≫ nerveMap (Resolution.evaluate H q)
    have h := congrArg (fun f ↦ (columnIso H q).inv ≫ f ≫
        (discreteNerveIso ((H.obj q).obj q)).inv) (columnIso_evaluation H q)
    simpa only [Category.assoc, Iso.inv_hom_id_assoc, Iso.hom_inv_id, Category.comp_id] using h
  · exact ⟨resolutionEvaluationHomotopyEquiv H q, rfl⟩

end SSet.TwoSidedBar

end
