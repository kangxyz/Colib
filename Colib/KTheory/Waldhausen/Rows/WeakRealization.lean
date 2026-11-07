/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.CategoryTheory.Waldhausen.Rows.NerveFunctoriality
public import Colib.KTheory.Waldhausen.Map
public import Colib.Topology.Homotopy.HomotopyGroup.WeakEquivalenceCancellation

/-! # Transport complete diagonal weakness to the original S-map

The genuine original-grid presentation is a natural simplicial isomorphism.
Conjugation by its actual realization homeomorphisms preserves the complete
weak property, including its component-surjectivity clause.

Implementation provenance:
`Quillen/Waldhausen/SConstruction/Rows/WeakRealization.lean`
at Quillen commit `c561118b7795eb9780be9ed391c3251d6a4d0afd`. Original maps,
hypotheses and universe parameters are retained.
-/
@[expose] public section

noncomputable section
open Topology TopCat SSet
open CategoryTheory
open scoped Simplicial
universe u v
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace CategoryTheory.Waldhausen.QuotientRows
variable {C D : Type u} [Category.{v} C] [Category.{v} D]
  {W : Structure C} {V : Structure D} {F : C ⥤ D}
  (hF : IsExact W.cof W.weq V.cof V.weq F)

/-- The forward grid presentation realizes to a genuine complete weak equivalence. -/
theorem sSetWeakRowDiagonalIso_isWeakHomotopyEquivalence :
    IsWeakHomotopyEquivalence (SSet.toTop.map (sSetWeakRowDiagonalIso W).hom).hom :=
  isWeakHomotopyEquivalence_of_homotopyEquiv
    (TopCat.homeoOfIso (SSet.toTop.mapIso (sSetWeakRowDiagonalIso W))).toHomotopyEquiv

/-- Complete weakness of the actual row-nerve diagonal map transfers to the
unchanged original delooping map, without introducing any chosen inverse. -/
theorem deloopingMap_isWeakHomotopyEquivalence_of_weakRowDiagonal
    (h : IsWeakHomotopyEquivalence
      (SSet.toTop.map (SSet.diagonalMap (weakRowNerveMap W V hF))).hom) :
    IsWeakHomotopyEquivalence (deloopingMap hF).hom := by
  have hc := h.comp (sSetWeakRowDiagonalIso_isWeakHomotopyEquivalence (W := W))
  have he : (SSet.toTop.map (SSet.diagonalMap (weakRowNerveMap W V hF))).hom.comp
      (SSet.toTop.map (sSetWeakRowDiagonalIso W).hom).hom =
      (SSet.toTop.map (sSetWeakRowDiagonalIso V).hom).hom.comp (deloopingMap hF).hom := by
    dsimp only [deloopingMap]
    rw [← TopCat.hom_comp, ← TopCat.hom_comp, ← SSet.toTop.map_comp, ← SSet.toTop.map_comp]
    exact congrArg (fun f ↦ (SSet.toTop.map f).hom) (sSetWeakRowDiagonalIso_naturality W V hF).symm
  rw [he] at hc
  exact hc.of_comp_right (sSetWeakRowDiagonalIso_isWeakHomotopyEquivalence (W := V))

end CategoryTheory.Waldhausen.QuotientRows
