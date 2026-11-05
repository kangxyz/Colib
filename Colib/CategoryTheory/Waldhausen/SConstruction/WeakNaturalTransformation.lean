/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Colib.CategoryTheory.Waldhausen.SConstruction.WeakGridHomotopy

/-! # Weak natural transformations give actual S-construction homotopies

The endpoints are the existing postcomposition maps of the original exact
functors. The construction uses the genuine nerve-direction cylinder.
-/
/- Implementation provenance: adapted from
   Quillen/Waldhausen/SConstruction/WeakNaturalTransformation.lean
   at c561118b7795eb9780be9ed391c3251d6a4d0afd.
   Validation status is recorded in the accompanying release report. -/
@[expose] public section


noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor Opposite MonoidalCategory
open scoped Simplicial
universe v u

namespace CategoryTheory.Waldhausen

variable {C D : Type u} [Category.{v} C] [Category.{v} D]
  (V : Structure C) (W : Structure D) {F G : C ⥤ D}
  (hF : IsExact V.cof V.weq W.cof W.weq F)
  (hG : IsExact V.cof V.weq W.cof W.weq G)
  (η : F ⟶ G) (hη : ∀ X, W.weq (η.app X))

/-- The actual cylinder between the existing S-construction postcomposition maps. -/
def weakNaturalTransformationCylinder : sSet V.cof V.weq ⊗ Δ[1] ⟶ sSet W.cof W.weq :=
  ((bisimplicialDiagonalIso V).inv ▷ Δ[1]) ≫
    weakGridFamilyCylinder W (bisimplicialSSetMap V.cof V.weq hF)
      (bisimplicialSSetMap V.cof V.weq hG)
      (fun _ _ A ↦ whiskerLeft A.1 η) (fun _ _ A p ↦ hη (A.1.obj p))
      (fun _ _ _ ↦ HEq.rfl) ≫ (bisimplicialDiagonalIso W).hom

/-- The cylinder acts on the canonical product of the two simplex types. -/
@[simp] theorem weakNaturalTransformationCylinder_app_hom_val (n : SimplexCategoryᵒᵖ) (z : (sSet
    V.cof V.weq).obj n × (Δ[1]).obj n) :
    (TypeCat.Hom.hom (X := (sSet V.cof V.weq).obj n × (Δ[1]).obj n)
      ((weakNaturalTransformationCylinder V W hF hG η hη).app n) z).val =
      nerveCylinderDiagram (whiskerLeft z.1.1 η) z.2.down := rfl


@[simp] theorem weakNaturalTransformationCylinder_zero :
    SSet.ι₀ ≫ weakNaturalTransformationCylinder V W hF hG η hη = sSetMap hF := by
  ext n A
  apply Subtype.ext
  exact nerveCylinderDiagram_zero (whiskerLeft A.1 η)

@[simp] theorem weakNaturalTransformationCylinder_one :
    SSet.ι₁ ≫ weakNaturalTransformationCylinder V W hF hG η hη = sSetMap hG := by
  ext n A
  apply Subtype.ext
  exact nerveCylinderDiagram_one (whiskerLeft A.1 η)

/-- Pointwise weak transformations between genuine exact functors induce a
simplicial homotopy of their original S-maps. -/
def weakNaturalTransformationHomotopy : SSet.Homotopy (sSetMap hF) (sSetMap hG) where
  h := weakNaturalTransformationCylinder V W hF hG η hη
  h₀ := weakNaturalTransformationCylinder_zero V W hF hG η hη
  h₁ := weakNaturalTransformationCylinder_one V W hF hG η hη
  rel := by ext n z; exact z.1.property.elim

end CategoryTheory.Waldhausen

attribute [colib_tag "COL-0156",
  colib_ref "Waldhausen1985" "Section 1.3, pp. 328-330" "background"
    "Background for the stated unnormalized IsZero model; not a strict-model identification"]
  CategoryTheory.Waldhausen.weakNaturalTransformationHomotopy
