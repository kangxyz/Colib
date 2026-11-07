/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Colib.CategoryTheory.ArrowDiagrams
public import Colib.CategoryTheory.Waldhausen.Rows.PostcomposeExact
public import Colib.CategoryTheory.Waldhausen.ArrowCategory.Structure
public import Colib.CategoryTheory.Waldhausen.ExtensionCategory.PostcomposeDetection

/-! # Actual interchange of quotient rows and pointwise arrows

Arrows between original quotient rows are exactly original quotient rows of
arrows. The two genuine Waldhausen structures agree by their actual component
and relative pushout tests, not by an assumed row-exactness statement.


Implementation provenance:
`Quillen/Waldhausen/SConstruction/Rows/PointwiseArrows.lean`
at Quillen commit `c561118b7795eb9780be9ed391c3251d6a4d0afd`. The original maps,
hypotheses, chosen zero objects and universe parameters are retained.
-/
@[expose] public section

noncomputable section
open CategoryTheory CategoryTheory.Limits
universe u v
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace CategoryTheory.Waldhausen.QuotientRows
variable {C : Type u} [Category.{v} C] (W : Structure C)

/-- Reedy cofibrations of pointwise arrows are detected by the two original
component Reedy squares, using the actual mapped relative pushouts. -/
theorem pointwiseExtension_cof_iff
    {X Y : ExtensionCategory.Obj (ArrowCategory.waldhausenStructure W)} (f : X ⟶ Y) :
    ExtensionCategory.cof (ArrowCategory.waldhausenStructure W) f ↔
      ExtensionCategory.cof W
        ((ExtensionCategory.postcompose _ W (ArrowCategory.source_exact W)).map f) ∧
      ExtensionCategory.cof W
        ((ExtensionCategory.postcompose _ W (ArrowCategory.target_exact W)).map f) := by
  constructor
  · intro h
    exact ⟨ExtensionCategory.postcompose_cof _ W (ArrowCategory.source_exact W) h,
      ExtensionCategory.postcompose_cof _ W (ArrowCategory.target_exact W) h⟩
  · rintro ⟨hl, hr⟩
    exact ⟨⟨hl.1, hr.1⟩,
      ⟨ExtensionCategory.mapped_relative_cof _ W (ArrowCategory.source_exact W) hl,
        ExtensionCategory.mapped_relative_cof _ W (ArrowCategory.target_exact W) hr⟩⟩

/-- The literal diagram underlying an arbitrary arrow between quotient rows. -/
def arrowDiagram (n : SimplexCategory) : Arrow (Obj W n) ⥤ (Interval n ⥤ Arrow C) :=
  (forget W n).mapArrow ⋙ ArrowDiagrams.toDiagram

/-- Original source and target row axioms give the actual arrow-valued row axioms. -/
theorem arrowDiagram_isRow {n : SimplexCategory} (X : Arrow (Obj W n)) :
    IsRow (ArrowCategory.waldhausenStructure W) ((arrowDiagram W n).obj X) where
  zero i := ArrowCategory.isZero_of_components _ (X.left.property.zero i) (X.right.property.zero i)
  cofibration i j k hij hjk :=
    ⟨X.left.property.cofibration i j k hij hjk, X.right.property.cofibration i j k hij hjk⟩
  quotient i j k hij hjk := ExtensionCategory.arrow_isPushout _ _ _ _
    (X.left.property.quotient i j k hij hjk) (X.right.property.quotient i j k hij hjk)

/-- Arrows of actual quotient rows are sent to their original component-arrow diagrams. -/
def arrowToRows (n : SimplexCategory) :
    Arrow (Obj W n) ⥤ Obj (ArrowCategory.waldhausenStructure W) n where
  obj X := ⟨(arrowDiagram W n).obj X, arrowDiagram_isRow W X⟩
  map f := (objects _ n).homMk ((arrowDiagram W n).map f)
  map_id X := by apply ObjectProperty.hom_ext; exact (arrowDiagram W n).map_id X
  map_comp f g := by apply ObjectProperty.hom_ext; exact (arrowDiagram W n).map_comp f g

/-- The original component arrows form a natural transformation between the
source and target quotient-row functors. -/
def rowsArrowTransformation (n : SimplexCategory) :
    postcompose (ArrowCategory.waldhausenStructure W) W (ArrowCategory.source_exact W) n ⟶
      postcompose (ArrowCategory.waldhausenStructure W) W (ArrowCategory.target_exact W) n where
  app X := (objects W n).homMk (Functor.whiskerLeft X.obj Arrow.leftToRight)
  naturality X Y f := by
    apply ObjectProperty.hom_ext
    ext p
    exact (f.hom.app p).w

/-- Arrow-valued quotient rows are sent to the original natural-transformation arrow. -/
def rowsToArrow (n : SimplexCategory) :
    Obj (ArrowCategory.waldhausenStructure W) n ⥤ Arrow (Obj W n) :=
  ArrowDiagrams.toDiagramObj (Arrow.mk (rowsArrowTransformation W n))

@[simp] theorem arrowToRows_obj_hom {n : SimplexCategory} (X : Arrow (Obj W n)) (p : Interval n) :
    (((arrowToRows W n).obj X).obj.obj p).hom = X.hom.hom.app p := rfl
@[simp] theorem rowsToArrow_obj_hom_app {n : SimplexCategory}
    (X : Obj (ArrowCategory.waldhausenStructure W) n) (p : Interval n) :
    ((rowsToArrow W n).obj X).hom.hom.app p = (X.obj.obj p).hom := rfl

@[simp] theorem arrowToRows_rowsToArrow (n : SimplexCategory) :
    arrowToRows W n ⋙ rowsToArrow W n = 𝟭 _ := by
  apply CategoryTheory.Functor.ext (fun _ ↦ rfl)
@[simp] theorem rowsToArrow_arrowToRows (n : SimplexCategory) :
    rowsToArrow W n ⋙ arrowToRows W n = 𝟭 _ := by
  apply CategoryTheory.Functor.ext (fun _ ↦ rfl)

/-- The genuine categorical equivalence retains the literal original component diagrams. -/
def pointwiseArrowEquivalence (n : SimplexCategory) :
    Arrow (Obj W n) ≌ Obj (ArrowCategory.waldhausenStructure W) n :=
  CategoryTheory.Equivalence.mk (arrowToRows W n) (rowsToArrow W n)
    (eqToIso (arrowToRows_rowsToArrow W n).symm) (eqToIso (rowsToArrow_arrowToRows W n))

/-- The actual component-row arrow detects every genuine row relative test. -/
theorem cof_of_rowsToArrow {n : SimplexCategory}
    {X Y : Obj (ArrowCategory.waldhausenStructure W) n} {f : X ⟶ Y}
    (hf : ArrowCategory.cof (waldhausenStructure W n) ((rowsToArrow W n).map f)) :
    cof (ArrowCategory.waldhausenStructure W) n f := by
  intro i j k hij hjk
  apply (pointwiseExtension_cof_iff W _).2
  exact ⟨hf.1 i j k hij hjk, hf.2 i j k hij hjk⟩

/-- Collecting the original arrow components is genuinely exact. -/
theorem rowsToArrow_exact (n : SimplexCategory) :
    IsExact (waldhausenStructure (ArrowCategory.waldhausenStructure W) n).cof
      (waldhausenStructure (ArrowCategory.waldhausenStructure W) n).weq
      (ArrowCategory.waldhausenStructure (waldhausenStructure W n)).cof
      (ArrowCategory.waldhausenStructure (waldhausenStructure W n)).weq (rowsToArrow W n) where
  zero h := ArrowCategory.isZero_of_components _
    ((postcompose_exact _ W (ArrowCategory.source_exact W) n).zero h)
    ((postcompose_exact _ W (ArrowCategory.target_exact W) n).zero h)
  cofibration _ h :=
    ⟨(postcompose_exact _ W (ArrowCategory.source_exact W) n).cofibration _ h,
      (postcompose_exact _ W (ArrowCategory.target_exact W) n).cofibration _ h⟩
  weak _ h := ⟨fun p ↦ (h p).1, fun p ↦ (h p).2⟩
  pushout hf h := ExtensionCategory.arrow_isPushout _ _ _ _
    ((postcompose_exact _ W (ArrowCategory.source_exact W) n).pushout hf h)
    ((postcompose_exact _ W (ArrowCategory.target_exact W) n).pushout hf h)

/-- Sending an original row arrow to its component diagram is genuinely exact. -/
theorem arrowToRows_exact (n : SimplexCategory) :
    IsExact (ArrowCategory.waldhausenStructure (waldhausenStructure W n)).cof
      (ArrowCategory.waldhausenStructure (waldhausenStructure W n)).weq
      (waldhausenStructure (ArrowCategory.waldhausenStructure W) n).cof
      (waldhausenStructure (ArrowCategory.waldhausenStructure W) n).weq (arrowToRows W n) where
  zero h := isZero_of_components _ _ (fun p ↦ ArrowCategory.isZero_of_components _
    (evaluation_isZero W ((ArrowCategory.source_exact (waldhausenStructure W n)).zero h) p)
    (evaluation_isZero W ((ArrowCategory.target_exact (waldhausenStructure W n)).zero h) p))
  cofibration _ h := cof_of_rowsToArrow W h
  weak _ h p := ⟨h.1 p, h.2 p⟩
  pushout hf h := by
    obtain ⟨hl, hr⟩ := ArrowCategory.pointwise_of_isPushout (waldhausenStructure W n) hf h
    exact isPushout_of_pointwise _ _ _ _ _ (fun p ↦ ExtensionCategory.arrow_isPushout _ _ _ _
      (pointwise_of_isPushout W hf.1 hl p) (pointwise_of_isPushout W hf.2 hr p))

end CategoryTheory.Waldhausen.QuotientRows
