/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Mathlib.CategoryTheory.Comma.Arrow

/-! # The actual equivalence between arrows of diagrams and diagrams of arrows

Both directions retain the original component maps. No choice of replacement
objects or quotient diagrams occurs in this categorical interchange.


Implementation provenance:
`Quillen/Aglib/CategoryTheory/ArrowDiagrams.lean`
at Quillen commit `c561118b7795eb9780be9ed391c3251d6a4d0afd`. The original maps,
hypotheses, chosen zero objects and universe parameters are retained.
-/
@[expose] public section

noncomputable section
open CategoryTheory
universe u v u' v'
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace CategoryTheory.ArrowDiagrams
variable {C : Type u} [Category.{v} C] {J : Type u'} [Category.{v'} J]

/-- Evaluate a natural-transformation arrow at every original index. -/
def toDiagramObj (X : Arrow (J ⥤ C)) : J ⥤ Arrow C where
  obj j := Arrow.mk (X.hom.app j)
  map f := Arrow.homMk (X.left.map f) (X.right.map f) (X.hom.naturality f)
  map_id j := by apply Arrow.hom_ext <;> exact CategoryTheory.Functor.map_id _ j
  map_comp f g := by apply Arrow.hom_ext <;> exact CategoryTheory.Functor.map_comp _ f g

/-- A square of natural transformations is sent to its original component squares. -/
def toDiagramMap {X Y : Arrow (J ⥤ C)} (a : X ⟶ Y) : toDiagramObj X ⟶ toDiagramObj Y where
  app j := Arrow.homMk (a.left.app j) (a.right.app j) (congrArg (fun k ↦ k.app j) a.w)
  naturality _ _ f := by
    apply Arrow.hom_ext
    · exact a.left.naturality f
    · exact a.right.naturality f

/-- The actual arrow-to-diagram functor. -/
def toDiagram : Arrow (J ⥤ C) ⥤ (J ⥤ Arrow C) where
  obj := toDiagramObj
  map := toDiagramMap
  map_id _ := by ext j <;> rfl
  map_comp _ _ := by ext j <;> rfl

/-- Collect the original diagram of arrows into a natural transformation. -/
def toArrowObj (X : J ⥤ Arrow C) : Arrow (J ⥤ C) :=
  Arrow.mk (Functor.whiskerLeft X Arrow.leftToRight)

/-- Collect a transformation of arrow diagrams into the original commutative square. -/
def toArrowMap {X Y : J ⥤ Arrow C} (a : X ⟶ Y) : toArrowObj X ⟶ toArrowObj Y :=
  Arrow.homMk (Functor.whiskerRight a Arrow.leftFunc) (Functor.whiskerRight a Arrow.rightFunc)
    (by ext j; exact (a.app j).w)

/-- The actual diagram-to-arrow functor. -/
def toArrow : (J ⥤ Arrow C) ⥤ Arrow (J ⥤ C) where
  obj := toArrowObj
  map := toArrowMap
  map_id _ := by apply Arrow.hom_ext <;> rfl
  map_comp _ _ := by apply Arrow.hom_ext <;> rfl

@[simp] theorem toDiagram_obj_hom (X : Arrow (J ⥤ C)) (j : J) :
    ((toDiagram.obj X).obj j).hom = X.hom.app j := rfl
@[simp] theorem toDiagram_map_app_left {X Y : Arrow (J ⥤ C)} (a : X ⟶ Y) (j : J) :
    ((toDiagram.map a).app j).left = a.left.app j := rfl
@[simp] theorem toDiagram_map_app_right {X Y : Arrow (J ⥤ C)} (a : X ⟶ Y) (j : J) :
    ((toDiagram.map a).app j).right = a.right.app j := rfl
@[simp] theorem toArrow_obj_hom_app (X : J ⥤ Arrow C) (j : J) :
    (toArrow.obj X).hom.app j = (X.obj j).hom := rfl

@[simp] theorem toDiagram_toArrow :
    (toDiagram : Arrow (J ⥤ C) ⥤ (J ⥤ Arrow C)) ⋙ toArrow = 𝟭 _ := by
  apply CategoryTheory.Functor.ext (fun _ ↦ rfl)
@[simp] theorem toArrow_toDiagram :
    (toArrow : (J ⥤ Arrow C) ⥤ Arrow (J ⥤ C)) ⋙ toDiagram = 𝟭 _ := by
  apply CategoryTheory.Functor.ext (fun _ ↦ rfl)

/-- The equivalence is the literal component-diagram interchange. -/
def equivalence (J : Type u') [Category.{v'} J] (C : Type u) [Category.{v} C] :
    Arrow (J ⥤ C) ≌ (J ⥤ Arrow C) :=
  CategoryTheory.Equivalence.mk toDiagram toArrow
    (eqToIso toDiagram_toArrow.symm) (eqToIso toArrow_toDiagram)

end CategoryTheory.ArrowDiagrams
