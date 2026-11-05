/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Colib.CategoryTheory.Waldhausen.Rows.Reindex
public import Colib.CategoryTheory.Waldhausen.ExactFunctor

/-! # Genuine exact-functor postcomposition of quotient rows

Postcomposition preserves row objects and pointwise weak maps directly from
the exact functor. No row-level Reedy structure is needed for the nerve comparison.
-/
/- Implementation provenance: adapted from
   Quillen/Waldhausen/SConstruction/Rows/Functoriality.lean
   at c561118b7795eb9780be9ed391c3251d6a4d0afd.
   Isolated strict compilation is recorded in the accompanying release report. -/
@[expose] public section

noncomputable section
open CategoryTheory CategoryTheory.Limits
universe u v u' v' u'' v''
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace CategoryTheory.Waldhausen.QuotientRows
variable {C : Type u} [Category.{v} C] {D : Type u'} [Category.{v'} D]
  {E : Type u''} [Category.{v''} E]
variable (V : Structure C) (W : Structure D) {F : C ⥤ D}
  (hF : IsExact V.cof V.weq W.cof W.weq F)

include hF in
/-- Exactness maps the original zero, cofibration, and quotient-square predicates. -/
theorem IsRow.postcomp {n : SimplexCategory} {A : Interval n ⥤ C} (hA : IsRow V A) :
    IsRow W (A ⋙ F) where
  zero i := hF.zero (hA.zero i)
  cofibration i j k hij hjk := hF.cofibration _ (hA.cofibration i j k hij hjk)
  quotient i j k hij hjk := hF.pushout (hA.cofibration i j k hij hjk) (hA.quotient i j k hij hjk)

/-- The actual quotient-row functor is postcomposition on every diagram and map. -/
def postcompose (n : SimplexCategory) : Obj V n ⥤ Obj W n where
  obj A := ⟨A.obj ⋙ F, A.property.postcomp V W hF⟩
  map η := (objects W n).homMk (Functor.whiskerRight η.hom F)
  map_id A := by
    apply ObjectProperty.hom_ext
    ext p
    exact F.map_id (A.obj.obj p)
  map_comp η θ := by
    apply ObjectProperty.hom_ext
    ext p
    exact F.map_comp (η.hom.app p) (θ.hom.app p)

@[simp] theorem postcompose_obj_diagram (n : SimplexCategory) (A : Obj V n) :
    ((postcompose V W hF n).obj A).obj = A.obj ⋙ F := rfl
@[simp] theorem postcompose_map_app {n : SimplexCategory} {A B : Obj V n}
    (η : A ⟶ B) (p : Interval n) :
    ((postcompose V W hF n).map η).hom.app p = F.map (η.hom.app p) := rfl

/-- Exact postcomposition preserves the actual pointwise weak maps. -/
theorem postcompose_weq {n : SimplexCategory} {A B : Obj V n} {η : A ⟶ B}
    (hη : weq V n η) : weq W n ((postcompose V W hF n).map η) := by
  intro p
  exact hF.weak _ (hη p)

@[simp] theorem postcompose_evaluation {n : SimplexCategory} (p : Interval n) :
    postcompose V W hF n ⋙ evaluation W p = evaluation V p ⋙ F := by
  apply CategoryTheory.Functor.ext (fun _ ↦ rfl)

/-- Postcomposition commutes strictly with every original ordinal restriction. -/
@[simp] theorem postcompose_reindex {m n : SimplexCategory} (α : m ⟶ n) :
    postcompose V W hF n ⋙ reindex W α = reindex V α ⋙ postcompose V W hF m := by
  apply CategoryTheory.Functor.ext (fun _ ↦ rfl)

@[simp] theorem postcompose_id (n : SimplexCategory) :
    postcompose V V (IsExact.id V.cof V.weq) n = 𝟭 (Obj V n) := by
  apply CategoryTheory.Functor.ext (fun _ ↦ rfl)

/-- Composition simplifies by combining the two displayed maps with their actual intermediate data.
-/
@[simp] theorem postcompose_comp_postcompose (U : Structure E) {G : D ⥤ E}
    (hG : IsExact W.cof W.weq U.cof U.weq G) (n : SimplexCategory) :
    postcompose V W hF n ⋙ postcompose W U hG n =
      postcompose V U (hF.comp hG) n := by
  apply CategoryTheory.Functor.ext (fun _ ↦ rfl)


end CategoryTheory.Waldhausen.QuotientRows
