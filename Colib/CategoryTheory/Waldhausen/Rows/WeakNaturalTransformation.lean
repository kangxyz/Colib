/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.CategoryTheory.Waldhausen.Rows.NerveFunctoriality

/-! # Actual weak natural transformations on quotient rows

Components are the original transformation evaluated at each quotient object.
Pointwise weakness is enough; no row-level Reedy structure is used.
-/
@[expose] public section
noncomputable section
open CategoryTheory CategoryTheory.Limits
universe v u
namespace CategoryTheory.Waldhausen.QuotientRows

variable {C D : Type u} [Category.{v} C] [Category.{v} D]
  (V : Structure C) (W : Structure D) {F G : C ⥤ D}
  (hF : IsExact V.cof V.weq W.cof W.weq F)
  (hG : IsExact V.cof V.weq W.cof W.weq G)
  (η : F ⟶ G) (hη : ∀ X, W.weq (η.app X))

/-- Original weak components restrict to an actual transformation of weak-row functors. -/
def weakRowsPostcomposeTransformation (n : SimplexCategory) :
    weakRowsPostcompose V W hF n ⟶ weakRowsPostcompose V W hG n where
  app X := ⟨(objects W n).homMk (Functor.whiskerLeft X.obj.obj η),
    fun p ↦ hη (X.obj.obj.obj p)⟩
  naturality X Y f := by
    apply WideSubcategory.hom_ext
    apply ObjectProperty.hom_ext
    ext p
    exact η.naturality (f.hom.hom.app p)

/-- Every row component is precisely the original transformation component. -/
@[simp] theorem weakRowsPostcomposeTransformation_app
    (n : SimplexCategory) (X : WeakRows V n) (p : Interval n) :
    ((weakRowsPostcomposeTransformation V W hF hG η hη n).app X).hom.hom.app p =
      η.app (X.obj.obj.obj p) := rfl

/-- Restriction retains the very same transformation component at the reindexed interval. -/
theorem weakRowsPostcomposeTransformation_reindex_app
    {n m : SimplexCategory} (α : m ⟶ n) (X : WeakRows V n) (p : Interval m) :
    ((weakRowsPostcomposeTransformation V W hF hG η hη m).app
      ((weakRowsReindex V α).obj X)).hom.hom.app p =
    ((weakRowsPostcomposeTransformation V W hF hG η hη n).app X).hom.hom.app
      ((indexMap α).obj p) := rfl

end CategoryTheory.Waldhausen.QuotientRows
