/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Colib.CategoryTheory.Waldhausen.Rows.ReedyArrows

/-! # The genuine quotient-row lift of an exact joint-arrow functor

The lift uses the proved pointwise-arrow interchange, exact postcomposition,
and genuine Reedy-arrow interchange. Its original component maps and every
ordinal restriction are retained literally.


Implementation provenance:
`Quillen/Waldhausen/SConstruction/Rows/JointFunctor.lean`
at Quillen commit `c561118b7795eb9780be9ed391c3251d6a4d0afd`. The original maps,
hypotheses, chosen zero objects and universe parameters are retained.
-/
@[expose] public section

noncomputable section
open CategoryTheory CategoryTheory.Limits
universe u v u' v'
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace CategoryTheory.Waldhausen.QuotientRows
variable {C : Type u} [Category.{v} C] (V : Structure C)

@[simp] theorem arrowToRows_reindex {m n : SimplexCategory} (α : m ⟶ n) :
    (reindex V α).mapArrow ⋙ arrowToRows V m =
      arrowToRows V n ⋙ reindex (ArrowCategory.waldhausenStructure V) α := by
  apply CategoryTheory.Functor.ext (fun _ ↦ rfl)
@[simp] theorem rowsToArrow_reindex {m n : SimplexCategory} (α : m ⟶ n) :
    rowsToArrow V n ⋙ (reindex V α).mapArrow =
      reindex (ArrowCategory.waldhausenStructure V) α ⋙ rowsToArrow V m := by
  apply CategoryTheory.Functor.ext (fun _ ↦ rfl)
@[simp] theorem reedyToRows_reindex {m n : SimplexCategory} (α : m ⟶ n) :
    ExtensionCategory.postcompose _ _ (reindex_exact V α) ⋙ reedyToRows V m =
      reedyToRows V n ⋙ reindex (ExtensionCategory.waldhausenStructure V) α := by
  apply CategoryTheory.Functor.ext (fun _ ↦ rfl)
@[simp] theorem rowsToReedy_reindex {m n : SimplexCategory} (α : m ⟶ n) :
    rowsToReedy V n ⋙ ExtensionCategory.postcompose _ _ (reindex_exact V α) =
      reindex (ExtensionCategory.waldhausenStructure V) α ⋙ rowsToReedy V m := by
  apply CategoryTheory.Functor.ext (fun _ ↦ rfl)

variable {D : Type u'} [Category.{v'} D] (W : Structure D)
  {J : Arrow C ⥤ ExtensionCategory.Obj W}
  (hJ : IsExact (ArrowCategory.waldhausenStructure V).cof
    (ArrowCategory.waldhausenStructure V).weq
    (ExtensionCategory.waldhausenStructure W).cof
    (ExtensionCategory.waldhausenStructure W).weq J)

/-- The original exact joint-arrow functor acts on all quotient rows. -/
def jointOnRows (n : SimplexCategory) :
    Arrow (Obj V n) ⥤ ExtensionCategory.Obj (waldhausenStructure W n) :=
  arrowToRows V n ⋙ postcompose (ArrowCategory.waldhausenStructure V)
    (ExtensionCategory.waldhausenStructure W) hJ n ⋙ rowsToReedy W n

/-- The actual lifted joint-arrow functor is genuinely exact. -/
theorem jointOnRows_exact (n : SimplexCategory) :
    IsExact (ArrowCategory.waldhausenStructure (waldhausenStructure V n)).cof
      (ArrowCategory.waldhausenStructure (waldhausenStructure V n)).weq
      (ExtensionCategory.waldhausenStructure (waldhausenStructure W n)).cof
      (ExtensionCategory.waldhausenStructure (waldhausenStructure W n)).weq (jointOnRows V W hJ
        n) :=
  (arrowToRows_exact V n).comp
    ((postcompose_exact _ _ hJ n).comp (rowsToReedy_exact W n))

/-- The lift retains the actual joint map at every original quotient component. -/
@[simp] theorem jointOnRows_obj_hom_app {n : SimplexCategory} (X : Arrow (Obj V n)) (p :
    Interval n) :
    ((jointOnRows V W hJ n).obj X).obj.hom.hom.app p =
      (J.obj (Arrow.mk (X.hom.hom.app p))).obj.hom := rfl

/-- The lift retains the two actual maps of each original component square. -/
@[simp] theorem jointOnRows_map_left_app {n : SimplexCategory} {X Y : Arrow (Obj V n)}
    (f : X ⟶ Y) (p : Interval n) :
    ((jointOnRows V W hJ n).map f).hom.left.hom.app p =
      (J.map (((arrowDiagram V n).map f).app p)).hom.left := rfl
@[simp] theorem jointOnRows_map_right_app {n : SimplexCategory} {X Y : Arrow (Obj V n)}
    (f : X ⟶ Y) (p : Interval n) :
    ((jointOnRows V W hJ n).map f).hom.right.hom.app p =
      (J.map (((arrowDiagram V n).map f).app p)).hom.right := rfl

/-- Every ordinal restriction commutes strictly with the original lifted functor. -/
@[simp] theorem jointOnRows_reindex {m n : SimplexCategory} (α : m ⟶ n) :
    (reindex V α).mapArrow ⋙ jointOnRows V W hJ m =
      jointOnRows V W hJ n ⋙ ExtensionCategory.postcompose _ _ (reindex_exact W α) := by
  apply CategoryTheory.Functor.ext (fun _ ↦ rfl)

end CategoryTheory.Waldhausen.QuotientRows
