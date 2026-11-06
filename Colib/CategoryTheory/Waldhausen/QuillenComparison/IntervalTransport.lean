/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Colib.CategoryTheory.Waldhausen.QuillenComparison.RowFull


/-! # Exact transport formulas for terminal interval spans -/
/- Adapted from the corresponding Quillen Q/S reconstruction source at
   c561118b7795eb9780be9ed391c3251d6a4d0afd. Native Colib objects are retained. -/
@[expose] public section


noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits
open scoped Simplicial
universe v u

namespace CategoryTheory.Waldhausen.QuillenComparison
open QuotientRows SSet

variable {C : Type u} [Category.{v} C] [Preadditive C] [HasFiniteBiproducts C]
variable (E : CategoryTheory.ExactCategory.ExactStructure C)

@[simp]
theorem qIsoOfIso_eqToIso {X Y : C} (h : X = Y) :
    (E.qIsoOfIso (eqToIso h)).hom =
      eqToHom (congrArg (QConstruction.of E.deflation E.inflation) h) := by
  subst Y
  rfl

/-- An interval arrow becomes the actual whole-row span after the displayed
source and target index identifications. -/
theorem rowInterval_map_to_whole {n : SimplexCategory} (F : Obj (ofExactCategory E) n)
    {a b : NestedInterval n} (f : a ⟶ b) (p : NestedInterval n)
    (ha : a = p) (hb : b = topNested n) :
    (intervalQFunctor E F).map f ≫
        (E.qIsoOfIso (eqToIso (congrArg (fun k ↦ F.obj.obj (nestedToInterval k)) hb))).hom =
      (E.qIsoOfIso (eqToIso (congrArg (fun k ↦ F.obj.obj (nestedToInterval k)) ha))).hom ≫
        QConstruction.mkHom E.deflation E.inflation (wholeSpan E F p) := by
  subst a
  subst b
  change QConstruction.mkHom E.deflation E.inflation (intervalSpan E F (leOfHom f)) ≫
    𝟙 _ = 𝟙 _ ≫ QConstruction.mkHom E.deflation E.inflation (wholeSpan E F p)
  rw [Category.id_comp, Category.comp_id]
  rfl

end CategoryTheory.Waldhausen.QuillenComparison
