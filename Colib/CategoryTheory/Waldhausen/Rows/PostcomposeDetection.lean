/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Colib.CategoryTheory.Waldhausen.Rows.Functoriality
public import Colib.CategoryTheory.Waldhausen.Rows.PostcomposeExact
public import Colib.CategoryTheory.Waldhausen.ExtensionCategory.PostcomposeDetection

/-! # Reflecting actual row cofibrations through an exact inclusion

The concrete ambient cofibration reflection is lifted through the actual
mapped relative pushouts on every original horizontal-arrow test.


Implementation provenance:
`Quillen/Waldhausen/SConstruction/Rows/PostcomposeDetection.lean`
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
variable {C : Type u} [Category.{v} C] {D : Type u'} [Category.{v'} D]
variable (V : Structure C) (W : Structure D) {F : C ⥤ D}
  (hF : IsExact V.cof V.weq W.cof W.weq F)

/-- Actual reflection of ambient cofibrations detects every original relative row test. -/
theorem cof_of_postcompose
    (detect : ∀ ⦃A B : C⦄ (f : A ⟶ B), W.cof (F.map f) → V.cof f)
    {n : SimplexCategory} {A B : Obj V n} {η : A ⟶ B}
    (hη : cof W n ((postcompose V W hF n).map η)) : cof V n η := by
  intro i j k hij hjk
  exact ExtensionCategory.cof_of_postcompose V W hF detect (hη i j k hij hjk)

/-- An exact functor which reflects ambient cofibrations also reflects and
preserves the actual all-triples Reedy row cofibration class. -/
theorem postcompose_cof_iff
    (detect : ∀ ⦃A B : C⦄ (f : A ⟶ B), W.cof (F.map f) → V.cof f)
    {n : SimplexCategory} {A B : Obj V n} (η : A ⟶ B) :
    cof W n ((postcompose V W hF n).map η) ↔ cof V n η :=
  ⟨cof_of_postcompose V W hF detect, postcompose_cof V W hF⟩

end CategoryTheory.Waldhausen.QuotientRows
