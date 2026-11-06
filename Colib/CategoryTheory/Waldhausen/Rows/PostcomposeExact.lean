/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Colib.CategoryTheory.Waldhausen.Rows.Functoriality
public import Colib.CategoryTheory.Waldhausen.Rows.ReindexExact
public import Colib.CategoryTheory.Waldhausen.ExtensionCategory.Functoriality

/-! # Exact postcomposition on the existing quotient rows

Implementation provenance: `Quillen/Waldhausen/SConstruction/Rows/Functoriality.lean`
at commit `c561118b7795eb9780be9ed391c3251d6a4d0afd`, Reedy exactness declarations.
-/
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

/-- Every actual horizontal relative cofibration test is preserved. -/
theorem postcompose_cof {n : SimplexCategory} {A B : Obj V n} {η : A ⟶ B} (hη : cof V n η) :
    cof W n ((postcompose V W hF n).map η) := by
  intro i j k hij hjk
  exact ExtensionCategory.postcompose_cof V W hF (hη i j k hij hjk)

/-- The row functor induced by a genuine exact functor is genuinely exact. -/
theorem postcompose_exact (n : SimplexCategory) :
    IsExact (waldhausenStructure V n).cof (waldhausenStructure V n).weq
      (waldhausenStructure W n).cof (waldhausenStructure W n).weq (postcompose V W hF n) where
  zero h := isZero_of_components W _ (fun p ↦ hF.zero (evaluation_isZero V h p))
  cofibration _ h := postcompose_cof V W hF h
  weak _ h p := hF.weak _ (h p)
  pushout hf h := isPushout_of_pointwise W _ _ _ _
    (fun p ↦ hF.pushout (cof_app V hf p) (pointwise_of_isPushout V hf h p))

@[simp] theorem postcompose_horizontalArrow {n : SimplexCategory}
    (i j k : Fin (n.len + 1)) (hij : i ≤ j) (hjk : j ≤ k) :
    postcompose V W hF n ⋙ horizontalArrow W i j k hij hjk =
      horizontalArrow V i j k hij hjk ⋙ ExtensionCategory.postcompose V W hF := by
  apply CategoryTheory.Functor.ext (fun _ ↦ rfl)

end CategoryTheory.Waldhausen.QuotientRows
