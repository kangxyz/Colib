/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Colib.CategoryTheory.Waldhausen.ExtensionCategory.ArrowPushouts

/-! # Cofibration-arrow closure under displayed component pushouts

The new arrow is not assumed to be a cofibration. Its actual relative target
map is a cobase change of the original relative map, and supplies that conclusion.


Implementation provenance:
`Quillen/Waldhausen/SConstruction/Rows/RelativePushout.lean`
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

/-- Actual pointwise pushouts along a Reedy cofibration remain cofibration arrows. -/
theorem arrow_cof_of_pointwise_pushouts
    {X Y Z : ExtensionCategory.Obj W} {P : Arrow C}
    (f : X ⟶ Y) (g : X ⟶ Z) (i : Y.obj ⟶ P) (j : Z.obj ⟶ P)
    (hl : IsPushout f.hom.left g.hom.left i.left j.left)
    (hr : IsPushout f.hom.right g.hom.right i.right j.right)
    (hf : ExtensionCategory.cof W f) : W.cof P.hom := by
  obtain ⟨S, si, sj, hS⟩ := W.pushout_exists Z.obj.hom j.left Z.property
  let k : S ⟶ P.right := hS.desc j.right P.hom j.w.symm
  have hsi : si ≫ k = j.right := hS.inl_desc _ _ _
  have hsj : sj ≫ k = P.hom := hS.inr_desc _ _ _
  have hk : W.cof k := ExtensionCategory.relative_cof_of_pointwise_pushout W f.hom g.hom i j hl hr
    (Additivity.pushoutFunctor_isPushout W (ExtensionCategory.inclusion W)
      (ExtensionCategory.inclusion_cof W) (Arrow.mk f)) hS
    (Additivity.sourceι_comparison W (ExtensionCategory.inclusion W)
      (ExtensionCategory.inclusion_cof W) (Arrow.mk f))
    (Additivity.targetι_comparison W (ExtensionCategory.inclusion W)
      (ExtensionCategory.inclusion_cof W) (Arrow.mk f)) hsi hsj hf.2
  rw [← hsj]
  exact W.cof.comp_mem _ _ (W.cof_pushout Z.property hS) hk

end CategoryTheory.Waldhausen.QuotientRows
