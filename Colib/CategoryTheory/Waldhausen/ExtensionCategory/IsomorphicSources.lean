/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Colib.CategoryTheory.Waldhausen.ExtensionCategory.Structure

/-! # Actual relative cofibrations with isomorphic sources

The relative pushout leg is an isomorphism when the original source map is.
Thus its actual comparison is the target map composed with that inverse.
No chosen pushout is replaced by an assumed relative condition.


Implementation provenance:
`Quillen/Waldhausen/ExtensionCategory/IsomorphicSources.lean`
at Quillen commit `c561118b7795eb9780be9ed391c3251d6a4d0afd`. The original maps,
hypotheses, chosen zero objects and universe parameters are retained.
-/
@[expose] public section

noncomputable section
open CategoryTheory CategoryTheory.Limits
universe u v
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace CategoryTheory.Waldhausen.ExtensionCategory
variable {C : Type u} [Category.{v} C] (W : Structure C)

/-- A genuine source isomorphism makes the Reedy condition exactly target cofibrancy. -/
theorem cof_of_left_isIso {X Y : Obj W} (f : X ⟶ Y) [IsIso f.hom.left]
    (hf : W.cof f.hom.right) : cof W f := by
  refine ⟨W.cof_iso _ (inferInstance : IsIso f.hom.left), ?_⟩
  let s := Additivity.sourceι W (inclusion W) (inclusion_cof W) (Arrow.mk f)
  let : IsIso ((source W).map (Arrow.mk f).hom) := inferInstanceAs (IsIso f.hom.left)
  let : IsIso s :=
    (Additivity.pushoutFunctor_isPushout W (inclusion W) (inclusion_cof W) (Arrow.mk
      f)).isIso_inl_of_isIso
  have h : relativeMap W f = inv s ≫ f.hom.right := by
    apply (cancel_epi s).1
    simp only [← Category.assoc, IsIso.hom_inv_id, Category.id_comp]
    exact Additivity.sourceι_comparison W (inclusion W) (inclusion_cof W) (Arrow.mk f)
  rw [h]
  exact W.cof.comp_mem _ _ (W.cof_iso _ (inferInstance : IsIso (inv s))) hf

/-- If the original upper arrow is an isomorphism, source cofibrancy already implies the genuine
relative condition. -/
theorem cof_of_top_isIso {X Y : Obj W} (f : X ⟶ Y) [IsIso X.obj.hom]
    (hf : W.cof f.hom.left) : cof W f := by
  refine ⟨hf, ?_⟩
  let j := Additivity.targetι W (inclusion W) (inclusion_cof W) (Arrow.mk f)
  let : IsIso ((inclusion W).app (Arrow.mk f).left) := inferInstanceAs (IsIso X.obj.hom)
  let : IsIso j :=
    (Additivity.pushoutFunctor_isPushout W (inclusion W) (inclusion_cof W) (Arrow.mk
      f)).isIso_inr_of_isIso
  have h : relativeMap W f = inv j ≫ Y.obj.hom := by
    apply (cancel_epi j).1
    simp only [← Category.assoc, IsIso.hom_inv_id, Category.id_comp]
    exact Additivity.targetι_comparison W (inclusion W) (inclusion_cof W) (Arrow.mk f)
  rw [h]
  exact W.cof.comp_mem _ _ (W.cof_iso _ (inferInstance : IsIso (inv j))) Y.property

/-- A choice-free equivalence on the original square. -/
theorem cof_iff_of_left_isIso {X Y : Obj W} (f : X ⟶ Y) [IsIso f.hom.left] :
    cof W f ↔ W.cof f.hom.right := ⟨cof_middle W, cof_of_left_isIso W f⟩

/-- In particular, between actual zero-source arrows the target detects the genuine relative
condition. -/
theorem cof_of_zero_sources {X Y : Obj W} (f : X ⟶ Y)
    (hX : IsZero X.obj.left) (hY : IsZero Y.obj.left) (hf : W.cof f.hom.right) : cof W f := by
  let : IsIso f.hom.left := hX.isIso hY _
  exact cof_of_left_isIso W f hf

end CategoryTheory.Waldhausen.ExtensionCategory
