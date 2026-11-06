/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Colib.CategoryTheory.Waldhausen.ExtensionCategory.IsomorphicSources
public import Colib.CategoryTheory.Waldhausen.ExtensionCategory.Functoriality

/-! # Genuine Reedy cube tests with isomorphic horizontal sources

For a cube whose two horizontal source maps are isomorphisms, the actual
outer relative comparison has isomorphic source. Its target cofibration is
proved using the original target-face relative pushout, not merely from
pointwise cofibrations.


Implementation provenance:
`Quillen/Waldhausen/ExtensionCategory/IsomorphicSourceCubes.lean`
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

/-- The original target face together with the source face detects this genuine Reedy cube. -/
theorem cof_cube_of_horizontal_left_isIso
    {X Y : Obj (waldhausenStructure W)} (f : X ⟶ Y)
    [IsIso X.obj.hom.hom.left] [IsIso Y.obj.hom.hom.left]
    (hl : cof W f.hom.left)
    (hr : cof W ((postcompose (waldhausenStructure W) W (middle_exact W)).map f)) :
    cof (waldhausenStructure W) f := by
  let V := waldhausenStructure W
  let i := Additivity.sourceι V (inclusion V) (inclusion_cof V) (Arrow.mk f)
  let j := Additivity.targetι V (inclusion V) (inclusion_cof V) (Arrow.mk f)
  let k := relativeMap V f
  have hP := Additivity.pushoutFunctor_isPushout V (inclusion V) (inclusion_cof V) (Arrow.mk f)
  have hcomp_i : i ≫ k = f.hom.right :=
    Additivity.sourceι_comparison V (inclusion V) (inclusion_cof V) (Arrow.mk f)
  have hcomp_j : j ≫ k = Y.obj.hom :=
    Additivity.targetι_comparison V (inclusion V) (inclusion_cof V) (Arrow.mk f)
  obtain ⟨hPl, hPr⟩ := pointwise_of_isPushout W X.property hP
  let : IsIso j.hom.left := hPl.isIso_inr_of_isIso
  have hkleft : k.hom.left = inv j.hom.left ≫ Y.obj.hom.hom.left := by
    apply (cancel_epi j.hom.left).1
    simpa only [← Category.assoc, IsIso.hom_inv_id, Category.id_comp] using!
      congrArg (fun a ↦ a.hom.left) hcomp_j
  let : IsIso k.hom.left := by rw [hkleft]; infer_instance
  refine ⟨hl, cof_of_left_isIso W k ?_⟩
  exact cof_relative W hr hPr k.hom.right
    (congrArg (fun a ↦ a.hom.right) hcomp_i)
    (congrArg (fun a ↦ a.hom.right) hcomp_j)

end CategoryTheory.Waldhausen.ExtensionCategory
