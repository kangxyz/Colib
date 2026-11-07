/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Colib.CategoryTheory.Waldhausen.ExtensionCategory.Basic
public import Colib.CategoryTheory.Waldhausen.ExtensionCategory.PushoutCube

/-! # Choice-free tests for relative cofibrations and their pushout cubes

Implementation provenance:
`Quillen/Waldhausen/ExtensionCategory/RelativeCofibrations.lean` at Quillen commit
`c561118b7795eb9780be9ed391c3251d6a4d0afd`. The original maps, hypotheses,
chosen zero objects and universe parameters are retained.
-/
@[expose] public section

noncomputable section
open CategoryTheory CategoryTheory.Limits
universe u v
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace CategoryTheory.Waldhausen.ExtensionCategory
variable {C : Type u} [Category.{v} C] (W : Structure C)

/-- The chosen relative comparison agrees with any displayed relative pushout,
up to its unique actual pushout isomorphism. -/
theorem cof_relative {X Y : Obj W} {f : X ⟶ Y} (hf : cof W f)
    {R : C} {i : X.obj.right ⟶ R} {j : Y.obj.left ⟶ R}
    (h : IsPushout X.obj.hom f.hom.left i j)
    (k : R ⟶ Y.obj.right) (hi : i ≫ k = f.hom.right) (hj : j ≫ k = Y.obj.hom) : W.cof k := by
  let h₀ := Additivity.pushoutFunctor_isPushout W (inclusion W) (inclusion_cof W) (Arrow.mk f)
  let e := h₀.isoIsPushout _ _ h
  have he : e.hom ≫ k = relativeMap W f := by
    apply h₀.hom_ext
    · rw [← Category.assoc, h₀.inl_isoIsPushout_hom, hi]
      exact (Additivity.sourceι_comparison W (inclusion W) (inclusion_cof W) (Arrow.mk f)).symm
    · rw [← Category.assoc, h₀.inr_isoIsPushout_hom, hj]
      exact (Additivity.targetι_comparison W (inclusion W) (inclusion_cof W) (Arrow.mk f)).symm
  have hk : k = e.inv ≫ relativeMap W f := by rw [← he]; simp
  rw [hk]
  exact W.cof.comp_mem _ _ (W.cof_iso _ (inferInstance : IsIso e.inv)) hf.2

/-- A genuine displayed relative pushout suffices to prove the Reedy condition. -/
theorem cof_of_relative {X Y : Obj W} (f : X ⟶ Y) (hf : W.cof f.hom.left)
    {R : C} {i : X.obj.right ⟶ R} {j : Y.obj.left ⟶ R}
    (h : IsPushout X.obj.hom f.hom.left i j)
    (k : R ⟶ Y.obj.right) (hi : i ≫ k = f.hom.right) (hj : j ≫ k = Y.obj.hom)
    (hk : W.cof k) : cof W f := by
  refine ⟨hf, ?_⟩
  let h₀ := Additivity.pushoutFunctor_isPushout W (inclusion W) (inclusion_cof W) (Arrow.mk f)
  let e := h₀.isoIsPushout _ _ h
  have he : e.hom ≫ k = relativeMap W f := by
    apply h₀.hom_ext
    · rw [← Category.assoc, h₀.inl_isoIsPushout_hom, hi]
      exact (Additivity.sourceι_comparison W (inclusion W) (inclusion_cof W) (Arrow.mk f)).symm
    · rw [← Category.assoc, h₀.inr_isoIsPushout_hom, hj]
      exact (Additivity.targetι_comparison W (inclusion W) (inclusion_cof W) (Arrow.mk f)).symm
  rw [← he]
  exact W.cof.comp_mem _ _ (W.cof_iso _ (inferInstance : IsIso e.hom)) hk

/-- The relative target map in a pointwise pushout of arrows is a cofibration.
The new arrow is not assumed to be a cofibration: that conclusion is obtained
later by composing this map with the new relative pushout leg. -/
theorem relative_cof_of_pointwise_pushout
    {A B D P : Arrow C} (f : A ⟶ B) (g : A ⟶ D) (i : B ⟶ P) (j : D ⟶ P)
    (hleft : IsPushout f.left g.left i.left j.left)
    (hright : IsPushout f.right g.right i.right j.right)
    {R S : C} {ri : A.right ⟶ R} {rj : B.left ⟶ R} {rk : R ⟶ B.right}
    {si : D.right ⟶ S} {sj : P.left ⟶ S} {sk : S ⟶ P.right}
    (hR : IsPushout A.hom f.left ri rj) (hS : IsPushout D.hom j.left si sj)
    (hri : ri ≫ rk = f.right) (hrj : rj ≫ rk = B.hom)
    (hsi : si ≫ sk = j.right) (hsj : sj ≫ sk = P.hom)
    (hk : W.cof rk) : W.cof sk := by
  let r : R ⟶ S := hR.desc (g.right ≫ si) (i.left ≫ sj) (by
    rw [← Category.assoc, ← g.w, Category.assoc, hS.w,
      ← Category.assoc, ← hleft.w, Category.assoc])
  have hir : ri ≫ r = g.right ≫ si := hR.inl_desc _ _ _
  have hjr : rj ≫ r = i.left ≫ sj := hR.inr_desc _ _ _
  have hc : rk ≫ i.right = r ≫ sk := by
    apply hR.hom_ext
    · rw [← Category.assoc, hri, ← Category.assoc, hir, Category.assoc, hsi, hright.w]
    · rw [← Category.assoc, hrj, ← Category.assoc, hjr, Category.assoc, hsj]
      exact i.w.symm
  exact W.cof_pushout hk (relativePushoutCube hleft hright hR hS g.w.symm
    hri hsi hir hjr hc)

end CategoryTheory.Waldhausen.ExtensionCategory
