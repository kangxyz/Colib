/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Colib.CategoryTheory.Waldhausen.ExtensionCategory.RelativeCofibrations

/-! # Genuine pointwise pushouts of cofibration arrows

Implementation provenance:
`Quillen/Waldhausen/ExtensionCategory/ArrowPushouts.lean` at Quillen commit
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
variable {C : Type u} [Category.{v} C]

/-- Displayed componentwise pushouts give the actual arrow-category pushout. -/
theorem arrow_isPushout {A B D P : Arrow C}
    (f : A ⟶ B) (g : A ⟶ D) (i : B ⟶ P) (j : D ⟶ P)
    (hl : IsPushout f.left g.left i.left j.left)
    (hr : IsPushout f.right g.right i.right j.right) : IsPushout f g i j := by
  have w : f ≫ i = g ≫ j := Arrow.hom_ext _ _ hl.w hr.w
  let l (s : PushoutCocone f g) := hl.desc s.inl.left s.inr.left
    (congrArg Arrow.Hom.left s.condition)
  let r (s : PushoutCocone f g) := hr.desc s.inl.right s.inr.right
    (congrArg Arrow.Hom.right s.condition)
  have wh (s : PushoutCocone f g) : l s ≫ s.pt.hom = P.hom ≫ r s := by
    apply hl.hom_ext
    · dsimp [l, r]
      rw [← Category.assoc, hl.inl_desc, ← Category.assoc, i.w,
        Category.assoc, hr.inl_desc]
      exact s.inl.w
    · dsimp [l, r]
      rw [← Category.assoc, hl.inr_desc, ← Category.assoc, j.w,
        Category.assoc, hr.inr_desc]
      exact s.inr.w
  let d (s : PushoutCocone f g) : P ⟶ s.pt := Arrow.homMk (l s) (r s) (wh s)
  have hi (s : PushoutCocone f g) : i ≫ d s = s.inl := by
    apply Arrow.hom_ext
    · exact hl.inl_desc _ _ _
    · exact hr.inl_desc _ _ _
  have hj (s : PushoutCocone f g) : j ≫ d s = s.inr := by
    apply Arrow.hom_ext
    · exact hl.inr_desc _ _ _
    · exact hr.inr_desc _ _ _
  apply IsPushout.of_isColimit (c := PushoutCocone.mk i j w)
  refine PushoutCocone.IsColimit.mk w d hi hj ?_
  intro s m hm hn
  apply Arrow.hom_ext
  · apply hl.hom_ext
    · exact (congrArg Arrow.Hom.left hm).trans (congrArg Arrow.Hom.left (hi s)).symm
    · exact (congrArg Arrow.Hom.left hn).trans (congrArg Arrow.Hom.left (hj s)).symm
  · apply hr.hom_ext
    · exact (congrArg Arrow.Hom.right hm).trans (congrArg Arrow.Hom.right (hi s)).symm
    · exact (congrArg Arrow.Hom.right hn).trans (congrArg Arrow.Hom.right (hj s)).symm

variable (W : Structure C)

/-- A pushout along a Reedy cofibration exists, remains an actual cofibration
arrow, and the new leg is again a Reedy cofibration. Both component squares
are genuine pushouts. -/
theorem exists_pointwise_pushout {X Y Z : Obj W} (f : X ⟶ Y) (g : X ⟶ Z) (hf : cof W f) :
    ∃ (P : Obj W) (i : Y ⟶ P) (j : Z ⟶ P), IsPushout f g i j ∧
      IsPushout f.hom.left g.hom.left i.hom.left j.hom.left ∧
      IsPushout f.hom.right g.hom.right i.hom.right j.hom.right ∧ cof W j := by
  obtain ⟨L, li, lj, hL⟩ := W.pushout_exists f.hom.left g.hom.left hf.1
  obtain ⟨M, mi, mj, hM⟩ := W.pushout_exists f.hom.right g.hom.right (cof_middle W hf)
  let p : L ⟶ M := hL.desc (Y.obj.hom ≫ mi) (Z.obj.hom ≫ mj) (by
    rw [← Category.assoc, f.hom.w, Category.assoc, hM.w,
      ← Category.assoc, ← g.hom.w, Category.assoc])
  let I : Y.obj ⟶ Arrow.mk p := Arrow.homMk li mi (hL.inl_desc _ _ _)
  let J : Z.obj ⟶ Arrow.mk p := Arrow.homMk lj mj (hL.inr_desc _ _ _)
  obtain ⟨S, si, sj, hS⟩ := W.pushout_exists Z.obj.hom lj Z.property
  let k : S ⟶ M := hS.desc mj p J.w.symm
  have hsi : si ≫ k = mj := hS.inl_desc _ _ _
  have hsj : sj ≫ k = p := hS.inr_desc _ _ _
  have hk : W.cof k := relative_cof_of_pointwise_pushout W f.hom g.hom I J hL hM
    (Additivity.pushoutFunctor_isPushout W (inclusion W) (inclusion_cof W) (Arrow.mk f)) hS
    (Additivity.sourceι_comparison W (inclusion W) (inclusion_cof W) (Arrow.mk f))
    (Additivity.targetι_comparison W (inclusion W) (inclusion_cof W) (Arrow.mk f))
    hsi hsj hf.2
  have hp : W.cof p := by
    rw [← hsj]
    exact W.cof.comp_mem _ _ (W.cof_pushout Z.property hS) hk
  let P : Obj W := ⟨Arrow.mk p, hp⟩
  let i : Y ⟶ P := (objects W).homMk I
  let j : Z ⟶ P := (objects W).homMk J
  refine ⟨P, i, j, ?_, hL, hM, ?_⟩
  · exact IsPushout.of_map_of_faithful (forget W) (arrow_isPushout f.hom g.hom I J hL hM)
  · exact cof_of_relative W j (W.cof_pushout hf.1 hL) hS k hsi hsj hk

end CategoryTheory.Waldhausen.ExtensionCategory
