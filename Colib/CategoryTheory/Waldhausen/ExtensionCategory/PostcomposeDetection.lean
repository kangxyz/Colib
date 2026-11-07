/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Colib.CategoryTheory.Waldhausen.ExtensionCategory.Functoriality

/-! # Detecting genuine relative cofibrations after exact postcomposition

The relative map is tested using its actual mapped pushout. In particular a
family which jointly detects the original cofibration class also detects the
Reedy class. Applications supply the concrete componentwise detection proof.


Implementation provenance:
`Quillen/Waldhausen/ExtensionCategory/PostcomposeDetection.lean`
at Quillen commit `c561118b7795eb9780be9ed391c3251d6a4d0afd`. The original maps,
hypotheses, chosen zero objects and universe parameters are retained.
-/
@[expose] public section

noncomputable section
open CategoryTheory CategoryTheory.Limits
universe u v u' v' w
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace CategoryTheory.Waldhausen.ExtensionCategory
variable {C : Type u} [Category.{v} C] {D : Type u'} [Category.{v'} D]
variable (V : Structure C) (W : Structure D) {F : C ⥤ D}
  (hF : IsExact V.cof V.weq W.cof W.weq F)

/-- A cofibrant image square makes the image of the original relative map
cofibrant, by the universal property of the actual mapped relative pushout. -/
theorem mapped_relative_cof {X Y : Obj V} {f : X ⟶ Y}
    (hf : cof W ((postcompose V W hF).map f)) : W.cof (F.map (relativeMap V f)) := by
  apply cof_relative W hf
    (hF.pushout X.property
      (Additivity.pushoutFunctor_isPushout V (inclusion V) (inclusion_cof V) (Arrow.mk f)))
    (F.map (relativeMap V f))
  · simpa only [← F.map_comp] using! congrArg F.map
      (Additivity.sourceι_comparison V (inclusion V) (inclusion_cof V) (Arrow.mk f))
  · simpa only [← F.map_comp] using! congrArg F.map
      (Additivity.targetι_comparison V (inclusion V) (inclusion_cof V) (Arrow.mk f))

/-- Exact postcomposition reflects the genuine Reedy class whenever the
original functor reflects the actual cofibration class. -/
theorem cof_of_postcompose
    (detect : ∀ ⦃A B : C⦄ (f : A ⟶ B), W.cof (F.map f) → V.cof f)
    {X Y : Obj V} {f : X ⟶ Y} (hf : cof W ((postcompose V W hF).map f)) : cof V f :=
  ⟨detect _ hf.1, detect _ (mapped_relative_cof V W hF hf)⟩

/-- Joint detection of original cofibrations lifts to joint detection of
Reedy cofibrations, using each functor's actual mapped relative pushout. -/
theorem cof_of_postcompose_family {ι : Sort w} (F : ι → C ⥤ D)
    (hF : ∀ i, IsExact V.cof V.weq W.cof W.weq (F i))
    (detect : ∀ ⦃A B : C⦄ (f : A ⟶ B), (∀ i, W.cof ((F i).map f)) → V.cof f)
    {X Y : Obj V} {f : X ⟶ Y}
    (hf : ∀ i, cof W ((postcompose V W (hF i)).map f)) : cof V f :=
  ⟨detect _ (fun i ↦ (hf i).1),
    detect _ (fun i ↦ mapped_relative_cof V W (hF i) (hf i))⟩

end CategoryTheory.Waldhausen.ExtensionCategory
