/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Colib.CategoryTheory.Waldhausen.ExtensionCategory.Embeddings

/-! # Exact postcomposition of actual Reedy cofibration arrows

An exact functor maps the original relative pushout to a displayed relative
pushout. The choice-free relative criterion then proves the genuine Reedy
condition, without identifying independently chosen pushout objects.


Implementation provenance:
`Quillen/Waldhausen/ExtensionCategory/Functoriality.lean`
at Quillen commit `c561118b7795eb9780be9ed391c3251d6a4d0afd`. The original maps,
hypotheses, chosen zero objects and universe parameters are retained.
-/
@[expose] public section

noncomputable section
open CategoryTheory CategoryTheory.Limits
universe u v u' v' u'' v''
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace CategoryTheory.Waldhausen.ExtensionCategory
variable {C : Type u} [Category.{v} C] {D : Type u'} [Category.{v'} D]
  {E : Type u''} [Category.{v''} E]
variable (V : Structure C) (W : Structure D) {F : C ⥤ D}
  (hF : IsExact V.cof V.weq W.cof W.weq F)

/-- Postcomposition sends the actual cofibration arrow to its actual image. -/
def postcompose : Obj V ⥤ Obj W where
  obj X := ⟨F.mapArrow.obj X.obj, hF.cofibration _ X.property⟩
  map f := (objects W).homMk (F.mapArrow.map f.hom)
  map_id X := by
    apply ObjectProperty.hom_ext
    exact F.mapArrow.map_id X.obj
  map_comp f g := by
    apply ObjectProperty.hom_ext
    exact F.mapArrow.map_comp f.hom g.hom

@[simp] theorem postcompose_obj_hom (X : Obj V) :
    ((postcompose V W hF).obj X).obj.hom = F.map X.obj.hom := rfl
@[simp] theorem postcompose_map_left {X Y : Obj V} (f : X ⟶ Y) :
    ((postcompose V W hF).map f).hom.left = F.map f.hom.left := rfl
@[simp] theorem postcompose_map_right {X Y : Obj V} (f : X ⟶ Y) :
    ((postcompose V W hF).map f).hom.right = F.map f.hom.right := rfl

/-- Preservation of the relative condition follows from the actual mapped
relative pushout and the mapped original comparison cofibration. -/
theorem postcompose_cof {X Y : Obj V} {f : X ⟶ Y} (hf : cof V f) :
    cof W ((postcompose V W hF).map f) := by
  apply cof_of_relative W ((postcompose V W hF).map f) (hF.cofibration _ hf.1)
    (hF.pushout X.property
      (Additivity.pushoutFunctor_isPushout V (inclusion V) (inclusion_cof V) (Arrow.mk f)))
    (F.map (relativeMap V f))
  · simpa only [← F.map_comp] using! congrArg F.map
      (Additivity.sourceι_comparison V (inclusion V) (inclusion_cof V) (Arrow.mk f))
  · simpa only [← F.map_comp] using! congrArg F.map
      (Additivity.targetι_comparison V (inclusion V) (inclusion_cof V) (Arrow.mk f))
  · exact hF.cofibration _ hf.2

/-- Actual Reedy extension postcomposition is genuinely exact. -/
theorem postcompose_exact :
    IsExact (waldhausenStructure V).cof (waldhausenStructure V).weq
      (waldhausenStructure W).cof (waldhausenStructure W).weq (postcompose V W hF) where
  zero h := isZero_of_components W _ (hF.zero (source_isZero V h)) (hF.zero (middle_isZero V h))
  cofibration _ h := postcompose_cof V W hF h
  weak _ h := ⟨hF.weak _ h.1, hF.weak _ h.2⟩
  pushout hf h := IsPushout.of_map_of_faithful (forget W)
    (arrow_isPushout _ _ _ _
      (hF.pushout hf.1 (pointwise_of_isPushout V hf h).1)
      (hF.pushout (cof_middle V hf) (pointwise_of_isPushout V hf h).2))

@[simp] theorem postcompose_source : postcompose V W hF ⋙ source W = source V ⋙ F := by
  apply CategoryTheory.Functor.ext (fun _ ↦ rfl)
@[simp] theorem postcompose_middle : postcompose V W hF ⋙ middle W = middle V ⋙ F := by
  apply CategoryTheory.Functor.ext (fun _ ↦ rfl)

@[simp] theorem postcompose_id : postcompose V V (IsExact.id V.cof V.weq) = 𝟭 (Obj V) := by
  apply CategoryTheory.Functor.ext (fun _ ↦ rfl)

/-- Composition simplifies by combining the two displayed maps with their actual intermediate data.
-/
@[simp] theorem postcompose_comp_postcompose (U : Structure E) {G : D ⥤ E}
    (hG : IsExact W.cof W.weq U.cof U.weq G) :
    postcompose V W hF ⋙ postcompose W U hG =
      postcompose V U (hF.comp hG) := by
  apply CategoryTheory.Functor.ext (fun _ ↦ rfl)


end CategoryTheory.Waldhausen.ExtensionCategory
