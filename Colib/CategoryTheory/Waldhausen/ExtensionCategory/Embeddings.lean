/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Colib.CategoryTheory.Waldhausen.ExtensionCategory.Cofiber

/-! # Canonical identity-arrow and zero-arrow embeddings

Implementation provenance:
`Quillen/Waldhausen/ExtensionCategory/Embeddings.lean`
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

/-- An extension with two zero components is genuinely a zero object. -/
theorem isZero_of_components (X : Obj W) (hl : IsZero X.obj.left) (hr : IsZero X.obj.right) :
    IsZero X where
  unique_to Y := by
    refine ⟨{ default := (objects W).homMk (Arrow.homMk (hl.to_ Y.obj.left) (hr.to_ Y.obj.right)
      (hl.eq_of_src _ _)), uniq := ?_ }⟩
    intro f
    apply ObjectProperty.hom_ext
    exact Arrow.hom_ext _ _ (hl.eq_of_src _ _) (hr.eq_of_src _ _)
  unique_from Y := by
    refine ⟨{ default := (objects W).homMk (Arrow.homMk (hl.from_ Y.obj.left) (hr.from_ Y.obj.right)
      (hr.eq_of_tgt _ _)), uniq := ?_ }⟩
    intro f
    apply ObjectProperty.hom_ext
    exact Arrow.hom_ext _ _ (hl.eq_of_tgt _ _) (hr.eq_of_tgt _ _)

/-- The canonical identity extension `A → A`. -/
def identityEmbedding : C ⥤ Obj W where
  obj X := ⟨Arrow.mk (𝟙 X), W.cof.id_mem _⟩
  map f := (objects W).homMk (Arrow.homMk f f (by simp))
  map_id X := by apply ObjectProperty.hom_ext; apply Arrow.hom_ext <;> rfl
  map_comp f g := by apply ObjectProperty.hom_ext; apply Arrow.hom_ext <;> rfl

/-- The canonical zero-source extension `0 → B`. -/
def zeroEmbedding : C ⥤ Obj W where
  obj X := ⟨Arrow.mk (W.isZero.to_ X), W.cof_zero X⟩
  map f := (objects W).homMk (Arrow.homMk (𝟙 W.zero) f (W.isZero.eq_of_src _ _))
  map_id X := by apply ObjectProperty.hom_ext; apply Arrow.hom_ext <;> rfl
  map_comp f g := by apply ObjectProperty.hom_ext; apply Arrow.hom_ext <;> simp

/-- Identity-arrow embedding is genuinely exact for the Reedy structure. -/
theorem identityEmbedding_exact :
    IsExact W.cof W.weq (waldhausenStructure W).cof (waldhausenStructure W).weq
      (identityEmbedding W) where
  zero h := isZero_of_components W _ h h
  cofibration f hf := cof_of_relative W ((identityEmbedding W).map f) hf
    (IsPushout.of_id_fst (f := f)) (𝟙 _) (by simp [identityEmbedding])
    (by simp [identityEmbedding]) (W.cof.id_mem _)
  weak _ hf := ⟨hf, hf⟩
  pushout hf h := IsPushout.of_map_of_faithful (forget W)
    (arrow_isPushout _ _ _ _ h h)

/-- Zero-source embedding is genuinely exact for the Reedy structure. -/
theorem zeroEmbedding_exact :
    IsExact W.cof W.weq (waldhausenStructure W).cof (waldhausenStructure W).weq (zeroEmbedding
      W) where
  zero h := isZero_of_components W _ W.isZero h
  cofibration {X Y} f hf := cof_of_relative W ((zeroEmbedding W).map f) (W.cof.id_mem _)
    (IsPushout.of_id_snd (f := W.isZero.to_ X)) f (by simp [zeroEmbedding]) (W.isZero.eq_of_src
      _ _) hf
  weak _ hf := ⟨W.weq.id_mem _, hf⟩
  pushout hf h := IsPushout.of_map_of_faithful (forget W)
    (arrow_isPushout _ _ _ _ IsPushout.of_id_fst h)

/-- The subextension `(A→A)` inside the original extension `(A→B)`. -/
def identityToExtension : source W ⋙ identityEmbedding W ⟶ 𝟭 (Obj W) where
  app X := (objects W).homMk (Arrow.homMk (𝟙 X.obj.left) X.obj.hom (by
    simp only [identityEmbedding, source, Functor.comp_obj, Functor.id_obj,
      Arrow.leftFunc_obj, Arrow.mk_left, Arrow.mk_right, Arrow.mk_hom, Category.id_comp];
    exact Category.id_comp X.obj.hom))
  naturality X Y f := by
    apply ObjectProperty.hom_ext
    apply Arrow.hom_ext
    · simp [identityEmbedding, source, forget]
    · exact f.hom.w

/-- The actual quotient extension `(0→B/A)`. -/
def extensionToZero : 𝟭 (Obj W) ⟶ cofiber W ⋙ zeroEmbedding W where
  app X := (objects W).homMk (Arrow.homMk (W.isZero.from_ X.obj.left) ((quotient W).app X)
    (cofiber_isPushout W X).w.symm)
  naturality X Y f := by
    apply ObjectProperty.hom_ext
    apply Arrow.hom_ext
    · exact W.isZero.eq_of_tgt _ _
    · exact (quotient W).naturality f

end CategoryTheory.Waldhausen.ExtensionCategory
