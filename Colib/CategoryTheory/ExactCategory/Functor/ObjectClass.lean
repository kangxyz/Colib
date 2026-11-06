/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.CategoryTheory.ExactCategory.Functor.QIsomorphisms
public import Colib.CategoryTheory.QConstruction.ObjectClass
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Zero
public import Mathlib.CategoryTheory.Conj

/-!
# Exact functors preserve canonical Q-object classes

Adapted from `Quillen/KTheory/GrothendieckComparison/Naturality.lean` at
Quillen commit `c561118b7795eb9780be9ed391c3251d6a4d0afd`.
The original maps, specified basepoint equalities and multiplication order are retained.
-/

@[expose] public noncomputable section

universe u v
open CategoryTheory CategoryTheory.Limits
open scoped ZeroObject
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

namespace CategoryTheory.ExactCategory.ExactFunctor

variable {C D : Type u} [Category.{v} C] [Category.{v} D]
  [Preadditive C] [HasFiniteBiproducts C] [Preadditive D] [HasFiniteBiproducts D]
  {EC : ExactStructure C} {ED : ExactStructure D}

/-- The exact Q-functor preserves zero-apex arrows after the canonical
zero-object isomorphism. -/
lemma mapQ_fromZero (F : ExactFunctor EC ED) (X : C) :
    (ED.qIsoOfIso F.toFunctor.mapZeroObject).hom ≫
        ED.fromZero (QConstruction.of ED.deflation ED.inflation (F.toFunctor.obj X)) =
      F.mapQ.map (EC.fromZero (QConstruction.of EC.deflation EC.inflation X)) := by
  let e := F.toFunctor.mapZeroObject
  change QConstruction.mkHom ED.deflation ED.inflation (QConstruction.isoSpan _ _ e _) ≫
    QConstruction.mkHom ED.deflation ED.inflation _ =
      QConstruction.mkHom ED.deflation ED.inflation _
  have h : IsPullback (𝟙 (F.toFunctor.obj (0 : C))) e.hom e.hom (𝟙 (0 : D)) :=
    IsPullback.of_horiz_isIso ⟨by exact Subsingleton.elim _ _⟩
  apply ED.q_comp_of_isPullback _ _ _ _ h _ (Iso.refl _)
  · simp [QConstruction.CompatibleFunctor.mapSpan, QConstruction.isoSpan, QConstruction.of,
    CategoryTheory.ExactCategory.ExactFunctor.toQCompatibleFunctor]
    simpa using F.toFunctor.mapZeroObject.hom_inv_id
  · simp [QConstruction.CompatibleFunctor.mapSpan, QConstruction.of,
    CategoryTheory.ExactCategory.ExactFunctor.toQCompatibleFunctor]

/-- The exact Q-functor preserves whole-apex arrows with the same canonical
zero-object comparison. -/
lemma mapQ_fromZeroTotal (F : ExactFunctor EC ED) (X : C) :
    (ED.qIsoOfIso F.toFunctor.mapZeroObject).hom ≫
        ED.fromZeroTotal (QConstruction.of ED.deflation ED.inflation (F.toFunctor.obj X)) =
      F.mapQ.map (EC.fromZeroTotal (QConstruction.of EC.deflation EC.inflation X)) := by
  let e := F.toFunctor.mapZeroObject
  change QConstruction.mkHom ED.deflation ED.inflation (QConstruction.isoSpan _ _ e _) ≫
    QConstruction.mkHom ED.deflation ED.inflation _ =
      QConstruction.mkHom ED.deflation ED.inflation _
  have h : IsPullback (0 : F.toFunctor.obj X ⟶ F.toFunctor.obj (0 : C))
      (𝟙 (F.toFunctor.obj X)) e.hom (0 : F.toFunctor.obj X ⟶ 0) :=
    (IsPullback.of_horiz_isIso ⟨by simp⟩).flip
  apply ED.q_comp_of_isPullback _ _ _ _ h _ (Iso.refl _)
  · simp [QConstruction.CompatibleFunctor.mapSpan, QConstruction.isoSpan, QConstruction.of,
    CategoryTheory.ExactCategory.ExactFunctor.toQCompatibleFunctor]
  · simp [QConstruction.CompatibleFunctor.mapSpan, QConstruction.of,
    CategoryTheory.ExactCategory.ExactFunctor.toQCompatibleFunctor]

/-- Canonical object classes are natural for exact functors in every groupoid
image, after conjugation by exactly the chosen zero-object isomorphism. -/
lemma qObjectClass_mapQ {T : Type*} [Groupoid T] (F : ExactFunctor EC ED)
    (H : ED.QCategory ⥤ T) (X : C) :
    (H.mapIso (ED.qIsoOfIso F.toFunctor.mapZeroObject)).conj
        (EC.qObjectClass (F.mapQ ⋙ H) X) =
      ED.qObjectClass H (F.toFunctor.obj X) := by
  simp only [Iso.conj_apply, CategoryTheory.ExactCategory.ExactStructure.qObjectClass,
    Functor.comp_map,
    Functor.mapIso_inv, Functor.mapIso_hom]
  rw [← F.mapQ_fromZeroTotal X]
  simp only [← Groupoid.inv_eq_inv]
  rw [← F.mapQ_fromZero X]
  simp [Category.assoc, Groupoid.inv_eq_inv]

end CategoryTheory.ExactCategory.ExactFunctor
